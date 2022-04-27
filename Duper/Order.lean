import Lean

namespace Duper
open Lean

inductive Comparison
| GreaterThan
| LessThan
| Equal
| Incomparable
deriving BEq

namespace Comparison

instance : ToMessageData Comparison := ⟨
  fun c => match c with
| GreaterThan => ">"
| LessThan => "<"
| Equal => "="
| Incomparable => "?"
⟩ 

end Comparison

namespace Order
open Lean.Meta
open Comparison

partial def weight (s : Expr) (w : Int := 0) (sign : Int) : MetaM Int := do
  Core.checkMaxHeartbeats "weight"
  trace[Meta.debug] "s: {s}" 
  s.withApp fun f ss =>
    match f with
    | Expr.fvar .. => do
      let mut w := w + sign * 1
      for u in ss do
        w ← weight u w sign
      return w
    | Expr.const .. => do
      let mut w := w + sign * 1
      for u in ss do
        w ← weight u w sign
      return w
    | Expr.forallE _ _ body _ => do -- TODO: Also search type? 
      let mut w := w + sign * 1
      w ← weight body w sign
      -- TODO: Assert ss empty?
      return w
    | Expr.bvar .. => do
      let mut w := w + sign * 1
      for u in ss do
        w ← weight u w sign
      return w
    | Expr.sort .. => do
      return w + sign * 1
    | Expr.mvar mVarId .. => do
      return w + sign * 1
    | _ => throwError "Not implemented {s}"

def VarBalance := Std.HashMap Expr Int

partial def varBalance (s : Expr) (vb : Std.HashMap Expr Int := {}) (sign : Int) : MetaM (Std.HashMap Expr Int) := do
  Core.checkMaxHeartbeats "varBalance"
  trace[Meta.debug] "s: {s}" 
  s.withApp fun f ss =>
    match f with
    | Expr.fvar .. => do
      let mut vb := vb
      for u in ss do
        vb ← varBalance u vb sign
      return vb
    | Expr.const .. => do
      let mut vb := vb
      for u in ss do
        vb ← varBalance u vb sign
      return vb
    | Expr.forallE _ _ body _ => do -- TODO: Also search type?
      let vb ← varBalance body vb sign
      -- TODO: Assert ss empty?
      return vb
    | Expr.bvar .. => do
      let mut vb := vb
      for u in ss do
        vb ← varBalance u vb sign
      return vb
    | Expr.sort .. => do
      return vb
    | Expr.mvar mVarId .. => do
      let vb := vb.insert s $ vb.findD s 0 + sign
      return vb
    | _ => throwError "Not implemented {s}"

def compareVarBalance (vb : Std.HashMap Expr Int := {}) : MetaM Comparison := do
  let mut res := Equal
  for (v, b) in vb.toArray do
    if b > 0 then
      if res == LessThan then
        res := Incomparable
        break
      else
        res := GreaterThan
    else if b < 0 then
      if res == GreaterThan then
        res := Incomparable
        break
      else
        res := LessThan
  return res

-- TODO: Not quite KBO yet
def kbo (s t : Expr) : MetaM Comparison := do
  Core.checkMaxHeartbeats "kbo"
  if s == t then return Equal
  else
    let wb : Int := 0
    let wb ← weight s wb 1
    let wb ← weight t wb (-1)
    let vb := {}
    let vb ← varBalance s vb 1
    let vb ← varBalance t vb (-1)
    trace[Meta.debug] "wb: {wb}"
    trace[Meta.debug] "vb: {vb.toArray}"
    let vbComparison ← compareVarBalance vb
    return if wb > 0 ∧ (vbComparison == GreaterThan ∨ vbComparison == Equal) then
      GreaterThan
    else if wb < 0 ∧ (vbComparison == LessThan ∨ vbComparison == Equal) then
      LessThan
    else
      Incomparable

inductive Head
| V (v : Expr) : Head
| C (c : Expr) : Head
def Head.term_to_head (t : Expr) : Head := sorry
def Head.term_to_args (t : Expr) : List Expr := sorry
def add_pos_var (vb : VarBalance) (t : Expr) : VarBalance := sorry
def add_neg_var (vb : VarBalance) (t : Expr) : VarBalance := sorry
def Head.weight (f : Head) : Int := sorry
def weight_var_headed : Int := 1
def no_negatives (vb : VarBalance) : Bool := sorry
def no_positives (vb : VarBalance) : Bool := sorry
def prec_compare (f g : Head) : Comparison := sorry

partial def kbo' (t1 t2 : Expr) : MetaM Comparison := do
  let (_, _, res) ← tckbo 0 Std.HashMap.empty t1 t2
  return res
where
--     -- (** Update variable balance, weight balance, and check whether the term contains the fluid term s.
--     --     @param pos stands for positive (is t the left term?)
--     --     @return weight balance, was `s` found?
--     -- *)
  balance_weight (wb : Int) vb t s pos : MetaM (Int × VarBalance × Bool) := do
    if t.isMVar then
      return ← balance_weight_var wb vb t s pos
    else
      match Head.term_to_head t, Head.term_to_args t with
      | Head.V v, args =>
        let (wb, vb, res) := ← balance_weight_var wb vb v s pos
        balance_weight_rec wb vb args s pos res
      | h, args =>
        let wb :=
          if pos
          then wb + Head.weight h
          else wb - Head.weight h
        balance_weight_rec wb vb args s pos false
  -- (** balance_weight for the case where t is an applied variable *)
  balance_weight_var wb vb t s pos : MetaM (Int × VarBalance × Bool) := do
    if pos then
      let vb := add_pos_var vb t
      let wb := wb + weight_var_headed
      return (wb, vb, s == some t)
    else
      let vb := add_neg_var vb t
      let wb := wb - weight_var_headed
      return (wb, vb, s == some t)
--     (** list version of the previous one, threaded with the check result *)
  balance_weight_rec wb vb terms (s : Option Expr) pos res : MetaM _ := 
    match terms with
    | [] => pure (wb, vb, res)
    | t::terms' => do
      let (wb, vb, res') := ← balance_weight wb vb t s pos
      return ← balance_weight_rec wb vb terms' s pos (res || res')
--     (** lexicographic comparison *)
  tckbolex wb vb terms1 terms2 : MetaM _ := do
    match terms1, terms2 with
    | [], [] => return (wb, vb, Comparison.Equal)
    | t1::terms1', t2::terms2' =>
      match ← tckbo wb vb t1 t2 with
        | (wb, vb, Comparison.Equal) => tckbolex wb vb terms1' terms2'
        | (wb, vb, res) => -- (* just compute the weights and return result *)
          let (wb, vb, _) := ← balance_weight_rec wb vb terms1' none (pos := true) false
          let (wb, vb, _) := ← balance_weight_rec wb vb terms2' none (pos := false) false
          return (wb, vb, res)
    | [], _ =>
      let (wb, vb, _) := ← balance_weight_rec wb vb terms2 none (pos := false) false
      return (wb, vb, Comparison.LessThan)
    | _, [] =>
      let (wb, vb, _) := ← balance_weight_rec wb vb terms1 none (pos := true) false
      return (wb, vb, Comparison.GreaterThan)
--     (* length-lexicographic comparison *)
  tckbolenlex wb vb terms1 terms2 : MetaM _ := do
    if terms1.length == terms2.length
    then return ← tckbolex wb vb terms1 terms2
    else (
      --(* just compute the weights and return result *)
      let (wb, vb, _) := ← balance_weight_rec wb vb terms1 none (pos := true) false
      let (wb, vb, _) := ← balance_weight_rec wb vb terms2 none (pos := false) false
      let res :=
        if List.length terms1 > List.length terms2
        then Comparison.GreaterThan 
        else Comparison.LessThan
      return (wb, vb, res)
    )
--     (* tupled version of kbo (kbo_5 of the paper) *)
  tckbo (wb : Int) (vb : VarBalance) (t1 t2 : Expr) : MetaM (Int × VarBalance × Comparison) := do
    if t1 == t2
    then return (wb, vb, Equal) -- do not update weight or var balance
    else
      match Head.term_to_head t1, Head.term_to_head t2 with
      | Head.V _, Head.V _ =>
        let vb := add_pos_var vb t1;
        let vb := add_neg_var vb t2;
        return (wb, vb, Incomparable)
      | Head.V _,  _ =>
        let vb := add_pos_var vb t1;
        let (wb, vb, contains) ← balance_weight wb vb t2 (some t1) (pos := false)
        return ((wb + weight_var_headed), vb, if contains then LessThan else Incomparable)
      |  _, Head.V _ =>
        let vb := add_neg_var vb t2;
        let (wb, vb, contains) ← balance_weight wb vb t1 (some t2) (pos := true)
        return ((wb - weight_var_headed), vb, if contains then GreaterThan else Incomparable)
      | h1, h2 => 
        return ← tckbo_composite wb vb h1 h2 (Head.term_to_args t1) (Head.term_to_args t2)
--     (** tckbo, for non-variable-headed terms). *)
  tckbo_composite wb vb f g ss ts : MetaM (Int × VarBalance × Comparison) := do
--       (* do the recursive computation of kbo *)
    let (wb', vb', res) := ← tckbo_rec wb vb f g ss ts
    let wb'' := wb' + Head.weight f - Head.weight g
    --(* check variable condition *)
    let g_or_n := if no_negatives vb then GreaterThan else Incomparable
    let l_or_n := if no_positives vb then LessThan else Incomparable
    --(* lexicographic product of weight and precedence *)
    if wb'' > 0 then return (wb'', vb', g_or_n)
    else if wb'' < 0 then return (wb'', vb', l_or_n)
    else 
      match prec_compare f g with
      | GreaterThan => return (wb'', vb', g_or_n)
      | LessThan => return (wb'', vb', l_or_n)
      | Equal =>
        if res == Equal then return (wb'', vb', Equal)
        else if res == LessThan then return (wb'', vb', l_or_n)
        else if res == GreaterThan then return (wb'', vb', g_or_n)
        else return (wb'', vb', Incomparable)
      | _ => return (wb'', vb', Incomparable)
--     (* recursive comparison *)
  tckbo_rec wb vb f g ss ts : MetaM (Int × VarBalance × Comparison) := do
    if prec_compare f g == Comparison.Equal
    then return ← tckbolenlex wb vb ss ts
    else
      --(* just compute variable and weight balances *)
      let (wb, vb, _) := ← balance_weight_rec wb vb ss none (pos := true) false
      let (wb, vb, _) := ← balance_weight_rec wb vb ts none (pos := false) false
      return (wb, vb, Comparison.Incomparable)


def test : MetaM Unit := do
  let ty := mkConst ``Nat
  let x ← mkFreshExprMVar ty
  let y ← mkFreshExprMVar ty
  let s := (mkConst ``Nat.zero)
  let t := mkApp (mkConst ``Nat.succ) x
  let res ← kbo s t
  trace[Meta.debug] "s: {s}"
  trace[Meta.debug] "t: {t}"
  trace[Meta.debug] "res: {res}"

set_option trace.Meta.debug true
#eval test

end Order

end Duper
