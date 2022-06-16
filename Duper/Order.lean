import Lean

namespace Duper
open Lean

inductive Comparison
| GreaterThan
| LessThan
| Equal
| Incomparable
deriving BEq, Inhabited

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

def VarBalance := Std.HashMap Expr Int

def VarBalance.addPosVar (vb : VarBalance) (t : Expr) : VarBalance :=
  vb.insert t $ vb.findD t 0 + 1

def VarBalance.addNegVar (vb : VarBalance) (t : Expr) : VarBalance :=
  vb.insert t $ vb.findD t 0 - 1

def headWeight (f : Expr) : Int := match f with
| Expr.const .. => 1
| Expr.mvar .. => 1
| Expr.fvar .. => 1
| Expr.bvar .. => 1
| Expr.sort .. => 1
| Expr.mdata _ e _ => headWeight e
| _ => panic! s!"head_weight: not implemented {f}"

-- The orderings treat lambda-expressions like a "LAM" symbol applied to the
-- type and body of the lambda-expression
constant LAM : Prop
constant FORALL : Prop
def getHead (t : Expr) := match t with
| Expr.lam .. => mkConst ``LAM
| Expr.forallE .. => mkConst ``FORALL
| _ => t.getAppFn

def getArgs (t : Expr) := match t with
| Expr.lam _ ty b _ => [ty, b]
| Expr.forallE _ ty b _ => [ty, b]
| _ => t.getAppArgs.toList

def weightVarHeaded : Int := 1

def VarBalance.noNegatives (vb : VarBalance) : Bool := Id.run do
  for (v, b) in vb.toArray do
    if b < 0 then
      return False
  return True

def VarBalance.noPositives (vb : VarBalance) : Bool := Id.run do
  for (v, b) in vb.toArray do
    if b > 0 then
      return False
  return True

def precCompare (f g : Expr) : Comparison := match f, g with

-- Sort > lam > db > quantifier > symbols > False > True 
| Expr.sort .., Expr.const ``LAM _ _ => GreaterThan
| Expr.sort .., Expr.bvar .. => GreaterThan
| Expr.sort .., Expr.fvar .. => GreaterThan
| Expr.sort .., Expr.const ``False _ _ => GreaterThan
| Expr.sort .., Expr.const ``True _ _ => GreaterThan

| Expr.const ``LAM _ _, Expr.sort .. => LessThan
| Expr.const ``LAM _ _, Expr.bvar .. => GreaterThan
| Expr.const ``LAM _ _, Expr.fvar .. => GreaterThan
| Expr.const ``LAM _ _, Expr.const ``False _ _ => GreaterThan
| Expr.const ``LAM _ _, Expr.const ``True _ _ => GreaterThan

| Expr.bvar .., Expr.sort .. => LessThan
| Expr.bvar .., Expr.const ``LAM _ _ => LessThan
| Expr.bvar .., Expr.fvar .. => GreaterThan
| Expr.bvar .., Expr.const ``False _ _ => GreaterThan
| Expr.bvar .., Expr.const ``True _ _ => GreaterThan

| Expr.fvar .., Expr.sort .. => LessThan
| Expr.fvar .., Expr.const ``LAM _ _ => LessThan
| Expr.fvar .., Expr.bvar .. => LessThan
| Expr.fvar .., Expr.const ``False _ _ => GreaterThan
| Expr.fvar .., Expr.const ``True _ _ => GreaterThan

| Expr.const ``False _ _, Expr.sort .. => LessThan
| Expr.const ``False _ _, Expr.const ``LAM _ _ => LessThan
| Expr.const ``False _ _, Expr.bvar .. => LessThan
| Expr.const ``False _ _, Expr.fvar .. => LessThan
| Expr.const ``False _ _, Expr.const ``True _ _ => GreaterThan

| Expr.const ``True _ _, Expr.sort .. => LessThan
| Expr.const ``True _ _, Expr.const ``LAM _ _ => LessThan
| Expr.const ``True _ _, Expr.bvar .. => LessThan
| Expr.const ``True _ _, Expr.fvar .. => LessThan
| Expr.const ``True _ _, Expr.const ``False _ _ => LessThan

| Expr.sort l .., Expr.sort m .. => if l == m then Equal else Incomparable -- TODO?
| Expr.const ``LAM _ _, Expr.const ``LAM _ _ => Equal
| Expr.bvar m .., Expr.bvar n .. => 
  if m == n then Equal
  else if m > n then GreaterThan
  else if m < n then LessThan
  else Incomparable
| Expr.fvar m .., Expr.fvar n .. => 
  if m == n then Equal
  else if m.name.hash > n.name.hash then GreaterThan
  else if m.name.hash < n.name.hash then LessThan
  else Incomparable
| Expr.const ``False _ _, Expr.const ``False _ _ => Equal
| Expr.const ``True _ _, Expr.const ``True _ _ => Equal


| Expr.const ``LAM _ _, Expr.const .. => GreaterThan
| Expr.bvar .., Expr.const .. => GreaterThan
| Expr.fvar .., Expr.const .. => GreaterThan
| Expr.const ``True _ _, Expr.const .. => LessThan
| Expr.const ``False _ _, Expr.const .. => LessThan

| Expr.const .., Expr.const ``LAM _ _ => LessThan
| Expr.const .., Expr.bvar .. => LessThan
| Expr.const .., Expr.fvar .. => LessThan
| Expr.const .., Expr.const ``False _ _ => GreaterThan
| Expr.const .., Expr.const ``True _ _ => GreaterThan

| Expr.const m .., Expr.const n .. =>
  if m == n then Equal
  else if m.hash > n.hash then GreaterThan
  else if m.hash < n.hash then LessThan
  else Incomparable

| Expr.mvar v _, Expr.mvar w _ => 
  if v == w then Equal else Incomparable
| _, Expr.mvar _ _ => Incomparable
| Expr.mvar _ _, _ => Incomparable
| _, _ => panic! s!"precCompare: not implemented {f} <> {g}"

-- Inspired by Zipperposition
partial def kbo (t1 t2 : Expr) : MetaM Comparison := do
  let (_, _, res) ← tckbo 0 Std.HashMap.empty t1 t2
  return res
where
--     -- (** Update variable balance, weight balance, and check whether the term contains the fluid term s.
--     --     @param pos stands for positive (is t the left term?)
--     --     @return weight balance, was `s` found?
--     -- *)
  balance_weight (wb : Int) (vb : VarBalance) (t : Expr) (s : Option Expr) (pos : Bool) : MetaM (Int × VarBalance × Bool) := do
    if t.isMVar then
      return ← balance_weight_var wb vb t s pos
    else
      match getHead t, getArgs t with
      | h@(Expr.mvar v _), args =>
        let (wb, vb, res) := ← balance_weight_var wb vb h s pos
        balance_weight_rec wb vb args s pos res
      | h, args =>
        let wb :=
          if pos
          then wb + headWeight h
          else wb - headWeight h
        balance_weight_rec wb vb args s pos false
  -- (** balance_weight for the case where t is an applied variable *)
  balance_weight_var (wb : Int) (vb : VarBalance) (t : Expr) (s : Option Expr) (pos : Bool) : MetaM (Int × VarBalance × Bool) := do
    if pos then
      let vb := vb.addPosVar t
      let wb := wb + weightVarHeaded
      return (wb, vb, s == some t)
    else
      let vb := vb.addNegVar t
      let wb := wb - weightVarHeaded
      return (wb, vb, s == some t)
--     (** list version of the previous one, threaded with the check result *)
  balance_weight_rec (wb : Int) (vb : VarBalance) (terms : List Expr) (s : Option Expr) (pos : Bool) (res : Bool) : MetaM _ := 
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
      match getHead t1, getHead t2 with
      | Expr.mvar _ _, Expr.mvar _ _ =>
        let vb := vb.addPosVar t1;
        let vb := vb.addNegVar t2;
        return (wb, vb, Incomparable)
      | Expr.mvar _ _,  _ =>
        let vb := vb.addPosVar t1;
        let (wb, vb, contains) ← balance_weight wb vb t2 (some t1) (pos := false)
        return ((wb + weightVarHeaded), vb, if contains then LessThan else Incomparable)
      |  _, Expr.mvar _ _ =>
        let vb := vb.addNegVar t2;
        let (wb, vb, contains) ← balance_weight wb vb t1 (some t2) (pos := true)
        return ((wb - weightVarHeaded), vb, if contains then GreaterThan else Incomparable)
      | h1, h2 => 
        return ← tckbo_composite wb vb h1 h2 (getArgs t1) (getArgs t2)
--     (** tckbo, for non-variable-headed terms). *)
  tckbo_composite wb vb f g ss ts : MetaM (Int × VarBalance × Comparison) := do
--       (* do the recursive computation of kbo *)
    let (wb, vb, res) := ← tckbo_rec wb vb f g ss ts
    let wb := wb + headWeight f - headWeight g
    --(* check variable condition *)
    let g_or_n := if vb.noNegatives then GreaterThan else Incomparable
    let l_or_n := if vb.noPositives then LessThan else Incomparable
    --(* lexicographic product of weight and precedence *)
    if wb > 0 then return (wb, vb, g_or_n)
    else if wb < 0 then return (wb, vb, l_or_n)
    else 
      match precCompare f g with
      | GreaterThan => return (wb, vb, g_or_n)
      | LessThan => return (wb, vb, l_or_n)
      | Equal =>
        if res == Equal then return (wb, vb, Equal)
        else if res == LessThan then return (wb, vb, l_or_n)
        else if res == GreaterThan then return (wb, vb, g_or_n)
        else return (wb, vb, Incomparable)
      | _ => return (wb, vb, Incomparable)
--     (* recursive comparison *)
  tckbo_rec wb vb f g ss ts : MetaM (Int × VarBalance × Comparison) := do
    if precCompare f g == Comparison.Equal
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
  let s := mkApp2 (mkConst ``Nat.sub) x x
  let t := mkApp2 (mkConst ``Nat.add) x y
  let res ← kbo s t
  trace[Meta.debug] "s: {s}"
  trace[Meta.debug] "t: {t}"
  trace[Meta.debug] "res: {res}"

set_option trace.Meta.debug true
#eval test

end Order

end Duper
