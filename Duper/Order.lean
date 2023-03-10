import Lean
import Duper.Util.Misc

namespace Duper
open Lean

inductive Comparison
| GreaterThan
| LessThan
| Equal
| Incomparable
deriving BEq, Inhabited

inductive Symbol
| FVarId : FVarId → Symbol
| Const : Name → Symbol
deriving BEq, Inhabited, Hashable

def Symbol.format : Symbol → MessageData
  | FVarId fVarId => m!"FVarId {fVarId.name}"
  | Const name => m!"Const {name}"

def Symbol.toString : Symbol → String
  | FVarId fVarId => s!"FVarId {fVarId.name}"
  | Const name => s!"Const {name}"

instance : ToMessageData Symbol := ⟨Symbol.format⟩
instance : ToString Symbol := ⟨Symbol.toString⟩

abbrev SymbolPrecMap := HashMap Symbol Nat -- Maps symbols to their precedence. Lower numbers indicate higher precedence

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

def VarBalance := HashMap Expr Int

def VarBalance.addPosVar (vb : VarBalance) (t : Expr) : VarBalance :=
  vb.insert t $ vb.findD t 0 + 1

def VarBalance.addNegVar (vb : VarBalance) (t : Expr) : VarBalance :=
  vb.insert t $ vb.findD t 0 - 1

/-- Computes headWeight according to firstmaximal0 weight generation scheme. The head
    is given weight 1 unless if the head is the unique symbol with the highest precedence in
    symbolPrecMap, in which case, it is given weight 0.

    Note: In order to make the firstmaximal0 weight generation scheme compliant with KBO, if
    the highest precedence symbol has arity 0 (i.e. is a first-order 'constant'), then I cannot
    assign the highest precedence symbol weight 0 (because this would violate KBO's constraint
    that all first-order 'constants' share some positive weight μ). In this case, I simply assign
    the highest precedence symbol weight 1, as with everything else. -/
def headWeight (f : Expr) (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : Int := match f with
  | Expr.const name _ =>
    let fSymbol := Symbol.Const name
    match symbolPrecMap.find? fSymbol with
    | some 0 => -- The symbol with the highest precedence in symbolPrecMap is mapped to 0 (unless it has arity zero)
      if highesetPrecSymbolHasArityZero then 1
      else 0
    | _ => 1
  | Expr.fvar fVarId =>
    let fSymbol := Symbol.FVarId fVarId
    match symbolPrecMap.find? fSymbol with
    | some 0 => -- The symbol with the highest precedence in symbolPrecMap is mapped to 0 (unless it has arity zero)
      if highesetPrecSymbolHasArityZero then 1
      else 0
    | _ => 1
  | Expr.mvar .. => 1
  | Expr.bvar .. => 1
  | Expr.sort .. => 1
  | Expr.lit .. => 1
  | Expr.mdata _ e => headWeight e symbolPrecMap highesetPrecSymbolHasArityZero
  | _ => panic! s!"head_weight: not implemented {f}"

-- The orderings treat lambda-expressions like a "LAM" symbol applied to the
-- type and body of the lambda-expression
opaque LAM : Prop
opaque FORALL : Prop
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

/-- A last resort comparison function to use if symbolPrecCompare needs to compare two symbols, neither
    of which appeared in symbolPrecMap. We use the convention: Anonymous < Num < Str -/
def nameCompare (n1 : Name) (n2 : Name) : Comparison :=
  match n1, n2 with
  | Name.anonymous, Name.anonymous => Equal
  | Name.num pre1 n1, Name.num pre2 n2 =>
    -- For completeness, it is important that newer skolems have higher precedence than older skolems. Fortunately,
    -- newer skolems also have larger numbers at the end, so simply comparing the numbers at the end works.
    if n1 < n2 then LessThan
    else if n1 > n2 then GreaterThan
    else nameCompare pre1 pre2
  | Name.str pre1 s1, Name.str pre2 s2 =>
    if s1 < s2 then LessThan
    else if s1 > s2 then GreaterThan
    else nameCompare pre1 pre2
  | Name.anonymous, Name.num _ _ => LessThan
  | Name.anonymous, Name.str _ _ => LessThan
  | Name.num _ _, Name.anonymous => GreaterThan
  | Name.num _ _, Name.str _ _ => LessThan
  | Name.str _ _, Name.anonymous => GreaterThan
  | Name.str _ _, Name.num _ _ => GreaterThan

/-- A comparison function for comparing fvars and consts based on precomputed precedences. Note that lower numbers in symbolPrecMap
    correspond to higher precedences. e1 is the expression that produces symbol s1 and e2 is the expression that produces symbol s2
    (e1 and e2 need to be included in addition to s1 and s2 in case if we need to determine the arity of e1 or e2) -/
def symbolPrecCompare (e1 : Expr) (e2 : Expr) (s1 : Symbol) (s2 : Symbol) (symbolPrecMap : SymbolPrecMap) : MetaM Comparison :=
  /-
    Note: We don't need hardcode checks to see if e1 or e2 is True/False because precCompare already checks for that

    However, we do need to hardcode that the highest precedence symbol in symbolPrecMap has the highest precedence symbol overall
    so that the firstmaximal0 weight generation scheme can determine if a symbol is maximal simply by checking whether it maps
    to 0 in symbolPrecMap
  -/
  match symbolPrecMap.find? s1, symbolPrecMap.find? s2 with
  | some n1, some n2 =>
    if n1 > n2 then return LessThan -- n1 is larger than n2 so s1 has a lower precedence
    else if n1 < n2 then return GreaterThan -- n1 is smaller than n2 so s1 has a higher precedence
    else return Equal
  | some n, none => do
    if n == 0 then return GreaterThan -- Hardcode that the highest precedence symbol in symbolPrecMap has the highest precedence overall
    -- Unary symbols > Large arity symbols > Small arity symbols (unary_first precedence rule)
    -- If arity is shared, symbols in symbolPrecMap have greater precedence than symbols not in symbolPrecMap
    let s1Type ← inferType e1
    let s2Type ← inferType e2
    let s1Arity := getArity s1Type
    let s2Arity := getArity s2Type
    if s1Arity == 1 && s2Arity != 1 then return GreaterThan
    else if s1Arity != 1 && s2Arity == 1 then return LessThan
    else if s1Arity > s2Arity then return GreaterThan
    else if s2Arity > s1Arity then return LessThan
    else return GreaterThan -- Arity is the same, tiebreak by preferring s1 which is in symbolPrecMap
  | none, some n => do
    if n == 0 then return LessThan -- Hardcode that the highest precedence symbol in symbolPrecMap has the highest precedence overall
    -- Unary symbols > Large arity symbols > Small arity symbols (unary_first precedence rule)
    -- If arity is shared, symbols in symbolPrecMap have greater precedence than symbols not in symbolPrecMap
    let s1Type ← inferType e1
    let s2Type ← inferType e2
    let s1Arity := getArity s1Type
    let s2Arity := getArity s2Type
    if s1Arity == 1 && s2Arity != 1 then return GreaterThan
    else if s1Arity != 1 && s2Arity == 1 then return LessThan
    else if s1Arity > s2Arity then return GreaterThan
    else if s2Arity > s1Arity then return LessThan
    else return LessThan -- Arity is the same, tiebreak by preferring s2 which is in symbolPrecMap
  | none, none =>
    let s1Name :=
      match s1 with
      | Symbol.Const n => n
      | Symbol.FVarId f => f.name
    let s2Name :=
      match s2 with
      | Symbol.Const n => n
      | Symbol.FVarId f => f.name
    return nameCompare s1Name s2Name

def precCompare (f g : Expr) (symbolPrecMap : SymbolPrecMap) : MetaM Comparison := match f, g with

-- Sort > lam > db > quantifier > symbols > lits > False > True
| Expr.sort .., Expr.const ``LAM _ => return GreaterThan
| Expr.sort .., Expr.bvar .. => return GreaterThan
| Expr.sort .., Expr.fvar .. => return GreaterThan
| Expr.sort .., Expr.lit .. => return GreaterThan
| Expr.sort .., Expr.const ``False _ => return GreaterThan
| Expr.sort .., Expr.const ``True _ => return GreaterThan

| Expr.const ``LAM _, Expr.sort .. => return LessThan
| Expr.const ``LAM _, Expr.bvar .. => return GreaterThan
| Expr.const ``LAM _, Expr.fvar .. => return GreaterThan
| Expr.const ``LAM _, Expr.lit .. => return GreaterThan
| Expr.const ``LAM _, Expr.const ``False _ => return GreaterThan
| Expr.const ``LAM _, Expr.const ``True _ => return GreaterThan

| Expr.bvar .., Expr.sort .. => return LessThan
| Expr.bvar .., Expr.const ``LAM _ => return LessThan
| Expr.bvar .., Expr.fvar .. => return GreaterThan
| Expr.bvar .., Expr.lit .. => return GreaterThan
| Expr.bvar .., Expr.const ``False _ => return GreaterThan
| Expr.bvar .., Expr.const ``True _ => return GreaterThan

| Expr.fvar .., Expr.sort .. => return LessThan
| Expr.fvar .., Expr.const ``LAM _ => return LessThan
| Expr.fvar .., Expr.bvar .. => return LessThan
| Expr.fvar .., Expr.lit .. => return GreaterThan
| Expr.fvar .., Expr.const ``False _ => return GreaterThan
| Expr.fvar .., Expr.const ``True _ => return GreaterThan

| Expr.lit .., Expr.sort .. => return LessThan
| Expr.lit .., Expr.bvar .. => return LessThan
| Expr.lit .., Expr.const ``False _ => return GreaterThan
| Expr.lit .., Expr.const ``True _ => return GreaterThan
| Expr.lit .., Expr.const .. => return LessThan
| Expr.lit .., Expr.fvar .. => return LessThan

| Expr.const ``False _, Expr.sort .. => return LessThan
| Expr.const ``False _, Expr.const ``LAM _ => return LessThan
| Expr.const ``False _, Expr.bvar .. => return LessThan
| Expr.const ``False _, Expr.fvar .. => return LessThan
| Expr.const ``False _, Expr.lit .. => return LessThan
| Expr.const ``False _, Expr.const ``True _ => return GreaterThan

| Expr.const ``True _, Expr.sort .. => return LessThan
| Expr.const ``True _, Expr.const ``LAM _ => return LessThan
| Expr.const ``True _, Expr.bvar .. => return LessThan
| Expr.const ``True _, Expr.fvar .. => return LessThan
| Expr.const ``True _, Expr.lit .. => return LessThan
| Expr.const ``True _, Expr.const ``False _ => return LessThan

| Expr.sort l .., Expr.sort m .. => if l == m then return Equal else return Incomparable -- TODO?
| Expr.const ``LAM _, Expr.const ``LAM _ => return Equal
| Expr.bvar m .., Expr.bvar n .. => 
  if m == n then return Equal
  else if m > n then return GreaterThan
  else if m < n then return LessThan
  else return Incomparable
| Expr.fvar m .., Expr.fvar n .. => symbolPrecCompare f g (Symbol.FVarId m) (Symbol.FVarId n) symbolPrecMap
| Expr.const ``False _, Expr.const ``False _ => return Equal
| Expr.const ``True _, Expr.const ``True _ => return Equal

| Expr.sort .., Expr.const .. => return GreaterThan
| Expr.const ``LAM _, Expr.const .. => return GreaterThan
| Expr.bvar .., Expr.const .. => return GreaterThan
| Expr.fvar m .., Expr.const n .. => symbolPrecCompare f g (Symbol.FVarId m) (Symbol.Const n) symbolPrecMap
| Expr.const ``True _, Expr.const .. => return LessThan
| Expr.const ``False _, Expr.const .. => return LessThan

| Expr.const .., Expr.sort .. => return LessThan
| Expr.const .., Expr.const ``LAM _ => return LessThan
| Expr.const .., Expr.bvar .. => return LessThan
| Expr.const m .., Expr.fvar n .. => symbolPrecCompare f g (Symbol.Const m) (Symbol.FVarId n) symbolPrecMap
| Expr.const .., Expr.const ``False _ => return GreaterThan
| Expr.const .., Expr.const ``True _ => return GreaterThan

| Expr.const m .., Expr.const n .. => symbolPrecCompare f g (Symbol.Const m) (Symbol.Const n) symbolPrecMap

| Expr.lit l1, Expr.lit l2 =>
  if l1 < l2 then return LessThan
  else if l2 < l1 then return GreaterThan
  else return Equal

| Expr.mvar v, Expr.mvar w => 
  if v == w then return Equal else return Incomparable
| _, Expr.mvar _ => return Incomparable
| Expr.mvar _, _ => return Incomparable
| _, _ => panic! s!"precCompare: not implemented {toString f} <> {toString g}"

-- Inspired by Zipperposition
partial def kbo (t1 t2 : Expr) (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM Comparison := do
  let (_, _, res) ← tckbo 0 HashMap.empty t1 t2
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
      | h@(Expr.mvar v), args =>
        let (wb, vb, res) := ← balance_weight_var wb vb h s pos
        balance_weight_rec wb vb args s pos res
      | h, args =>
        let wb :=
          if pos
          then wb + headWeight h symbolPrecMap highesetPrecSymbolHasArityZero
          else wb - headWeight h symbolPrecMap highesetPrecSymbolHasArityZero
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
      | Expr.mvar _, Expr.mvar _ =>
        let vb := vb.addPosVar t1;
        let vb := vb.addNegVar t2;
        return (wb, vb, Incomparable)
      | Expr.mvar _,  _ =>
        let vb := vb.addPosVar t1;
        let (wb, vb, contains) ← balance_weight wb vb t2 (some t1) (pos := false)
        return ((wb + weightVarHeaded), vb, if contains then LessThan else Incomparable)
      |  _, Expr.mvar _ =>
        let vb := vb.addNegVar t2;
        let (wb, vb, contains) ← balance_weight wb vb t1 (some t2) (pos := true)
        return ((wb - weightVarHeaded), vb, if contains then GreaterThan else Incomparable)
      | h1, h2 => 
        return ← tckbo_composite wb vb h1 h2 (getArgs t1) (getArgs t2)
--     (** tckbo, for non-variable-headed terms). *)
  tckbo_composite wb vb f g ss ts : MetaM (Int × VarBalance × Comparison) := do
--       (* do the recursive computation of kbo *)
    let (wb, vb, res) := ← tckbo_rec wb vb f g ss ts
    let wb := wb + headWeight f symbolPrecMap highesetPrecSymbolHasArityZero - headWeight g symbolPrecMap highesetPrecSymbolHasArityZero
    --(* check variable condition *)
    let g_or_n := if vb.noNegatives then GreaterThan else Incomparable
    let l_or_n := if vb.noPositives then LessThan else Incomparable
    --(* lexicographic product of weight and precedence *)
    if wb > 0 then return (wb, vb, g_or_n)
    else if wb < 0 then return (wb, vb, l_or_n)
    else 
      match ← precCompare f g symbolPrecMap with
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
    if (← precCompare f g symbolPrecMap) == Comparison.Equal
    then return ← tckbolenlex wb vb ss ts
    else
      --(* just compute variable and weight balances *)
      let (wb, vb, _) := ← balance_weight_rec wb vb ss none (pos := true) false
      let (wb, vb, _) := ← balance_weight_rec wb vb ts none (pos := false) false
      return (wb, vb, Comparison.Incomparable)

end Order

end Duper
