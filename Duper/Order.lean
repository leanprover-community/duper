import Lean
import Duper.Util.Misc
import Duper.Util.Reduction
import Duper.Expr

set_option linter.unusedVariables false

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

abbrev SymbolPrecMap := Std.HashMap Symbol Nat -- Maps symbols to their precedence. Lower numbers indicate higher precedence

namespace Comparison

def flip : Comparison → Comparison
| GreaterThan => LessThan
| LessThan => GreaterThan
| Incomparable => Incomparable
| Equal => Equal

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

def Weight := Int × Int
deriving Inhabited, DecidableEq

instance : Add Weight := ⟨fun (a₁, b₁) (a₂, b₂) => (a₁ + a₂, b₁ + b₂)⟩
instance : Sub Weight := ⟨fun (a₁, b₁) (a₂, b₂) => (a₁ - a₂, b₁ - b₂)⟩
instance : OfNat Weight n := ⟨(0, n)⟩
instance : LT Weight := ⟨fun (a₁, b₁) (a₂, b₂) => a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)⟩
instance (v w : Weight) : Decidable (v < w) :=
  if h : v.1 < w.1 ∨ (v.1 = w.1 ∧ v.2 < w.2) then .isTrue h else .isFalse fun g => h g

def absWeight (w : Weight) : Weight := (Int.natAbs w.1, Int.natAbs w.2)

local notation "ω" => ((1,0) : Weight)

def VarBalance := Std.HashMap (Expr × Bool) Weight

def VarBalance.addPosVar (vb : VarBalance) (t : Expr × Bool) : VarBalance :=
  vb.insert t $ vb.getD t 0 + 1

def VarBalance.addNegVar (vb : VarBalance) (t : Expr × Bool) : VarBalance :=
  vb.insert t $ vb.getD t 0 - 1

-- The orderings treat lambda-expressions like a "LAM" symbol applied to the
-- type and body of the lambda-expression
opaque LAM : Prop
opaque FORALL : Prop
opaque EXISTS : Prop
def getHead (t : Expr) := match t with
| Expr.lam .. => mkConst ``LAM
| Expr.forallE .. => mkConst ``FORALL
| Expr.app (Expr.app (Expr.const ``Exists _) _) _  => mkConst ``EXISTS
| Expr.mdata _ t => getHead t
| _ => t.getAppFn'

def getArgs (t : Expr) := match t with
| Expr.lam _ ty b _ => [ty, b]
| Expr.forallE _ ty b _ => [ty, b]
| Expr.app (Expr.app (Expr.const ``Exists _) ty) b  =>
  match b with
  | .lam _ _ b _ => [ty, b]
  | _ => [ty, .app (b.liftLooseBVars 0 1) (.bvar 0)]
| Expr.mdata _ t => getArgs t
| _ => t.getAppArgs.toList

/-- Computes headWeight according to firstmaximal0 weight generation scheme. The head
    is given weight 1 unless if the head is the unique symbol with the highest precedence in
    symbolPrecMap, in which case, it is given weight 0.

    Note: In order to make the firstmaximal0 weight generation scheme compliant with KBO, if
    the highest precedence symbol has arity 0 (i.e. is a first-order 'constant'), then I cannot
    assign the highest precedence symbol weight 0 (because this would violate KBO's constraint
    that all first-order 'constants' share some positive weight μ). In this case, I simply assign
    the highest precedence symbol weight 1, as with everything else. -/
def headWeight (f : Expr) (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) (belowLam : Bool) : Weight := match f with
  | Expr.const name _ =>
    if name == ``FORALL || name == ``EXISTS then
      if belowLam then 1 else ω
    else
      let fSymbol := Symbol.Const name
      match symbolPrecMap.get? fSymbol with
      | some 0 => -- The symbol with the highest precedence in symbolPrecMap is mapped to 0 (unless it has arity zero)
        if highesetPrecSymbolHasArityZero then 1
        else 0
      | _ => 1
  | Expr.fvar fVarId =>
    let fSymbol := Symbol.FVarId fVarId
    match symbolPrecMap.get? fSymbol with
    | some 0 => -- The symbol with the highest precedence in symbolPrecMap is mapped to 0 (unless it has arity zero)
      if highesetPrecSymbolHasArityZero then 1
      else 0
    | _ => 1
  | Expr.mvar .. => 1
  | Expr.bvar .. => 1
  | Expr.sort .. => 1
  | Expr.lit .. => 1
  | Expr.proj .. => 1 -- Treating projections like fvar symbols (except we don't allow projections to have the highest precedence)
  | Expr.mdata .. => panic! s!"head_weight: mdata is not a valid head symbol {f}"
  | Expr.forallE .. => panic! s!"head_weight: forall is not a valid head symbol {f}"
  | Expr.lam .. => panic! s!"head_weight: lambda is not a valid head symbol {f}"
  | Expr.app .. => panic! s!"head_weight: app is not a valid head symbol {f}"
  | Expr.letE .. => panic! s!"head_weight: let expressions must be eliminated to compute order {f}"

def weightVarHeaded : Weight := 1

def VarBalance.noNegatives (vb : VarBalance) : Bool := Id.run do
  for (_, b) in vb.toArray do
    if b < 0 then
      return False
  return True

def VarBalance.noPositives (vb : VarBalance) : Bool := Id.run do
  for (_, b) in vb.toArray do
    if b > 0 then
      return False
  return True

/-- A last resort comparison function to use if symbolPrecCompare needs to compare two symbols, neither
    of which appeared in symbolPrecMap. We use the convention: Anonymous < Num < Str -/
def nameCompare (n1 : Name) (n2 : Name) : Comparison :=
  match n1, n2 with
  | Name.anonymous, Name.anonymous => Equal
  | Name.num pre1 n1, Name.num pre2 n2 =>
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
  match symbolPrecMap.get? s1, symbolPrecMap.get? s2 with
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

-- TODO: quantifiers: ex/forall
-- Sort > lam > bvar > quantifier > symbols (projections are treated as symbols smaller than consts and fvars) > lits > False > True
| Expr.sort .., Expr.const ``LAM _ => return GreaterThan
| Expr.sort .., Expr.bvar .. => return GreaterThan
| Expr.sort .., Expr.const ``FORALL _ => return GreaterThan
| Expr.sort .., Expr.const ``EXISTS _ => return GreaterThan
| Expr.sort .., Expr.fvar .. => return GreaterThan
| Expr.sort .., Expr.lit .. => return GreaterThan
| Expr.sort .., Expr.const ``False _ => return GreaterThan
| Expr.sort .., Expr.const ``True _ => return GreaterThan

| Expr.const ``LAM _, Expr.sort .. => return LessThan
| Expr.const ``LAM _, Expr.bvar .. => return GreaterThan
| Expr.const ``LAM _, Expr.const ``FORALL _ => return GreaterThan
| Expr.const ``LAM _, Expr.const ``EXISTS _ => return GreaterThan
| Expr.const ``LAM _, Expr.fvar .. => return GreaterThan
| Expr.const ``LAM _, Expr.lit .. => return GreaterThan
| Expr.const ``LAM _, Expr.const ``False _ => return GreaterThan
| Expr.const ``LAM _, Expr.const ``True _ => return GreaterThan

| Expr.bvar .., Expr.sort .. => return LessThan
| Expr.bvar .., Expr.const ``LAM _ => return LessThan
| Expr.bvar .., Expr.const ``FORALL _ => return GreaterThan
| Expr.bvar .., Expr.const ``EXISTS _ => return GreaterThan
| Expr.bvar .., Expr.fvar .. => return GreaterThan
| Expr.bvar .., Expr.lit .. => return GreaterThan
| Expr.bvar .., Expr.const ``False _ => return GreaterThan
| Expr.bvar .., Expr.const ``True _ => return GreaterThan

| Expr.const ``FORALL _, Expr.sort .. => return LessThan
| Expr.const ``FORALL _, Expr.const ``LAM _ => return LessThan
| Expr.const ``FORALL _, Expr.bvar .. => return LessThan
| Expr.const ``FORALL _, Expr.const ``EXISTS _ => return GreaterThan
| Expr.const ``FORALL _, Expr.fvar .. => return GreaterThan
| Expr.const ``FORALL _, Expr.lit .. => return GreaterThan
| Expr.const ``FORALL _, Expr.const ``False _ => return GreaterThan
| Expr.const ``FORALL _, Expr.const ``True _ => return GreaterThan

| Expr.const ``EXISTS _, Expr.sort .. => return LessThan
| Expr.const ``EXISTS _, Expr.const ``LAM _ => return LessThan
| Expr.const ``EXISTS _, Expr.bvar .. => return LessThan
| Expr.const ``EXISTS _, Expr.const ``FORALL _ => return LessThan
| Expr.const ``EXISTS _, Expr.fvar .. => return GreaterThan
| Expr.const ``EXISTS _, Expr.lit .. => return GreaterThan
| Expr.const ``EXISTS _, Expr.const ``False _ => return GreaterThan
| Expr.const ``EXISTS _, Expr.const ``True _ => return GreaterThan

| Expr.fvar .., Expr.sort .. => return LessThan
| Expr.fvar .., Expr.const ``LAM _ => return LessThan
| Expr.fvar .., Expr.bvar .. => return LessThan
| Expr.fvar .., Expr.const ``FORALL _ => return LessThan
| Expr.fvar .., Expr.const ``EXISTS _ => return LessThan
| Expr.fvar .., Expr.lit .. => return GreaterThan
| Expr.fvar .., Expr.const ``False _ => return GreaterThan
| Expr.fvar .., Expr.const ``True _ => return GreaterThan

| Expr.lit .., Expr.sort .. => return LessThan
| Expr.lit .., Expr.const ``LAM _ => return LessThan
| Expr.lit .., Expr.bvar .. => return LessThan
| Expr.lit .., Expr.const ``FORALL _ => return LessThan
| Expr.lit .., Expr.const ``EXISTS _ => return LessThan
| Expr.lit .., Expr.fvar .. => return LessThan
| Expr.lit .., Expr.const ``False _ => return GreaterThan
| Expr.lit .., Expr.const ``True _ => return GreaterThan

| Expr.const ``False _, Expr.sort .. => return LessThan
| Expr.const ``False _, Expr.const ``LAM _ => return LessThan
| Expr.const ``False _, Expr.bvar .. => return LessThan
| Expr.const ``False _, Expr.const ``FORALL _ => return LessThan
| Expr.const ``False _, Expr.const ``EXISTS _ => return LessThan
| Expr.const ``False _, Expr.fvar .. => return LessThan
| Expr.const ``False _, Expr.lit .. => return LessThan
| Expr.const ``False _, Expr.const ``True _ => return GreaterThan

| Expr.const ``True _, Expr.sort .. => return LessThan
| Expr.const ``True _, Expr.const ``LAM _ => return LessThan
| Expr.const ``True _, Expr.bvar .. => return LessThan
| Expr.const ``True _, Expr.const ``FORALL _ => return LessThan
| Expr.const ``True _, Expr.const ``EXISTS _ => return LessThan
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
| Expr.const ``FORALL _, Expr.const ``FORALL _ => return Equal
| Expr.const ``EXISTS _, Expr.const ``EXISTS _ => return Equal
| Expr.fvar m .., Expr.fvar n .. => symbolPrecCompare f g (Symbol.FVarId m) (Symbol.FVarId n) symbolPrecMap
| Expr.const ``False _, Expr.const ``False _ => return Equal
| Expr.const ``True _, Expr.const ``True _ => return Equal

| Expr.sort .., Expr.const .. => return GreaterThan
| Expr.const ``LAM _, Expr.const .. => return GreaterThan
| Expr.bvar .., Expr.const .. => return GreaterThan
| Expr.const ``FORALL _, Expr.const .. => return GreaterThan
| Expr.const ``EXISTS _, Expr.const .. => return GreaterThan
| Expr.fvar m .., Expr.const n .. => symbolPrecCompare f g (Symbol.FVarId m) (Symbol.Const n) symbolPrecMap
| Expr.lit .., Expr.const .. => return LessThan
| Expr.const ``False _, Expr.const .. => return LessThan
| Expr.const ``True _, Expr.const .. => return LessThan

| Expr.const .., Expr.sort .. => return LessThan
| Expr.const .., Expr.const ``LAM _ => return LessThan
| Expr.const .., Expr.bvar .. => return LessThan
| Expr.const .., Expr.const ``FORALL _ => return LessThan
| Expr.const .., Expr.const ``EXISTS _ => return LessThan
| Expr.const m .., Expr.fvar n .. => symbolPrecCompare f g (Symbol.Const m) (Symbol.FVarId n) symbolPrecMap
| Expr.const .., Expr.lit _ => return GreaterThan
| Expr.const .., Expr.const ``False _ => return GreaterThan
| Expr.const .., Expr.const ``True _ => return GreaterThan

| Expr.const m .., Expr.const n .. => symbolPrecCompare f g (Symbol.Const m) (Symbol.Const n) symbolPrecMap

| Expr.proj .., Expr.sort .. => return LessThan
| Expr.proj .., Expr.const ``LAM _ => return LessThan
| Expr.proj .., Expr.bvar .. => return LessThan
| Expr.proj .., Expr.const ``FORALL _ => return LessThan
| Expr.proj .., Expr.const ``EXISTS _ => return LessThan
| Expr.proj .., Expr.fvar n .. => return LessThan
| Expr.proj .., Expr.lit _ => return GreaterThan
| Expr.proj .., Expr.const ``False _ => return GreaterThan
| Expr.proj .., Expr.const ``True _ => return GreaterThan
| Expr.proj .., Expr.const .. => return LessThan -- Projections considered less than any const except False and True

| Expr.sort .., Expr.proj .. => return GreaterThan
| Expr.const ``LAM _, Expr.proj .. => return GreaterThan
| Expr.bvar .., Expr.proj .. => return GreaterThan
| Expr.const ``FORALL _, Expr.proj .. => return GreaterThan
| Expr.const ``EXISTS _, Expr.proj .. => return GreaterThan
| Expr.fvar n .., Expr.proj .. => return GreaterThan
| Expr.lit _, Expr.proj .. => return LessThan
| Expr.const ``False _, Expr.proj .. => return LessThan
| Expr.const ``True _, Expr.proj .. => return LessThan
| Expr.const .., Expr.proj .. => return GreaterThan -- Projections considered less than any const except False and True

| Expr.proj _ idx1 struct1, Expr.proj _ idx2 struct2 => -- We use the projection idx to determine precedence
  if idx1 < idx2 then return LessThan
  else if idx1 > idx2 then return GreaterThan
  else if struct1 == struct2 then return Equal -- Head symbols are the same projection of the same struct
  else return Incomparable -- We cannot attempt to use struct1 and struct2 as a tiebreaker because it may be an expression that we don't permit as
                           -- a head symbol. I could try making precCompare mutually recursive with kbo and then call kbo to compare struct1 and struct2,
                           -- but I expect this edge case will come up infrequently enough that it's fine to just declare the projections incomparable
                           -- if their structs don't match

| Expr.lit l1, Expr.lit l2 =>
  if l1 < l2 then return LessThan
  else if l2 < l1 then return GreaterThan
  else return Equal

| Expr.mvar v, Expr.mvar w =>
  if v == w then return Equal else return Incomparable
| _, Expr.mvar _ => return Incomparable
| Expr.mvar _, _ => return Incomparable
| Expr.mdata .., _ => panic! s!"precCompare: mdata expression is not a valid head symbol {toString f} <> {toString g}"
| _, Expr.mdata .. => panic! s!"precCompare: mdata expression is not a valid head symbol {toString f} <> {toString g}"
| Expr.forallE .., _ => panic! s!"precCompare: forall expression is not a valid head symbol {toString f} <> {toString g}"
| _, Expr.forallE .. => panic! s!"precCompare: forall expression is not a valid head symbol {toString f} <> {toString g}"
| Expr.lam .., _ => panic! s!"precCompare: lambda expression is not a valid head symbol {toString f} <> {toString g}"
| _, Expr.lam .. => panic! s!"precCompare: lambda expression is not a valid head symbol {toString f} <> {toString g}"
| Expr.app .., _ => panic! s!"precCompare: applications are not a valid head symbol {toString f} <> {toString g}"
| _, Expr.app .. => panic! s!"precCompare: applications are not a valid head symbol {toString f} <> {toString g}"
| Expr.letE .., _ => panic! s!"precCompare: let expressions need to be eliminated before computing order {toString f} <> {toString g}"
| _, Expr.letE .. => panic! s!"precCompare: let expressions need to be eliminated before computing order {toString f} <> {toString g}"

/-- Overapproximation of being fluid -/
def isFluid (t : Expr) :=
  let t := t.consumeMData
  (t.isApp && t.getAppFn'.isMVar') || (t.isLambda && t.hasMVar)

mutual

  /-- Higher-Order KBO, inspired by `https://github.com/sneeuwballen/zipperposition/blob/master/src/core/Ordering.ml`.

      Follows Section 3.9 of `https://matryoshka-project.github.io/pubs/hosup_article.pdf`
      and the article "Things to Know when Implementing KBO" by Bernd Löchner. -/
  partial def kbo (t1 t2 : Expr) (alreadyReduced : Bool) (symbolPrecMap : SymbolPrecMap)
    (highesetPrecSymbolHasArityZero : Bool) : MetaM Comparison := do
    if alreadyReduced then
      let (_, _, res) ← tckbo 0 Std.HashMap.emptyWithCapacity t1 t2 (belowLam := false) symbolPrecMap highesetPrecSymbolHasArityZero
      trace[duper.unaryFirst.debug] "Result of comparing {t1} with {t2} (alreadyReduced: {alreadyReduced}) is {res}"
      return res
    else
      let t1 ← betaEtaReduceInstMVars t1
      let t2 ← betaEtaReduceInstMVars t2
      let (_, _, res) ← tckbo 0 Std.HashMap.emptyWithCapacity t1 t2 (belowLam := false) symbolPrecMap highesetPrecSymbolHasArityZero
      trace[duper.unaryFirst.debug] "Result of comparing {t1} with {t2} (alreadyReduced: {alreadyReduced}) is {res}"
      return res

  /-- Update variable balance, weight balance, and check whether the term contains the fluid term s.
      The argument `pos` determines whether weights and variables will be counted positively or negatively,
      i.e., whether `t` is the left term in the comparison. Returns the weight balance and whether `s` was found. -/
  partial def balance_weight (wb : Weight) (vb : VarBalance) (t : Expr) (s : Option Expr) (pos : Bool) (belowLam : Bool)
    (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Bool) := do
    if t.isMVar' || isFluid t then
      return ← balance_weight_var wb vb t s pos belowLam symbolPrecMap highesetPrecSymbolHasArityZero
    else
      match getHead t, getArgs t with
      | h@(Expr.mvar _), args =>
        let (wb, vb, res) := ← balance_weight_var wb vb h s pos belowLam symbolPrecMap highesetPrecSymbolHasArityZero
        balance_weight_rec wb vb args s pos belowLam res symbolPrecMap highesetPrecSymbolHasArityZero
      | h, args =>
        let wb :=
          if pos
          then wb + headWeight h symbolPrecMap highesetPrecSymbolHasArityZero belowLam
          else wb - headWeight h symbolPrecMap highesetPrecSymbolHasArityZero belowLam
        balance_weight_rec wb vb args s pos (belowLam := h.isConstOf ``LAM) false symbolPrecMap highesetPrecSymbolHasArityZero

  /-- balance_weight for the case where t is an applied variable -/
  partial def balance_weight_var (wb : Weight) (vb : VarBalance) (t : Expr) (s : Option Expr) (pos : Bool)
    (belowLam : Bool) (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Bool) := do
    if pos then
      let vb := vb.addPosVar (t, belowLam)
      let wb := wb + weightVarHeaded
      return (wb, vb, s == some t)
    else
      let vb := vb.addNegVar (t, belowLam)
      let wb := wb - weightVarHeaded
      return (wb, vb, s == some t)

  /-- list version of the previous one, threaded with the check result -/
  partial def balance_weight_rec (wb : Weight) (vb : VarBalance) (terms : List Expr) (s : Option Expr) (pos : Bool) (belowLam : Bool)
    (res : Bool) (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Bool) :=
    match terms with
    | [] => pure (wb, vb, res)
    | t::terms' => do
      let (wb, vb, res') := ← balance_weight wb vb t s pos belowLam symbolPrecMap highesetPrecSymbolHasArityZero
      return ← balance_weight_rec wb vb terms' s pos belowLam (res || res') symbolPrecMap highesetPrecSymbolHasArityZero

  /-- lexicographic comparison -/
  partial def tckbolex (wb : Weight) (vb : VarBalance) (terms1 terms2 : List Expr) (belowLam : Bool) (symbolPrecMap : SymbolPrecMap)
    (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Comparison) := do
    match terms1, terms2 with
    | [], [] => return (wb, vb, Comparison.Equal)
    | t1::terms1', t2::terms2' =>
      match ← tckbo wb vb t1 t2 belowLam symbolPrecMap highesetPrecSymbolHasArityZero with
        | (wb, vb, Comparison.Equal) => tckbolex wb vb terms1' terms2' belowLam symbolPrecMap highesetPrecSymbolHasArityZero
        | (wb, vb, res) => -- (* just compute the weights and return result *)
          let (wb, vb, _) := ← balance_weight_rec wb vb terms1' none (pos := true) belowLam false symbolPrecMap highesetPrecSymbolHasArityZero
          let (wb, vb, _) := ← balance_weight_rec wb vb terms2' none (pos := false) belowLam false symbolPrecMap highesetPrecSymbolHasArityZero
          return (wb, vb, res)
    | [], _ =>
      let (wb, vb, _) := ← balance_weight_rec wb vb terms2 none (pos := false) belowLam false symbolPrecMap highesetPrecSymbolHasArityZero
      return (wb, vb, Comparison.LessThan)
    | _, [] =>
      let (wb, vb, _) := ← balance_weight_rec wb vb terms1 none (pos := true) belowLam false symbolPrecMap highesetPrecSymbolHasArityZero
      return (wb, vb, Comparison.GreaterThan)

  /-- length-lexicographic comparison -/
  partial def tckbolenlex (wb : Weight) (vb : VarBalance) (terms1 terms2 : List Expr) (belowLam : Bool) (symbolPrecMap : SymbolPrecMap)
    (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Comparison) := do
    if terms1.length == terms2.length
    then return ← tckbolex wb vb terms1 terms2 belowLam symbolPrecMap highesetPrecSymbolHasArityZero
    else
      /- just compute the weights and return result -/
      let (wb, vb, _) := ← balance_weight_rec wb vb terms1 none (pos := true) belowLam false symbolPrecMap highesetPrecSymbolHasArityZero
      let (wb, vb, _) := ← balance_weight_rec wb vb terms2 none (pos := false) belowLam false symbolPrecMap highesetPrecSymbolHasArityZero
      let res :=
        if List.length terms1 > List.length terms2
        then Comparison.GreaterThan
        else Comparison.LessThan
      return (wb, vb, res)

  /-- tupled version of kbo (kbo_5 of the paper) -/
  partial def tckbo (wb : Weight) (vb : VarBalance) (t1 t2 : Expr) (belowLam : Bool) (symbolPrecMap : SymbolPrecMap)
    (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Comparison) := do
    if t1 == t2
    then return (wb, vb, Equal) -- do not update weight or var balance
    else
      match getHead t1, getHead t2 with
      | Expr.mvar _, Expr.mvar _ =>
        let vb := vb.addPosVar (t1, belowLam);
        let vb := vb.addNegVar (t2, belowLam);
        return (wb, vb, Incomparable)
      | Expr.mvar _,  _ =>
        let vb := vb.addPosVar (t1, belowLam);
        let (wb, vb, contains) ← balance_weight wb vb t2 (some t1) (pos := false) belowLam symbolPrecMap highesetPrecSymbolHasArityZero
        return ((wb + weightVarHeaded), vb, if contains then LessThan else Incomparable)
      |  _, Expr.mvar _ =>
        let vb := vb.addNegVar (t2, belowLam);
        let (wb, vb, contains) ← balance_weight wb vb t1 (some t2) (pos := true) belowLam symbolPrecMap highesetPrecSymbolHasArityZero
        return ((wb - weightVarHeaded), vb, if contains then GreaterThan else Incomparable)
      | h1, h2 =>
        return ← tckbo_composite wb vb h1 h2 (getArgs t1) (getArgs t2) belowLam symbolPrecMap highesetPrecSymbolHasArityZero

  /-- tckbo, for non-variable-headed terms). -/
  partial def tckbo_composite (wb : Weight) (vb : VarBalance) (f g : Expr) (ss ts : List Expr) (belowLam : Bool)
    (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Comparison) := do
    /- do the recursive computation of kbo -/
    let (wb, vb, res) := ← tckbo_rec wb vb f g ss ts belowLam symbolPrecMap highesetPrecSymbolHasArityZero
    let wb := wb + headWeight f symbolPrecMap highesetPrecSymbolHasArityZero belowLam - headWeight g symbolPrecMap highesetPrecSymbolHasArityZero belowLam
    /- check variable condition -/
    let g_or_n := if vb.noNegatives then GreaterThan else Incomparable
    let l_or_n := if vb.noPositives then LessThan else Incomparable
    /- lexicographic product of weight and precedence -/
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

  /-- recursive comparison -/
  partial def tckbo_rec (wb : Weight) (vb : VarBalance) (f g : Expr) (ss ts : List Expr) (belowLam : Bool)
    (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM (Weight × VarBalance × Comparison) := do
    let ssBelowLam := belowLam || f.isConstOf ``LAM
    let tsBelowLam := belowLam || g.isConstOf ``LAM
    if (← precCompare f g symbolPrecMap) == Comparison.Equal
    then return ← tckbolenlex wb vb ss ts (belowLam := ssBelowLam) symbolPrecMap highesetPrecSymbolHasArityZero
    else
      /- just compute variable and weight balances -/
      let (wb, vb, _) := ← balance_weight_rec wb vb ss none (pos := true) false (belowLam := ssBelowLam) symbolPrecMap highesetPrecSymbolHasArityZero
      let (wb, vb, _) := ← balance_weight_rec wb vb ts none (pos := false) false (belowLam := tsBelowLam) symbolPrecMap highesetPrecSymbolHasArityZero
      return (wb, vb, Comparison.Incomparable)

end

/-- getLitNetWeight takes two expressions `t1` and `t2` and calculates `weight(t1) - weight(t2)`, returning the difference of
    the two expressions' weights. -/
def getNetWeight (t1 t2 : Expr) (alreadyReduced : Bool) (symbolPrecMap : SymbolPrecMap) (highesetPrecSymbolHasArityZero : Bool) : MetaM Weight := do
  if alreadyReduced then
    let (netWeight, _, _) ← tckbo 0 Std.HashMap.emptyWithCapacity t1 t2 (belowLam := false) symbolPrecMap highesetPrecSymbolHasArityZero
    return netWeight
  else
    let t1 ← betaEtaReduceInstMVars t1
    let t2 ← betaEtaReduceInstMVars t2
    let (netWeight, _, _) ← tckbo 0 Std.HashMap.emptyWithCapacity t1 t2 (belowLam := false) symbolPrecMap highesetPrecSymbolHasArityZero
    return netWeight

end Order

end Duper
