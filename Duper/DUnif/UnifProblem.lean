import Lean
open Lean

namespace Duper

initialize Lean.registerTraceClass `DUnif.debug

-- Always avoid left-rigid right-flex
structure UnifEq where
  lhs : Expr
  rhs : Expr
  lflex : Bool := false
  rflex : Bool := false
  deriving Hashable, Inhabited, BEq, Repr

def UnifEq.toMessageData : UnifEq → MessageData :=
  fun ⟨lhs, rhs, lflex, rflex⟩ => m!"\{{h lflex} lhs: {lhs}, {h rflex} rhs: {rhs}}"
    where h b := if b then "Flex" else "Rigid"

instance : ToMessageData UnifEq := ⟨UnifEq.toMessageData⟩

def UnifEq.fromExprPair (e1 e2 : Expr) : UnifEq := {lhs := e1, rhs := e2, lflex := true, rflex := true}

-- Parent Rules

inductive ParentRule where
| FromExprPairs  : Array (Expr × Expr) → ParentRule
| Succeed        : ParentRule
-- Normalize, Dereference : Does not count as rule
-- Fail : Does not produce child
| Delete         : UnifEq → ParentRule
| OracleSucc     : UnifEq → ParentRule
| OracleFail     : UnifEq → ParentRule
| Decompose      : UnifEq → ParentRule
| ForallToLambda : UnifEq → Nat → ParentRule
-- Bindings
| Iteration      : UnifEq → Expr → (argn: Nat) → (narg : Nat) → Expr → ParentRule
| JPProjection   : UnifEq → Expr → (arg : Nat) → Expr → ParentRule
| HuetProjection : UnifEq → Expr → (arg : Nat) → Expr → ParentRule
| ImitForall     : UnifEq → Expr → Expr → ParentRule
| ImitProj       : UnifEq → Expr → (idx : Nat) → Expr → ParentRule
| Imitation      : UnifEq → (flex : Expr) → (rigid : Expr) → Expr → ParentRule
| Identification : UnifEq → (e1 e2 : Expr) → Expr → Expr → ParentRule
| Elimination    : UnifEq → Expr → Array Nat → Expr → ParentRule
deriving Inhabited, BEq

def ParentRule.toMessageData : ParentRule → MessageData
| FromExprPairs arr => m!"From {arr}"
| Succeed  => "Succeed"
| Delete ue => m!"Delete {ue}"
| OracleSucc ue => m!"OracleSucc {ue}"
| OracleFail ue => m!"OracleFail {ue}"
| Decompose ue => m!"Decompose {ue}"
| ForallToLambda ue n => m!"ForallToLambda {ue} for {n} binders"
| Iteration ue F i argn b => m!"Iteration for {F} at {i} with extra {argn} args in {ue} binding {b}"
| JPProjection ue F i b => m!"JPProjection for {F} at {i} in {ue} binding {b}"
| HuetProjection ue F i b => m!"HuetProjection for {F} at {i} in {ue} binding {b}"
| ImitForall ue F b => m!"ImitForall of {F} in {ue} binding {b}"
| ImitProj ue F i b => m!"ImitProj of {F} in {ue} proj {i} binding {b}"
| Imitation ue F g b => m!"Imitation of {g} for {F} in {ue} binding {b}"
| Identification ue F G bF bG => m!"Identification of {F} and {G} in {ue} binding {bF} and {bG}"
| Elimination ue F arr b => m!"Elimination of {F} at {arr} in {ue} binding {b}"

instance : ToMessageData ParentRule := ⟨ParentRule.toMessageData⟩



structure UnifProblem where
  -- Prioritized unification equations
  --   If an equation `e`'s corresponding type unification
  --   equation was not solved when `e` was inspected, the
  --   type unification equation is prioritized
  prioritized: Array UnifEq := #[]
  -- Attention:
  --   rigidrigid, flexrigid, flexflex, postponed, checked
  -- These five fields are useless except for the equation selection function.
  -- It's theoretically possible to have only one field for
  --   storing all the equations.
  rigidrigid : Array UnifEq := #[]
  flexrigid  : Array UnifEq := #[]
  -- Equations which haven't been checked are also put
  --   into flexflex
  flexflex   : Array UnifEq := #[]
  -- When selecting equations, we prioritize `prioritized` to `rigidrigid`
  --   to `rigidflex` to `flexflex`.
  -- When `prioritized` is empty and `rigidrigid` is not empty, we will
  --   select an arbitrary equation in `rigidrigid`. However, when
  --   `rigidrigid` is empty, we can't simply pick one in `rigidflex`
  --   because some metavariables may have already been instantiated.
  --
  -- We call the following operation "check":
  --   1. If `prioritized` is not empty, instantiate and normalize the head
  --      of the last equation in `prioritized`
  --   2. Otherwise, instantiates and normalize the head of all equations in
  --      `rigidflex` and `flexflex`, then redistribute then among
  --      the three arrays.
  --
  -- When
  --   1. `prioritized` is not empty, or
  --   2. `rigidrigid`, `rigidflex` and `flexflex` are all empty
  -- we need to check again.
  --
  -- The field `check` records whether new bindings has been applied since
  -- the last check. So, to test for whether a unification problem `p`
  -- requires check, we need to use `¬ p.checked ∨ ¬ p.prioritized.empty`
  --
  -- The function `derefNormProblem` does the check
  checked    : Bool         := false
  mctx       : MetavarContext
  -- Identification variables
  identVar   : HashSet Expr := HashSet.empty
  -- Elimivarion variables
  elimVar    : HashSet Expr := HashSet.empty
  -- PersistentArray of parent rules, for debugging
  parentRules: PersistentArray ParentRule
  -- PersistentArray of parent clauses (including itself), for debugging
  parentClauses : PersistentArray Nat
  -- Tracked expressions, for debugging.
  -- These expressions will have metavariables instantiated
  --   before they're printed.
  trackedExpr: Array Expr   := #[]
  deriving Inhabited

def UnifProblem.format : UnifProblem → MessageData :=
  fun ⟨prioritized, rigidrigid, flexrigid, flexflex, checked, _, identVar, elimVar, parentrules, parentclauses, trackedExpr⟩ =>
    "Unification Problem:" ++
    m!"\n  prioritized := {prioritized},\n  rigidrigid := {rigidrigid},\n  flexrigid := {flexrigid}," ++
    m!"\n  flexflex := {flexflex},\n  checked := {checked},\n  identVar := {identVar.toList},\n  elimVar := {elimVar.toList}" ++
    m!"\n  parentclauses := {parentclauses.toList}\n  parentrules := {parentrules.toArray}\n  trackedExpr := {trackedExpr}\n"

instance : ToMessageData UnifProblem := ⟨UnifProblem.format⟩

def UnifProblem.fromExprPairs (l : Array (Expr × Expr)) : MetaM (Option UnifProblem) := do
  -- withoutModifyingMCtx
  let mctx₀ ← getMCtx
  let mut flexflex := #[]
  let mut prioritized := #[]
  for (e1, e2) in l do
    let ty1 ← Meta.inferType e1
    let sort1 ← Meta.inferType ty1
    let ty2 ← Meta.inferType e2
    let sort2 ← Meta.inferType ty2
    if ¬ (← Meta.isExprDefEq sort1 sort2) then
      return none
    else
      let unifEq := UnifEq.fromExprPair e1 e2
      flexflex := flexflex.push unifEq
      let unifTyEq := UnifEq.fromExprPair ty1 ty2
      prioritized := prioritized.push unifTyEq
  let s ← getMCtx
  setMCtx mctx₀
  return some {mctx := s, prioritized := prioritized, flexflex := flexflex, checked := false,
               parentRules := #[.FromExprPairs l].toPArray', parentClauses := .empty}

def UnifProblem.pushPrioritized (p : UnifProblem) (e : UnifEq) :=
  {p with prioritized := p.prioritized.push e}

def UnifProblem.appendPrioritized (p : UnifProblem) (es : Array UnifEq) :=
  {p with prioritized := p.prioritized.append es}

-- Here `e` hasn't been checked
def UnifProblem.pushUnchecked (p : UnifProblem) (e : UnifEq) (is_prio := false) :=
  if is_prio then
    {p with prioritized := p.prioritized.push e, checked := false}
  else
    {p with flexflex := p.flexflex.push e, checked := false}

-- Here `es` hasn't been checked
def UnifProblem.appendUnchecked (p : UnifProblem) (es : Array UnifEq) (is_prio := false) :=
  if is_prio then
    {p with prioritized := p.prioritized.append es, checked := false}
  else
    {p with flexflex := p.flexflex.append es, checked := false}

-- Here `e` has been checked
def UnifProblem.pushChecked (p : UnifProblem) (e : UnifEq) (isprio : Bool) :=
  if isprio then
    {p with prioritized := p.prioritized.push e}
  else if ¬ e.lflex ∧ ¬ e.rflex then
    {p with rigidrigid := p.rigidrigid.push e}
  else if e.lflex ∧ ¬ e.rflex then
    {p with flexrigid := p.flexrigid.push e}
  else
    {p with flexflex := p.flexflex.push e}

def UnifProblem.pushParentRule (p : UnifProblem) (pr : ParentRule) :=
  {p with parentRules := p.parentRules.push pr}

def UnifProblem.dropParentRulesButLast (p : UnifProblem) (n : Nat) :=
  let len := p.parentRules.size
  {p with parentRules := (p.parentRules.toArray.extract (len - n) len).toPArray'}

def UnifProblem.pushParentClause (p : UnifProblem) (c : Nat) :=
  {p with parentClauses := p.parentClauses.push c}

-- The selection function                         -- prioritized : Bool
def UnifProblem.pop? (p : UnifProblem) : Option (UnifEq × UnifProblem) := Id.run <| do
  if p.prioritized.size != 0 then
    let e := p.prioritized.back
    let pr' := p.prioritized.pop
    return (e, {p with prioritized := pr'})
  if p.rigidrigid.size != 0 then
    let e := p.rigidrigid.back
    let rr' := p.rigidrigid.pop
    return (e, {p with rigidrigid := rr'})
  if ¬ p.checked then
    dbg_trace s!"UnifProblem.Pop :: Equations are not normalized"
  if p.flexrigid.size != 0 then
    let e := p.flexrigid.back
    let rf' := p.flexrigid.pop
    return (e, {p with flexrigid := rf'})
  if p.flexflex.size != 0 then
    let e := p.flexflex.back
    let rf' := p.flexflex.pop
    return (e, {p with flexflex := rf'})
  return none

def UnifProblem.instantiateTrackedExpr (p : UnifProblem) : MetaM UnifProblem := do
  let trackedExpr ← p.trackedExpr.mapM instantiateMVars
  return {p with trackedExpr := trackedExpr}