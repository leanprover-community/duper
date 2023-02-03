import Lean
open Lean

namespace Duper

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

structure UnifProblem where
  -- Attention:
  --   rigidrigid, flexrigid, flexflex, postponed, checked
  -- These five fields are useless except for the equation selection function.
  -- It's theoretically possible to have only one field for
  --   storing all the equations.
  rigidrigid : Array UnifEq := #[]
  flexrigid  : Array UnifEq := #[]
  -- Equations which haven't been checked are also put
  -- into flexflex
  flexflex   : Array UnifEq := #[]
  -- Postponed unification equations
  -- If some of an equation `e`'s corresponding type unification
  --   equation was not solved when `e` was inspected, the equation
  --   `e` is postponed.
  postponed  : Array UnifEq := #[]
  -- When selecting equations, we prioritize `rigidrigid` to `rigidflex`
  --   to `flexflex` to `postponed`.
  -- When `rigidrigid` is not empty, we will select an arbitrary equation
  --   in `rigidrigid`. However, when `rigidrigid` is empty, we can't simply
  --   pick one in `rigidflex` because some metavariables may have already
  --   been instantiated.
  --
  -- We call the following operation "check":
  --   1. If `rigidrigid`, `rigidflex` and `flexflex` are all empty, put all equations
  --   in `postponed` to `flexflex`. Otherwise do nothing.
  --   2. Instantiates and normalize the head of all equations in
  --      `rigidflex` and `flexflex`, then redistribute then among
  --      the three arrays.
  --
  -- When
  --   1. `rigidrigid` is empty, and some metavariables
  --      have been instantiated after the last check, or
  --   2. `rigidrigid`, `rigidflex` and `flexflex` are all empty
  -- we need to check again.
  --
  -- The field `check` records whether the equations in `flexflex`
  -- requres normalizing. So, to test for whether a unification problem `p`
  -- requires check, we need to use `¬ p.checked ∨ p.isActiveEmpty`
  --
  -- The function `derefNormProblem` does the check
  -- The function `isActiveEmpty` inspects whether `rigidrigid`, `rigidflex`
  --   and `flexflex` are all empty.
  checked    : Bool         := false
  mctx       : MetavarContext
  -- Identification variables
  identVar   : HashSet Expr := HashSet.empty
  -- Elimivarion variables
  elimVar    : HashSet Expr := HashSet.empty
  deriving Inhabited

def UnifProblem.format : UnifProblem → MessageData :=
  fun ⟨rigidrigid, flexrigid, flexflex, postponed, checked, _, identVar, elimVar⟩ =>
    "Unification Problem:" ++
    m!"\n  rigidrigid := {rigidrigid},\n  flexrigid := {flexrigid},\n  flexflex := {flexflex},\n  " ++
    m!"postponed := {postponed},\n  checked := {checked},\n  identVar := {identVar.toList},\n  elimVar := {elimVar.toList}" ++
    "\n"

instance : ToMessageData UnifProblem := ⟨UnifProblem.format⟩

def UnifProblem.empty : MetaM UnifProblem := do
  let s ← getMCtx
  return {mctx := s}

-- Empty, except that `postponed` might not be empty
def UnifProblem.isActiveEmpty (up : UnifProblem) : Bool := up.rigidrigid.isEmpty ∧ up.flexrigid.isEmpty ∧ up.flexflex.isEmpty

-- Here `e` hasn't been checked
def UnifProblem.pushUnchecked (p : UnifProblem) (e : UnifEq) := {p with flexflex := p.flexflex.push e, checked := false}

-- Here `es` hasn't been checked
def UnifProblem.appendUnchecked (p : UnifProblem) (es : Array UnifEq) := {p with flexflex := p.flexflex.append es, checked := false}

-- Here `e` has been checked
def UnifProblem.pushChecked (p : UnifProblem) (e : UnifEq) :=
  if ¬ e.lflex ∧ ¬ e.rflex then
    {p with rigidrigid := p.rigidrigid.push e}
  else if e.lflex ∧ ¬ e.rflex then
    {p with flexrigid := p.flexrigid.push e}
  else
    {p with flexflex := p.flexflex.push e}

-- Here `es` has been checked
def UnifProblem.appendChecked (p : UnifProblem) (es : Array UnifEq) := Id.run <| do
  let mut ret := p
  for e in es do
    ret := ret.pushChecked e

-- The selection function
def UnifProblem.pop? (p : UnifProblem) : Option (UnifEq × UnifProblem) := Id.run <| do
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