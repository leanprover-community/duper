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

instance : ToString UnifEq where
  toString := fun ⟨lhs, rhs, lflex, rflex⟩ => s!"\{{h lflex} lhs: {lhs}, {h rflex} rhs: {rhs}}"
    where h b := if b then "Flex" else "Rigid"

def UnifEq.fromExprPair (e1 e2 : Expr) : UnifEq := {lhs := e1, rhs := e2, lflex := true, rflex := true}

structure UnifProblem where
  rigidrigid : Array UnifEq := #[]
  flexrigid  : Array UnifEq := #[]
  -- Equations which haven't been checked are also put
  -- into flexflex
  flexflex   : Array UnifEq := #[]
  -- When selecting UnifEq, we prioritize `rigidrigid` to `rigidflex`
  --   to `flexflex`.
  -- When `rigidrigid` is not empty, we will select an arbitrary equation
  --   in `rigidrigid`. However, when `rigidrigid` is empty, we can't simply
  --   pick one in `rigidflex` because some metavariables may have already
  --   been instantiated.
  -- We call the following operation "check":
  --   instantiates and normalizes all equations in `rigidflex` and `flexflex`
  --   redistribute then among the three arrays a "check".
  -- So, when `rigidrigid` is empty, and some metavariables
  --   have been instantiated after the last check, we need to 
  --   check again.
  checked    : Bool         := false
  state      : Meta.SavedState
  -- Identification variables
  identVar   : HashSet Expr := HashSet.empty
  -- Elimivarion variables
  elimVar    : HashSet Expr := HashSet.empty
  deriving Inhabited

def UnifProblem.empty : MetaM UnifProblem := do
  let s ← saveState
  return {state := s}

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