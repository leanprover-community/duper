import Lean
import Duper.DUnif.Utils
import Duper.DUnif.UnifProblem
import Duper.Util.OccursCheck

open Lean

namespace DUnif

initialize
  registerTraceClass `DUnif.oracles

register_option oracleInstOn : Bool := {
  defValue := true
  descr := "Whether to use instantiation oracle, which attempts to " ++
           "instantiate a side of the equation if it's a metavariable"
}

def getOracleInstOn : CoreM Bool := do
  let opts ← getOptions
  return oracleInstOn.get opts

def oracleInst (p : UnifProblem) (eq : UnifEq) : MetaM (Option UnifProblem) := do
  setMCtx p.mctx
  let mut mvarId : MVarId := Inhabited.default
  if ¬ (← getOracleInstOn) then
    return none
  let mut eq := eq
  if let .some id ← metaEta eq.rhs then
    eq := eq.swapSide
    mvarId := id
  else
    if let .some id ← metaEta eq.lhs.eta then
      mvarId := id
    else
      return none
  -- We do not use Lean's occurs check here, because the occurs check
  --   does not consider metavariables in the type of metavariables
  if (← mustNotOccursCheck mvarId eq.rhs) then
    mvarId.assign eq.rhs
    /- It's not sufficient to just assigned mvarId to eq.rhs in all cases. If mvarId's type is more specific
       than eq.rhs's type (e.g. if mvarId's type is `Fin 3` and eq.rhs's type is `Fin ?m`), then it is necessary
       to additionally unify the types of mvarId and eq.rhs. -/
    let mvarIdType ← Meta.inferType (.mvar mvarId)
    let rhsType ← Meta.inferType eq.rhs
    if mvarIdType != rhsType then
      -- This code is loosely adapted from DUnif.imitation
      trace[DUnif.oracles] "oracleInst: {mvarIdType} needs to be unified with {rhsType}"
      trace[DUnif.oracles] "Before forallTelescope:"
      trace[DUnif.oracles] "rhs: {eq.rhs} (type: {rhsType})"
      trace[DUnif.oracles] "mvar: {mvarId} (type: {mvarIdType})"
      Meta.forallTelescopeReducing mvarIdType fun xs β => do
        let β ← Meta.mkLambdaFVars xs β
        let (ys, _, _) ← Meta.forallMetaTelescopeReducing rhsType
        let β' ← Meta.instantiateForall rhsType ys
        let β' ← Meta.mkLambdaFVars xs β'
        trace[DUnif.oracles] "After forallTelescope:"
        trace[DUnif.oracles] "oracleInst: rhsType (β'): {β'}"
        trace[DUnif.oracles] "oracleInst: mvarIdType (β): {β}"
        let p := p.pushPrioritized (UnifEq.fromExprPair β β')
        return some {(← p.pushParentRuleIfDbgOn (.OracleInst eq)) with checked := false, mctx := ← getMCtx}
    else
      return some {(← p.pushParentRuleIfDbgOn (.OracleInst eq)) with checked := false, mctx := ← getMCtx}
  else
    return none

register_option oracleOccursOn : Bool := {
  defValue := true
  descr := "Whether to use the occurs check oracle, which is the generalization" ++
           " of first-order occurs check to dependent type theory. It only checks metavariables" ++
           " which will always be in the term even after β-reduction and further metavariable instantiations."
}

def getOracleOccursOn : CoreM Bool := do
  let opts ← getOptions
  return oracleOccursOn.get opts

-- true  : fail
-- false : not fail
def oracleOccurs (p : UnifProblem) (eq : UnifEq) : MetaM Bool := do
  setMCtx p.mctx
  if ¬ (← getOracleOccursOn) then
    return false
  if let .mvar id := eq.rhs.eta then
    mustOccursCheck id eq.lhs
  else
    if let .mvar id := eq.lhs.eta then
      mustOccursCheck id eq.rhs
    else
      return false
