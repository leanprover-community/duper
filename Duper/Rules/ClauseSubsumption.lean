import Duper.Simp
import Duper.Util.ClauseSubsumptionCheck

namespace Duper

open Lean
open RuleM
open Meta
open SimpResult

initialize Lean.registerTraceClass `duper.rule.clauseSubsumption

/-- Returns true if there exists a clause that subsumes c, and returns false otherwise -/
def forwardClauseSubsumption (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let potentialSubsumingClauses ← subsumptionTrie.getPotentialSubsumingClauses c
  trace[duper.rule.clauseSubsumption] "number of potentialSubsumingClauses for {c}: {potentialSubsumingClauses.size}"
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc nextClause => do
    match acc with
    | false =>
      conditionallyModifyingLoadedClauses do
        let nextClause ← loadClause nextClause
        if ← subsumptionCheck nextClause c cMVarIds then
          trace[duper.rule.clauseSubsumption] "Forward subsumption: removed {c.lits} because it was subsumed by {nextClause.lits}"
          return (true, true)
        else return (false, false)
    | true => return true
  let isSubsumed ← potentialSubsumingClauses.foldlM fold_fn false
  if isSubsumed then
    return some #[]
  else
    return none

/-- Returns the list of clauses that givenSubsumingClause subsumes -/
def backwardClauseSubsumption (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSubsumingClause => do
  let potentialSubsumedClauses ← subsumptionTrie.getPotentialSubsumedClauses givenSubsumingClause
  trace[duper.rule.clauseSubsumption] "number potentialSubsumedClauses for {givenSubsumingClause}: {potentialSubsumedClauses.size}"
  let givenSubsumingClause ← loadClause givenSubsumingClause
  let fold_fn := fun acc nextClause =>
    withoutModifyingMCtx do
      conditionallyModifyingLoadedClauses do
        let (nextClauseMVars, nextClauseM) ← loadClauseCore nextClause
        let nextClauseMVarIds := nextClauseMVars.map Expr.mvarId!
        if ← subsumptionCheck givenSubsumingClause nextClauseM nextClauseMVarIds then
          trace[duper.rule.clauseSubsumption] "Backward subsumption: removed {nextClause.lits} because it was subsumed by {givenSubsumingClause.lits}"
          return (true, acc.push nextClause)
        else return (false, acc)
  let clausesToRemove ← potentialSubsumedClauses.foldlM fold_fn #[]
  return clausesToRemove.map (fun x => (x, none))
