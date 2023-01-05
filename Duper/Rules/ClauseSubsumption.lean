import Duper.Simp
import Duper.Util.ClauseSubsumptionCheck

namespace Duper

open Lean
open RuleM
open SimpResult

initialize Lean.registerTraceClass `Rule.clauseSubsumption

/-- Returns true if there exists a clause that subsumes c, and returns false otherwise -/
def forwardClauseSubsumption (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let potentialSubsumingClauses ← subsumptionTrie.getPotentialSubsumingClauses c
  trace[Rule.clauseSubsumption] "number of potentialSubsumingClauses for {c}: {potentialSubsumingClauses.size}"
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc nextClause => do
    match acc with
    | false =>
      conditionallyModifyingLoadedClauses do
        let nextClause ← loadClause nextClause
        if ← subsumptionCheck nextClause c cMVarIds then
          trace[Rule.clauseSubsumption] "Forward subsumption: removed {c.lits} because it was subsumed by {nextClause.lits}"
          return (true, true)
        else return (false, false)
    | true => return true
  potentialSubsumingClauses.foldlM fold_fn false

/-- Returns the list of clauses that givenSubsumingClause subsumes -/
def backwardClauseSubsumption (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSubsumingClause => do
  let potentialSubsumedClauses ← subsumptionTrie.getPotentialSubsumedClauses givenSubsumingClause
  trace[Rule.clauseSubsumption] "number potentialSubsumedClauses for {givenSubsumingClause}: {potentialSubsumedClauses.size}"
  let givenSubsumingClause ← loadClause givenSubsumingClause
  let fold_fn := fun acc nextClause =>
    conditionallyModifyingLoadedClauses do
      let (nextClauseMVars, nextClauseM) ← loadClauseCore nextClause
      let nextClauseMVarIds := nextClauseMVars.map Expr.mvarId!
      if ← subsumptionCheck givenSubsumingClause nextClauseM nextClauseMVarIds then
        trace[Rule.clauseSubsumption] "Backward subsumption: removed {nextClause.lits} because it was subsumed by {givenSubsumingClause.lits}"
        return (true, (nextClause :: acc))
      else return (false, acc)
  potentialSubsumedClauses.foldlM fold_fn []