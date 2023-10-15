import Duper.ProverM
import Duper.Simp
import Duper.Rules.ClauseSubsumption
import Duper.Rules.ContextualLiteralCutting
import Duper.Rules.Demodulation
import Duper.Rules.EqualitySubsumption
import Duper.Rules.SimplifyReflect

namespace Duper
namespace ProverM

def backwardSimpRules : ProverM (Array BackwardSimpRule) := do
  let subsumptionTrie ← getSubsumptionTrie
  return #[
    (backwardDemodulation (← getDemodMainPremiseIdx)).toBackwardSimpRule,
    (backwardClauseSubsumption subsumptionTrie).toBackwardSimpRule,
    (backwardEqualitySubsumption subsumptionTrie).toBackwardSimpRule,
    (backwardContextualLiteralCutting subsumptionTrie).toBackwardSimpRule,
    (backwardPositiveSimplifyReflect subsumptionTrie).toBackwardSimpRule,
    (backwardNegativeSimplifyReflect subsumptionTrie).toBackwardSimpRule
  ]

/-- Uses the givenClause to attempt to simplify other clauses in the active set. For each clause that backwardSimplify is
    able to produce a simplification for, backwardSimplify removes the clause adds any newly simplified clauses to the passive set.
    Additionally, for each clause removed from the active set in this way, all descendents of said clause should also be removed from
    the current state's allClauses and passiveSet -/
def backwardSimplify (givenClause : Clause) : ProverM Unit := do
  trace[Prover.saturate] "backward simplify with {givenClause}"
  let backwardSimpRules ← backwardSimpRules
  for i in [0 : backwardSimpRules.size] do
    let simpRule := backwardSimpRules[i]!
    simpRule givenClause