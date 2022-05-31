import Duper.Simp

namespace Duper

open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.demodulation

def forwardDemodulation (idx : ProverM.ClauseDiscrTree ClausePos) : MSimpRule := fun c => do
  if c.lits.size == 1 ∧ c.lits[0].sign then
    let l := c.lits[0]
    let c ← compare l.lhs l.rhs
    if c == Incomparable ∨ c == Equal then
      return Unapplicable
    let l := if c == LessThan then l.symm else l
    let partnerClauses ← DiscrTree.getMatch idx l.lhs
    trace[Rule.demodulation] "Demodulation Clause: {l}"
    trace[Rule.demodulation] "partners: {partnerClauses.map Prod.fst}"
    return Unapplicable
  else
    return Unapplicable

--TODO: Whereever indices are passed in (e.g. Sup), pass a closure instead
-- that checks whether the clauses found in the index are still in the
-- active set.