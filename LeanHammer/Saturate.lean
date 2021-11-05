import LeanHammer.ProverM
import LeanHammer.Iterate

namespace Prover
open Lean
open Lean.Core
open Result

set_option trace.Prover.debug true

set_option maxHeartbeats 1000

def emptyClauseFound : ProverM Bool := do
  (← getActiveSet).contains Clause.empty || 
  (← getPassiveSet).contains Clause.empty

def chooseGivenClause : ProverM (Option Clause) := do
  (← getPassiveSet).get? 0

def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  givenClause

def backwardSimplify (givenClause : Clause) : ProverM Unit := do
  ()

def performInferences (givenClause : Clause) : ProverM Unit := do
  ()

partial def saturate : ProverM Unit := do
  Core.withCurrHeartbeats $ iterate do
    if ← emptyClauseFound
    then 
      setResult contadiction
      return LoopCtrl.abort
    let some givenClause ← chooseGivenClause
      | do
        setResult saturated
        return LoopCtrl.abort
    let some givenClause ← forwardSimplify givenClause
      | return LoopCtrl.next
    backwardSimplify givenClause
    performInferences givenClause
    Core.checkMaxHeartbeats "saturate"
    return LoopCtrl.next
  trace[Prover.debug] "Done."
  trace[Prover.debug] "Result: {← getResult}"
  trace[Prover.debug] "Active: {← getActiveSet}"
  trace[Prover.debug] "Passive: {← getPassiveSet}"


#eval saturate

end Prover