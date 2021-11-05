import LeanHammer.ProverM
import LeanHammer.Iterate
import Std.Data.BinomialHeap

namespace Prover
open Lean
open Lean.Core
open Result
open Std

set_option trace.Prover.debug true

set_option maxHeartbeats 10000

def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  givenClause

def backwardSimplify (givenClause : Clause) : ProverM Unit := do
  ()

def performInferences (givenClause : Clause) : ProverM Unit := do
  ()

-- throwEmptyClauseException

partial def saturate : ProverM Unit := do
  Core.withCurrHeartbeats $ iterate $
    try do
      let some givenClause ← chooseGivenClause
        | do
          setResult saturated
          return LoopCtrl.abort
      let some givenClause ← forwardSimplify givenClause
        | return LoopCtrl.next
      backwardSimplify givenClause
      addToActive givenClause
      performInferences givenClause
      Core.checkMaxHeartbeats "saturate"
      return LoopCtrl.next
    catch
    | Exception.internal emptyClauseExceptionId _  =>
      setResult contadiction
      return LoopCtrl.abort
    | e => throw e
  trace[Prover.debug] "Done."
  trace[Prover.debug] "Result: {← getResult}"
  trace[Prover.debug] "Active: {(← getActiveSet).toArray}"
  trace[Prover.debug] "Passive: {(← getPassiveSet).toArray}"
  
#check BinomialHeap
#eval saturate

end Prover