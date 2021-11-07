import LeanHammer.ProverM
import LeanHammer.Iterate
import LeanHammer.RuleM
import LeanHammer.MClause
import LeanHammer.Boolean
import Std.Data.BinomialHeap

namespace ProverM
open Lean
open Meta
open Lean.Core
open Result
open Std
open ProverM
open RuleM

set_option trace.Prover.debug true

set_option maxHeartbeats 10000


#check Option.map

def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  let cs? : Option (List Clause) ← RuleM.runAsProverM do
    let mclause ← MClause.fromClause givenClause
    let cs? ← clausificationStep mclause
    return ← cs?.mapM fun cs => cs.mapM fun c => c.toClause
  match cs? with
  | some [] => return none
  | some (c :: cs) => do
    for c' in cs do addToPassive c'
    some c
  | none => return some givenClause

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

end ProverM