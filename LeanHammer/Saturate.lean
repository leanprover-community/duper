import LeanHammer.ProverM
import LeanHammer.Iterate
import LeanHammer.RuleM
import LeanHammer.MClause
import LeanHammer.Boolean
import LeanHammer.Simp
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

open SimpResult

def simpRules := #[clausificationStep.toSimpRule]

def applySimpRules (givenClause : Clause) (simpRules : Array SimpRule) :
    ProverM (SimpResult Clause) := do
  for simpRule in simpRules do
    match ← simpRule givenClause with
    | Removed => return Removed
    | Applied c => return Applied c
    | Unapplicable => continue
  return Unapplicable

partial def simpLoop (givenClause : Clause) : ProverM (Option Clause) := do
  match ← applySimpRules givenClause simpRules with
  | Applied c => 
    simpLoop c
  | Unapplicable => some givenClause 
  | Removed => none

partial def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  simpLoop givenClause

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