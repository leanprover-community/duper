import LeanHammer.ProverM
import LeanHammer.Iterate
import LeanHammer.RuleM
import LeanHammer.MClause
import LeanHammer.Boolean
import LeanHammer.Simp
import LeanHammer.Superposition
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
  -- TODO: Check for empty clause and raise throwEmptyClauseException

def backwardSimplify (givenClause : Clause) : ProverM Unit := do
  ()

def performInferences (givenClause : Clause) : ProverM Unit := do
  performEqualityResolution givenClause
  performSuperposition givenClause

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
      setResult contradiction
      return LoopCtrl.abort
    | e => throw e

end ProverM