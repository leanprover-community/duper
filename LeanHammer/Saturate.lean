import LeanHammer.ProverM
import LeanHammer.Iterate
import LeanHammer.RuleM
import LeanHammer.MClause
import LeanHammer.Boolean
import LeanHammer.Simp
import LeanHammer.Inferences.Superposition
import LeanHammer.Inferences.EqualityResolution
import LeanHammer.TrivialSimp
import Std.Data.BinomialHeap

namespace Schroedinger

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

def simpRules := #[
  (clausificationStep.toSimpRule, "clausification"),
  (trivialSimp.toSimpRule, "trivial simp")
]

def applySimpRules (givenClause : Clause) :
    ProverM (SimpResult Clause) := do
  for (simpRule, ruleName) in simpRules do
    match ← simpRule ruleName givenClause with
    | Removed => return Removed
    | Applied c => return Applied c
    | Unapplicable => continue
  return Unapplicable

partial def simpLoop (givenClause : Clause) : ProverM (Option Clause) := do
  Core.checkMaxHeartbeats "simpLoop"
  match ← applySimpRules givenClause with
  | Applied c => 
    simpLoop c
  | Unapplicable => some givenClause 
  | Removed => none

def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
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
      Core.checkMaxHeartbeats "saturate"
      let some givenClause ← chooseGivenClause
        | do
          setResult saturated
          return LoopCtrl.abort
      trace[Prover.saturate] "### Given clause: {givenClause}"
      let some givenClause ← forwardSimplify givenClause
        | return LoopCtrl.next
      trace[Prover.saturate] "### Given clause after simp: {givenClause}"
      backwardSimplify givenClause
      addToActive givenClause
      performInferences givenClause
      trace[Prover.saturate] "### New active Set: {(← getActiveSet).toArray}"
      return LoopCtrl.next
    catch
    | Exception.internal emptyClauseExceptionId _  =>
      setResult contradiction
      return LoopCtrl.abort
    | e => throw e

end ProverM

end Schroedinger