import Duper.ProverM
import Duper.Util.Iterate
import Duper.RuleM
import Duper.MClause
import Duper.Rules.Clausification
import Duper.Simp
import Duper.Rules.Superposition
import Duper.Rules.ClausifyPropEq
import Duper.Rules.EqualityResolution
import Duper.Rules.TrivialSimp
import Duper.Rules.ElimDupLit
import Duper.Rules.Demodulation
import Std.Data.BinomialHeap

namespace Duper

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

def simpRules : ProverM (Array SimpRule) := do
  return #[
    (forwardDemodulation (← getSupMainPremiseIdx)).toSimpRule "forward demodulation",
    -- backwardDemodulation,
    clausificationStep.toSimpRule "clausification",
    trivialSimp.toSimpRule "trivial simp",
    elimDupLit.toSimpRule "eliminate duplicate literals"
  ]

def applySimpRules (givenClause : Clause) :
    ProverM (SimpResult Clause) := do
  for simpRule in ← simpRules do
    match ← simpRule givenClause with
    | Removed => return Removed
    | Applied c => return Applied c
    | Unapplicable => continue
  return Unapplicable

partial def simpLoop (givenClause : Clause) : ProverM (Option Clause) := do
  Core.checkMaxHeartbeats "simpLoop"
  match ← applySimpRules givenClause with
  | Applied c => 
    simpLoop c
  | Unapplicable => return some givenClause 
  | Removed => return none

def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  let c := simpLoop givenClause
  -- TODO: Check for empty clause and raise throwEmptyClauseException
  c

def backwardSimplify (givenClause : Clause) : ProverM Unit := do
  return ()

def performInferences (givenClause : Clause) : ProverM Unit := do
  performEqualityResolution givenClause
  performClausifyPropEq givenClause
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

end Duper
