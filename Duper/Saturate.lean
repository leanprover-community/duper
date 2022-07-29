import Duper.ProverM
import Duper.Util.Iterate
import Duper.RuleM
import Duper.MClause
import Duper.Rules.Clausification
import Duper.Simp
import Duper.Rules.Superposition
import Duper.Rules.ClausifyPropEq
import Duper.Rules.EqualityResolution
import Duper.Rules.SyntacticTautologyDeletion1
import Duper.Rules.SyntacticTautologyDeletion2
import Duper.Rules.ElimDupLit
import Duper.Rules.Demodulation
import Duper.Rules.ElimResolvedLit
import Duper.Rules.DestructiveEqualityResolution
import Duper.Rules.EqualityFactoring
import Duper.Rules.IdentBoolFalseElim
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

initialize
  registerTraceClass `Simp
  registerTraceClass `Simp.debug

set_option trace.Prover.debug true

set_option maxHeartbeats 10000

open SimpResult

def simpRules : ProverM (Array SimpRule) := do
  return #[
    (forwardDemodulation (← getDemodSidePremiseIdx)).toSimpRule "forward demodulation (rewriting of positive/negative literals)",
    clausificationStep.toSimpRule "clausification",
    syntacticTautologyDeletion1.toSimpRule "syntactic tautology deletion 1",
    syntacticTautologyDeletion2.toSimpRule "syntactic tautology deletion 2",
    elimDupLit.toSimpRule "eliminate duplicate literals",
    elimResolvedLit.toSimpRule "eliminate resolved literals",
    destructiveEqualityResolution.toSimpRule "destructive equality resolution",
    identBoolFalseElim.toSimpRule "identity boolean false elimination"
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
  c

def backwardSimplify (givenClause : Clause) : ProverM Unit := do
  -- TODO: Add backward demodulation
  return ()

def performInferences (givenClause : Clause) : ProverM Unit := do
  performEqualityResolution givenClause
  performClausifyPropEq givenClause
  performSuperposition givenClause
  performEqualityFactoring givenClause

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
        | do
          removeFromDiscriminationTrees givenClause
          return LoopCtrl.next
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
