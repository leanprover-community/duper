import Std.Data.BinomialHeap
import Duper.ProverM
import Duper.Util.Iterate
import Duper.RuleM
import Duper.MClause
import Duper.Simp
import Duper.Preprocessing
import Duper.Rules.BoolSimp
import Duper.Rules.ClauseSubsumption
import Duper.Rules.Clausification
import Duper.Rules.ClausifyPropEq
import Duper.Rules.ContextualLiteralCutting
import Duper.Rules.Demodulation
import Duper.Rules.ElimDupLit
import Duper.Rules.ElimResolvedLit
import Duper.Rules.EqualityFactoring
import Duper.Rules.EqualityResolution
import Duper.Rules.EqualitySubsumption
import Duper.Rules.FalseElim
import Duper.Rules.IdentBoolFalseElim
import Duper.Rules.IdentPropFalseElim
import Duper.Rules.SimplifyReflect
import Duper.Rules.Superposition
import Duper.Rules.SyntacticTautologyDeletion1
import Duper.Rules.SyntacticTautologyDeletion2
import Duper.Rules.SyntacticTautologyDeletion3
import Duper.Rules.DestructiveEqualityResolution
-- Higher order rules
import Duper.Rules.ArgumentCongruence
import Duper.Rules.BoolHoist

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
  registerTraceClass `Timeout.debug

open SimpResult

def forwardSimpRules : ProverM (Array SimpRule) := do
  let subsumptionTrie ← getSubsumptionTrie
  return #[
    clausificationStep.toSimpRule,
    syntacticTautologyDeletion1.toSimpRule,
    syntacticTautologyDeletion2.toSimpRule,
    boolSimp.toSimpRule,
    syntacticTautologyDeletion3.toSimpRule,
    elimDupLit.toSimpRule,
    elimResolvedLit.toSimpRule,
    destructiveEqualityResolution.toSimpRule,
    identPropFalseElim.toSimpRule,
    identBoolFalseElim.toSimpRule,
    (forwardDemodulation (← getDemodSidePremiseIdx)).toSimpRule,
    (forwardClauseSubsumption subsumptionTrie).toSimpRule,
    (forwardEqualitySubsumption subsumptionTrie).toSimpRule,
    (forwardContextualLiteralCutting subsumptionTrie).toSimpRule,
    (forwardPositiveSimplifyReflect subsumptionTrie).toSimpRule,
    (forwardNegativeSimplifyReflect subsumptionTrie).toSimpRule,
    -- Higher order rules
    boolHoist.toSimpRule
  ]

def backwardSimpRules : ProverM (Array BackwardSimpRule) := do
  let subsumptionTrie ← getSubsumptionTrie
  return #[
    (backwardDemodulation (← getMainPremiseIdx)).toBackwardSimpRule,
    (backwardClauseSubsumption subsumptionTrie).toBackwardSimpRule,
    (backwardEqualitySubsumption subsumptionTrie).toBackwardSimpRule,
    (backwardContextualLiteralCutting subsumptionTrie).toBackwardSimpRule,
    (backwardPositiveSimplifyReflect subsumptionTrie).toBackwardSimpRule,
    (backwardNegativeSimplifyReflect subsumptionTrie).toBackwardSimpRule
  ]

def applyForwardSimpRules (givenClause : Clause) : ProverM (SimpResult Clause) := do
  for simpRule in ← forwardSimpRules do
    match ← simpRule givenClause with
    | Removed => return Removed
    | Applied c => return Applied c
    | Unapplicable => continue
  return Unapplicable

partial def forwardSimpLoop (givenClause : Clause) : ProverM (Option Clause) := do
  Core.checkMaxHeartbeats "forwardSimpLoop"
  let activeSet ← getActiveSet
  match ← applyForwardSimpRules givenClause with
  | Applied c =>
    if activeSet.contains c then return none
    else forwardSimpLoop c
  | Unapplicable => return some givenClause 
  | Removed => return none

/-- Uses other clauses in the active set to attempt to simplify the given clause. Returns some simplifiedGivenClause if
    forwardSimpLoop is able to use simplification rules to transform givenClause to simplifiedGivenClause. Returns none if
    forwardSimpLoop is able to use simplification rules to show that givenClause is unneeded. -/
def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  let c := forwardSimpLoop givenClause
  c

/-- Attempts to use givenClause to apply backwards simplification rules (starting from the startIdx's backward simplification rule) on clauses
    in the active set. -/
def applyBackwardSimpRules (givenClause : Clause) : ProverM Unit := do
  let backwardSimpRules ← backwardSimpRules
  for i in [0 : backwardSimpRules.size] do
    let simpRule := backwardSimpRules[i]!
    simpRule givenClause

/-- Uses the givenClause to attempt to simplify other clauses in the active set. For each clause that backwardSimplify is
    able to produce a simplification for, backwardSimplify removes the clause adds any newly simplified clauses to the passive set.
    Additionally, for each clause removed from the active set in this way, all descendents of said clause should also be removed from
    the current state's allClauses and passiveSet -/
def backwardSimplify (givenClause : Clause) : ProverM Unit := applyBackwardSimpRules givenClause

def inferenceRules : ProverM (List (MClause → Nat → RuleM Unit)) := do
  return [
  equalityResolution,
  clausifyPropEq,
  superposition (← getMainPremiseIdx) (← getSupSidePremiseIdx),
  equalityFactoring,
  -- Prop specific rules
  falseElim,
  -- Higher order rules
  argCong
]

partial def saturate : ProverM Unit := do
  Core.withCurrHeartbeats $ iterate $
    try do
      Core.checkMaxHeartbeats "saturate"
      let some givenClause ← chooseGivenClause
        | do
          setResult saturated
          return LoopCtrl.abort
      trace[Prover.saturate] "Given clause: {givenClause}"
      let some simplifiedGivenClause ← forwardSimplify givenClause
        | return LoopCtrl.next
      trace[Prover.saturate] "Given clause after simp: {simplifiedGivenClause}"
      backwardSimplify simplifiedGivenClause
      addToActive simplifiedGivenClause
      let inferenceRules ← inferenceRules
      performInferences inferenceRules simplifiedGivenClause
      trace[Prover.saturate] "New active Set: {(← getActiveSet).toArray}"
      return LoopCtrl.next
    catch
    | Exception.internal emptyClauseExceptionId _  =>
      setResult ProverM.Result.contradiction
      return LoopCtrl.abort
    | e =>
      -- trace[Timeout.debug] "Active set at timeout: {(← getActiveSet).toArray}"
      trace[Timeout.debug] "Size of active set: {(← getActiveSet).toArray.size}"
      trace[Timeout.debug] "Size of passive set: {(← getPassiveSet).toArray.size}"
      trace[Timeout.debug] "Number of total clauses: {(← getAllClauses).toArray.size}"
      trace[Timeout.debug] "Active set unit clauses: {(← getActiveSet).toArray.filter (fun x => x.lits.size = 1)}"
      -- trace[Timeout.debug] "All clauses at timeout: {Array.map (fun x => x.1) (← getAllClauses).toArray}"
      throw e

def clausifyThenSaturate : ProverM Unit := do
  Core.withCurrHeartbeats $
    preprocessingClausification;
    let (symbolPrecMap, highesetPrecSymbolHasArityZero) ← buildSymbolPrecMap (← getPassiveSet).toList;
    setSymbolPrecMap symbolPrecMap;
    setHighesetPrecSymbolHasArityZero highesetPrecSymbolHasArityZero;
    saturate

def saturateNoPreprocessingClausification : ProverM Unit := do
  Core.withCurrHeartbeats $ do
    let (symbolPrecMap, highesetPrecSymbolHasArityZero) ← buildSymbolPrecMap (← getPassiveSet).toList;
    setSymbolPrecMap symbolPrecMap;
    setHighesetPrecSymbolHasArityZero highesetPrecSymbolHasArityZero;
    saturate

end ProverM

end Duper
