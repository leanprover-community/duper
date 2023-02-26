import Std.Data.BinomialHeap
import Duper.ProverM
import Duper.ClauseStreamHeap
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
-- Boolean specific rules
import Duper.Rules.BoolHoist
import Duper.Rules.EqHoist
import Duper.Rules.ExistsHoist
import Duper.Rules.NeHoist
-- Higher order rules
import Duper.Rules.ArgumentCongruence

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
    identBoolHoist.toSimpRule
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

-- The first `Clause` is the given clause
-- The second `MClause` is a loaded clause
def inferenceRules : ProverM (List (Clause → MClause → Nat → RuleM (Array ClauseStream))) := do
  return [
  equalityResolution,
  clausifyPropEq,
  superposition (← getMainPremiseIdx) (← getSupSidePremiseIdx),
  equalityFactoring,
  -- Prop specific rules
  falseElim,
  -- Higher order rules
  argCong,
  boolHoist,
  eqHoist,
  neHoist,
  existsHoist
]

register_option maxSaturationTime : Nat := {
  defValue := 500
  descr := "Time limit for saturation procedure, in s"
}

def getMaxSaturationTime (opts : Options) : Nat :=
  maxSaturationTime.get opts * 1000

def logSaturationTimeout (max : Nat) : CoreM Unit := do
  let msg := s!"Saturation procedure timed out, maximum time {max / 1000}s has been reached"
  logInfo msg

def checkSaturationTimeout (startTime : Nat) : CoreM Unit := do
  let currentTime ← IO.monoMsNow
  let opts ← getOptions
  let max := getMaxSaturationTime opts
  if currentTime - startTime > max then
    logSaturationTimeout max

register_option maxSaturationIteration : Nat := {
  defValue := 500000
  descr := "Limit for number of iterations in the saturation loop"
}

def getMaxSaturationIteration (opts : Options) : Nat :=
  maxSaturationIteration.get opts

def throwSaturationIterout (max : Nat) : CoreM Unit := do
  let msg := s!"Saturation procedure exceeded iteration limit {max}"
  throw <| Exception.error (← getRef) (MessageData.ofFormat (Std.Format.text msg))

def checkSaturationIterout (iter : Nat) : CoreM Unit := do
  let opts ← getOptions
  let maxiter := getMaxSaturationIteration opts
  if iter > maxiter then
    throwSaturationIterout maxiter

def checkSaturationTerminationCriterion (iter : Nat) : ProverM Unit := do
  -- Check whether maxheartbeat has been reached
  Core.checkMaxHeartbeats "saturate"
  -- Check whether maxiteration has been reached
  checkSaturationIterout iter

partial def saturate : ProverM Unit := do
  let startTime ← IO.monoMsNow
  Core.withCurrHeartbeats $ try
    let mut iter := 0
    while true do
      iter := iter + 1
      checkSaturationTerminationCriterion iter
      -- If the passive set is empty
      if (← getPassiveSet).isEmpty then
        -- ForceProbe
        runProbe ClauseStreamHeap.forceProbe
        -- If the passive set is still empty, the the prover has saturated
        if (← getPassiveSet).isEmpty then
          setResult saturated
          break
      -- Collect inference rules and perform inference
      let some givenClause ← chooseGivenClause
        | throwError "saturate :: Saturation should have been checked in the beginning of the loop."
      trace[Prover.saturate] "Given clause: {givenClause}"
      let some simplifiedGivenClause ← forwardSimplify givenClause
        | continue
      trace[Prover.saturate] "Given clause after simp: {simplifiedGivenClause}"
      backwardSimplify simplifiedGivenClause
      addToActive simplifiedGivenClause
      let inferenceRules ← inferenceRules
      performInferences inferenceRules simplifiedGivenClause
      -- Probe the clauseStreamHeap
      setQStreamSet <| ClauseStreamHeap.increaseFairnessCounter (← getQStreamSet)
      let fairnessCounter := (← getQStreamSet).status.fairnessCounter
      if fairnessCounter % kFair == 0 then
        runProbe (ClauseStreamHeap.fairProbe (fairnessCounter / kFair))
      else
        runProbe ClauseStreamHeap.heuristicProbe
      trace[Prover.saturate] "New active Set: {(← getActiveSet).toArray}"
      continue
    catch
    | Exception.internal emptyClauseExceptionId _  =>
      setResult ProverM.Result.contradiction
      return
    | e =>
      -- trace[Timeout.debug] "Active set at timeout: {(← getActiveSet).toArray}"
      checkSaturationTimeout startTime
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
