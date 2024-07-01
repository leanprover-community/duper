import Duper.ClauseStreamHeap
import Duper.RuleM
import Duper.MClause
import Duper.Preprocessing
import Duper.BackwardSimplification
import Duper.Rules.BetaEtaReduction
import Duper.Rules.BoolSimp
import Duper.Rules.Clausification
import Duper.Rules.ClausifyPropEq
import Duper.Rules.DecElim
import Duper.Rules.ElimDupLit
import Duper.Rules.ElimResolvedLit
import Duper.Rules.EqualityFactoring
import Duper.Rules.EqualityResolution
import Duper.Rules.FalseElim
import Duper.Rules.IdentBoolFalseElim
import Duper.Rules.IdentPropFalseElim
import Duper.Rules.Superposition
import Duper.Rules.SyntacticTautologyDeletion1
import Duper.Rules.SyntacticTautologyDeletion2
import Duper.Rules.SyntacticTautologyDeletion3
import Duper.Rules.DestructiveEqualityResolution
-- Boolean specific rules
import Duper.Rules.BoolHoist
import Duper.Rules.EqHoist
import Duper.Rules.ExistsHoist
import Duper.Rules.ForallHoist
import Duper.Rules.NeHoist
-- Inductive datatype rules
import Duper.Rules.DatatypeDistinctness
import Duper.Rules.DatatypeInjectivity
import Duper.Rules.DatatypeAcyclicity
-- Higher order rules
import Duper.Rules.ArgumentCongruence
import Duper.Rules.FluidSup
import Duper.Rules.FluidBoolHoist
-- Type inhabitation reasoning rules
import Duper.Util.TypeInhabitationReasoning

namespace Duper

namespace ProverM
open Lean
open Meta
open Lean.Core
open Result
open ProverM
open RuleM

initialize
  registerTraceClass `duper.timeout.debug
  registerTraceClass `duper.timeout.debug.fullActiveSet
  registerTraceClass `duper.timeout.debug.fullPassiveSet
  registerTraceClass `duper.misc.debug

open SimpResult

def forwardSimpRules : ProverM (Array SimpRule) := do
  let subsumptionTrie ← getSubsumptionTrie
  if ← getIncludeExpensiveRulesM then
    return #[
      betaEtaReduction.toSimpRule,
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
      datatypeDistinctness.toSimpRule, -- Inductive datatype rule
      datatypeInjectivity.toSimpRule, -- Inductive datatype rule
      datatypeAcyclicity.toSimpRule, -- Inductive datatype rule
      decElim.toSimpRule,
      (forwardDemodulation (← getDemodSidePremiseIdx)).toSimpRule,
      (forwardClauseSubsumption subsumptionTrie).toSimpRule,
      (forwardEqualitySubsumption subsumptionTrie).toSimpRule,
      (forwardContextualLiteralCutting subsumptionTrie).toSimpRule,
      (forwardPositiveSimplifyReflect subsumptionTrie).toSimpRule,
      (forwardNegativeSimplifyReflect subsumptionTrie).toSimpRule,
      identBoolHoist.toSimpRule -- Higher order rule
    ]
  else
    return #[
      betaEtaReduction.toSimpRule,
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
      datatypeDistinctness.toSimpRule, -- Inductive datatype rule
      datatypeInjectivity.toSimpRule, -- Inductive datatype rule
      datatypeAcyclicity.toSimpRule, -- Inductive datatype rule
      (forwardDemodulation (← getDemodSidePremiseIdx)).toSimpRule,
      (forwardClauseSubsumption subsumptionTrie).toSimpRule,
      (forwardEqualitySubsumption subsumptionTrie).toSimpRule,
      (forwardContextualLiteralCutting subsumptionTrie).toSimpRule,
      (forwardPositiveSimplifyReflect subsumptionTrie).toSimpRule,
      (forwardNegativeSimplifyReflect subsumptionTrie).toSimpRule,
      identBoolHoist.toSimpRule -- Higher order rule
    ]

-- The first `Clause` is the given clause
-- The second `MClause` is a loaded clause
def inferenceRules : ProverM (List (Clause → MClause → Nat → RuleM (Array ClauseStream))) := do
  if ← getIncludeExpensiveRulesM then
    return [
      equalityResolution,
      clausifyPropEq,
      superposition (← getSupMainPremiseIdx) (← getSupSidePremiseIdx),
      equalityFactoring,
      -- Prop specific rules
      falseElim,
      boolHoist,
      eqHoist,
      neHoist,
      existsHoist,
      forallHoist,
      -- Higher order rules
      argCong,
      fluidSup (← getFluidSupMainPremiseIdx) (← getSupSidePremiseIdx),
      fluidBoolHoist
    ]
  else
    return [
      equalityResolution,
      clausifyPropEq,
      superposition (← getSupMainPremiseIdx) (← getSupSidePremiseIdx),
      equalityFactoring,
      -- Prop specific rules
      falseElim,
      -- Higher order rules
      argCong
    ]

def applyForwardSimpRules (givenClause : Clause) : ProverM (SimpResult Clause) := do
  for simpRule in ← forwardSimpRules do
    match ← simpRule givenClause with
    | Removed => return Removed
    | Applied c => return Applied c
    | Unapplicable => continue
  return Unapplicable

/-- Uses other clauses in the active set to attempt to simplify the given clause. Returns some simplifiedGivenClause if
    forwardSimplify is able to use simplification rules to transform givenClause to simplifiedGivenClause. Returns none if
    forwardSimplify is able to use simplification rules to show that givenClause is unneeded.

    In addition to returning the simplifiedGivenClause, forwardSimplify also returns a Bool which indicates whether the
    clause can safely be used to simplify away other clauses. -/
partial def forwardSimplify (givenClause : Clause) : ProverM (Option (Clause × Bool)) := do
  trace[duper.prover.saturate] "forward simplifying {givenClause}"
  Core.checkMaxHeartbeats "forwardSimpLoop"
  let activeSet ← getActiveSet
  if activeSet.contains givenClause then return none
  if ← getInhabitationReasoningM then
    match ← removeVanishedVars givenClause with
    | some (givenClause, b) =>
      match ← applyForwardSimpRules givenClause with
      | Applied c => forwardSimplify c
      | Unapplicable => return some (givenClause, b)
      | Removed => return none
    | none => return none -- After removeVanishedVars, `givenClause` was transformed into a clause that has already been simplified away
  else
    match ← applyForwardSimpRules givenClause with
    | Applied c => forwardSimplify c
    | Unapplicable => return some (givenClause, true) -- When inhabitation reasoning is disabled, assume all types are nonempty
    | Removed => return none

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

/-- Used to check that the current instance of duper does not exceed the number of iterations allocated to it. -/
def checkSaturationIterout (iter : Nat) : CoreM Bool := do
  let opts ← getOptions
  let maxiter := getMaxSaturationIteration opts
  return iter > maxiter

/-- Used to check that the current instance of duper does not exceed the number of heartbeats allocated to it (which
    may be less than the overall tactic's max heartbeats if duper is running in portfolio mode). Returns true if this
    duper instance has exceeded its instance heartbeat allocation. -/
def checkInstanceMaxHeartbeats (initHeartbeats : Nat) (instanceMaxHeartBeats : Nat) : ProverM Bool := do
  if instanceMaxHeartBeats != 0 then -- Treat instanceMaxHeartBeats = 0 as all remaining heartbeats allocated to the current instance
    let numHeartbeats ← IO.getNumHeartbeats
    return numHeartbeats - initHeartbeats ≥ instanceMaxHeartBeats
  else
    return false

/-- Throws an error if duper has exceeded the total allowed max heartbeats, and returns true if duper has exeeded the max heartbeats
    or max iterations for this instance of duper. Returns false if neither of these are the case and duper may proceed-/
def checkSaturationTerminationCriterion (iter : Nat) (initHeartbeats : Nat) : ProverM Bool := do
  -- Check whether duper's overall maxheartbeat has been reached
  Core.checkMaxHeartbeats "saturate"
  -- Check whether the hearbeats allocated to this instance of duper (in portfolio mode) has been reached
  let check1 ← checkInstanceMaxHeartbeats initHeartbeats (← getInstanceMaxHeartbeats)
  -- Check whether maxiteration has been reached
  let check2 ← checkSaturationIterout iter
  return check1 || check2

def printTimeoutDebugStatements (startTime : Nat) : ProverM Unit := do
  checkSaturationTimeout startTime
  trace[duper.timeout.debug] "Size of active set: {(← getActiveSet).toArray.size}"
  trace[duper.timeout.debug] "Size of passive set: {(← getPassiveSet).toArray.size}"
  trace[duper.timeout.debug] "Number of total clauses: {(← getAllClauses).toArray.size}"
  trace[duper.timeout.debug] m!"Active set unit clause numbers: " ++
    m!"{← ((← getActiveSet).toArray.filter (fun x => x.lits.size = 1)).mapM (fun c => return (← getClauseInfo! c).number)}"
  trace[duper.timeout.debug] "Active set unit clauses: {(← getActiveSet).toArray.filter (fun x => x.lits.size = 1)}"
  trace[duper.timeout.debug] "Verified Inhabited Types: {(← getVerifiedInhabitedTypes).map (fun x => x.expr)}"
  trace[duper.timeout.debug] "Verified Nonempty Types: {(← getVerifiedNonemptyTypes).map (fun x => x.1.expr)}"
  trace[duper.timeout.debug] "Potentially Uninhabited Types: {(← getPotentiallyUninhabitedTypes).map (fun x => x.expr)}"
  trace[duper.timeout.debug] "Potentially Vacuous Clauses: {(← getPotentiallyVacuousClauses).toArray}"
  trace[duper.timeout.debug.fullActiveSet] m!"Active set numbers: " ++
    m!"{← ((← getActiveSet).toArray.mapM (fun c => return (← getClauseInfo! c).number))}"
  trace[duper.timeout.debug.fullActiveSet] "Active set: {(← getActiveSet).toArray}"
  trace[duper.timeout.debug.fullPassiveSet] m!"Passive set numbers: " ++
    m!"{← ((← getPassiveSet).toArray.mapM (fun c => return (← getClauseInfo! c).number))}"
  trace[duper.timeout.debug.fullPassiveSet] "Active set: {(← getPassiveSet).toArray}"

partial def saturate : ProverM Unit := do
  let startTime ← IO.monoMsNow
  let initHeartbeats ← IO.getNumHeartbeats
  Core.withCurrHeartbeats $ try
    let mut iter := 0
    while true do
      iter := iter + 1
      -- Check whether this duper instance has exceeded its allocated heartbeat or iteration limit (and return if so)
      if ← checkSaturationTerminationCriterion iter initHeartbeats then
        printTimeoutDebugStatements startTime
        setResult ProverM.Result.unknown -- Instance forced to terminate prior to reaching saturation or proving the goal
        return
      -- If the passive set is empty
      if (← getPassiveSet).isEmpty then
        -- ForceProbe
        runForceProbe
        -- If the passive set is still empty, the the prover has saturated
        if (← getPassiveSet).isEmpty then
          setResult saturated
          break
      -- Collect inference rules and perform inference
      let some givenClause ← chooseGivenClause
        | throwError "Saturate :: Saturation should have been checked in the beginning of the loop."
      trace[duper.prover.saturate] "Given clause: {givenClause}"
      let some (simplifiedGivenClause, simplifiedGivenClauseSafe) ← forwardSimplify givenClause
        | continue
      trace[duper.prover.saturate] "Given clause after simp: {simplifiedGivenClause} (simplifiedGivenClauseSafe: {simplifiedGivenClauseSafe})"
      if ← getInhabitationReasoningM then registerNewNonemptyTypes simplifiedGivenClause
      if simplifiedGivenClauseSafe then backwardSimplify simplifiedGivenClause -- Only do this if simplifiedGivenClause is certainly not vacuous
      else addPotentiallyVacuousClause simplifiedGivenClause -- We should re-evaluate simplifiedGivenClause when we learn new Nonempty type facts
      addToActive simplifiedGivenClause simplifiedGivenClauseSafe
      let inferenceRules ← inferenceRules
      performInferences inferenceRules simplifiedGivenClause
      -- Probe the clauseStreamHeap
      setQStreamSet <| ClauseStreamHeap.increaseFairnessCounter (← getQStreamSet)
      let fairnessCounter := (← getQStreamSet).status.fairnessCounter
      if fairnessCounter % kFair == 0 then
        runProbe (ClauseStreamHeap.fairProbe (fairnessCounter / kFair))
      else
        runProbe ClauseStreamHeap.heuristicProbe
      trace[duper.prover.saturate] "New active Set: {(← getActiveSet).toArray}"
      continue
    catch
    | e@(Exception.internal id _)  =>
      if id != ProverM.emptyClauseExceptionId then
        throwError e.toMessageData
      setResult ProverM.Result.contradiction
      return
    | e =>
      printTimeoutDebugStatements startTime
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
