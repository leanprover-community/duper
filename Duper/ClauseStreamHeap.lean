import Std.Data.BinomialHeap
import Duper.Util.IdStrategyHeap
import Duper.Clause
import Duper.DUnif.UnifRules
import Duper.ProverM
import Lean

-- The reason we need `ProverM` here is because we need to calculate
-- the penalty of each clause.

open Lean
open Std

namespace Duper
open ProverM
open RuleM

def kFair := 70
def kBest := 3
def kHighest := 10

register_option forceProbeRetry : Nat := {
  defValue := 500
  descr := "Iteration limit for forceProbe"
}

def getForceProbeRetry (opts : Options) : Nat :=
  forceProbeRetry.get opts

def logForceProbeRetry (max : Nat) : CoreM Unit := do
  let msg := s!"forceProbe exceeded iteration limit {max}"
  logInfo msg

register_option kStep : Nat := {
  defValue := 40
  descr := "Maximum steps a unification problem can take before it's postponed"
}

-- Clause Streams

-- The first `Clause` is the (simplified)GivenClause
-- The second `Clause` is the conclusion
abbrev ClauseProof := Clause × Clause × RuleM.Proof

def ClauseStream.takeAsProverM (cs : ClauseStream)
  : ProverM (Option ((Option ClauseProof) × ClauseStream)) := do
  -- No more unification problem left
  if cs.ug.isEmpty then
    return none
  let (opu, ug') ← cs.ug.takeWithRetry (kStep.get (← getOptions))
  if let some u := opu then
    let res ← ProverM.runRuleM <| do
      -- set `mctx` as the mctx of the unification problem
      setMCtx u.mctx
      cs.postUnification
    if let some clauseProof := res then
      return some ((cs.simplifiedGivenClause, clauseProof), {cs with ug := ug'})
    else
      return some (none, {cs with ug := ug'})
  else
    if ug'.isEmpty then
      return none
    else
      return some (none, {cs with ug := ug'})

instance : OptionMStream ProverM ClauseStream ClauseProof where
  next? (s : ClauseStream) := s.takeAsProverM

def penalty (c : Clause) : ProverM Nat := pure 1

def updateWeight (α? : Option ClauseProof) (weight : Nat) (nProbed : Nat) : ProverM Nat := do
  if let some (clause, _) := α? then
    return weight + (← penalty clause) * Nat.max 1 (nProbed - 64)
  else
    return weight + Nat.max 2 (nProbed - 16)

/-- Following `Making Higher-Order Superposition Work`.
    Extract an `Option Clause` from the stream.
    Add the rest of the stream to the heap. -/
def ClauseStreamHeap.extractClause {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) (nProbed : Nat) (precs : Array Nat) (s : σ) : ProverM (Option ClauseProof × ClauseStreamHeap σ) := do
  have : Inhabited σ := ⟨s⟩
  let next? ← MStream.next? s
  if let some (α?, stream') := next? then
    -- If this stream is not empty, extract clause from the
    -- stream and add it back to the heap
    let weight₀ := precs[0]!
    let weight ← updateWeight α? weight₀ nProbed
    let precs' := precs.set! 0 weight
    let Q' := Q.insertWithNProbed stream' precs' (nProbed + 1)
    return (α?, Q')
  else
    -- If this stream is already empty, then do nothing
    return (none, Q)

def ClauseStreamHeap.heuristicProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
  let mut collectedClauses := #[]
  let mut highestStream := #[]
  let mut Q := Q
  for _ in List.range kHighest do
    let res := Q.deleteMinWithNProbed 0
    if let some (str, Q') := res then
      highestStream := highestStream.push str
      Q := Q'
    else
      break
  for (nProbed, precs, stream) in highestStream do
    let (mc, Q') ← ClauseStreamHeap.extractClause Q nProbed precs stream
    if let some mc := mc then
      collectedClauses := collectedClauses.push mc
    Q := Q'
  return (collectedClauses, Q)

def ClauseStreamHeap.fairProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (nOldest : Nat) (Q : ClauseStreamHeap σ) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
  let mut collectedClauses := #[]
  let mut oldestStream := #[]
  let mut Q := Q
  for _ in List.range nOldest do
    -- Delete min from age heap
    let res := Q.deleteMinWithNProbed 1
    if let some (str, Q') := res then
      oldestStream := oldestStream.push str
      Q := Q'
    else
      break
  for (nProbed, precs, stream) in oldestStream do
    let (mc, Q') ← ClauseStreamHeap.extractClause Q nProbed precs stream
    if let some mc := mc then
      collectedClauses := collectedClauses.push mc
    Q := Q'
  return (collectedClauses, Q)

/-- Here `c` is `simplifiedGivenClause`. This function is responsible for adding results of inference rules to the passive set. -/
def ProverM.postProcessInferenceResult (cp : ClauseProof) : ProverM Unit := do
  let (given, c, proof) := cp
  let allClauses ← getAllClauses
  let parentClauseInfoOpts ← proof.parents.mapM
    (fun p =>
      match allClauses.find? p.clause with
      | some pi => pure pi
      | none => throwError "ProverM.postProcessInferenceResult: Unable to find parent clause {p.clause}")
  -- c's generation number is one greater than the sum of its parents generation numbers
  let generationNumber := parentClauseInfoOpts.foldl (fun acc parentInfo => acc + parentInfo.generationNumber) 1
  -- c's goalDistance is at most maxGoalDistance and is otherwise one greater than the distance of the parent closest to the goal
  let goalDistance := parentClauseInfoOpts.foldl (fun acc parentInfo => Nat.min acc (parentInfo.goalDistance + 1)) maxGoalDistance
  match ← immediateSimplification given c with
  | some subsumingClause => -- subsumingClause subsumes c so we can remove c and only need to add subsumingClause
    removeClause given [subsumingClause]
    if c == subsumingClause then
      addNewToPassive c proof goalDistance generationNumber (proof.parents.map (fun p => p.clause))
    else
      throwError "Unable to find {subsumingClause} in resultClauses"
  | none => -- No result clause subsumes c, so add each result clause to the passive set
    addNewToPassive c proof goalDistance generationNumber (proof.parents.map (fun p => p.clause))

def ProverM.performInferences (rules : List (Clause → MClause → Nat → RuleM (Array ClauseStream))) (given : Clause) : ProverM Unit := do
  trace[Prover.saturate] "perform inference with given clause {given}"
  let mut cs := #[]
  let cInfo ← getClauseInfo! given
  let cNum := cInfo.number
  for rule in rules do
    let curStreams ← runRuleM do
      let c ← loadClause given
      rule given c cNum
    cs := cs.append curStreams
  let mut Q ← getQStreamSet
  for stream in cs do
    let (mc, Q') ← Q.extractClause 0 #[0, Q.nextId] stream
    Q := Q'
    if let some clauseProof := mc then
      postProcessInferenceResult clauseProof
  setQStreamSet Q

-- Run probe in ProverM
--   Take clause and proof from the stream, and run `postProcessInferenceResult`
def ProverM.runProbe
  (probe : ClauseStreamHeap ClauseStream → ProverM (Array ClauseProof × ClauseStreamHeap ClauseStream)) := do
  let Q ← getQStreamSet
  let (arrcp, Q') ← probe Q
  setQStreamSet Q'
  let _ ← arrcp.mapM ProverM.postProcessInferenceResult

/-- We have to repeatedly call `runProbe` and test `(← getPassiveSet).isEmpty`
    If we return immediately when `fairProbe` yields a nonempty list of clauses, it is possible that all of these clauses
    are redundant and `postProcessInferenceResult` will remove all of them, which will cause `saturate` to think that the prover
    has saturated. -/
def ProverM.runForceProbe : ProverM Unit := do
    let maxIter := getForceProbeRetry (← getOptions)
    let mut fpiter := 0
    while (← getQStreamSet).size != 0 ∧ (← getPassiveSet).isEmpty do
      runProbe (ClauseStreamHeap.fairProbe (← getQStreamSet).size)
      fpiter := fpiter + 1
      if fpiter >= maxIter then
        logForceProbeRetry maxIter
        break
