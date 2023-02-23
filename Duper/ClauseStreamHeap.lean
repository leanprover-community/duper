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

def kUnifRetry := 40
def kFair := 70
def kBest := 7
def kRetry := 20
def forceProbeRetry := 500

@[inline] def ProverM.runMetaAsProverM (x : MetaM α) : ProverM α := do
  let lctx ← getLCtx
  let mctx ← getMCtx
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) do
    x
  ProverM.setMCtx state.mctx
  return res

-- Clause Streams

-- The first `Clause` is the (simplified)GivenClause
-- The second `Clause` is the conclusion
abbrev ClauseProof := Clause × Clause × RuleM.Proof

def ClauseStream.takeAsProverM (cs : ClauseStream)
  : ProverM (Option ((Option ClauseProof) × ClauseStream)) := do
  -- No more unification problem left
  if cs.ug.isEmpty then
    return none
  let (opu, ug') ← ProverM.runMetaAsProverM (cs.ug.takeWithRetry kUnifRetry)
  if let some u := opu then
    let symbolPrecMap ← getSymbolPrecMap
    let highesetPrecSymbolHasArityZero ← getHighesetPrecSymbolHasArityZero
    let order := λ e1 e2 => Order.kbo e1 e2 symbolPrecMap highesetPrecSymbolHasArityZero
    -- set `mctx` as the mctx of the unification problem
    -- set `lctx` as the lctx of ProverM
    let (res, state) ← RuleM.run cs.postUnification (ctx := {order := order}) (s := {lctx := ← getLCtx, mctx := u.mctx})
    ProverM.setLCtx state.lctx
    if let some clauseProof := res then
      return some ((cs.simplifiedGivenClause, clauseProof), {cs with ug := ug'})
    else
      return some (none, {cs with ug := ug'})
  else
    return some (none, {cs with ug := ug'})

instance : OptionMStream ProverM ClauseStream ClauseProof where
  next? (s : ClauseStream) := s.takeAsProverM

def penalty (c : Clause) : ProverM Nat := pure 1

-- Following `Making Higher-Order Superposition Work`
-- But returns the modified heap along with `maybe_clause`
  -- If `id` is `none`, then this is a new stream, and `weight` should be `0`
  -- If `id` is `some ?`, then this is a clause popped from the heap, and
  --   `id` is its id.
def ClauseStreamHeap.extractClause {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) (s : σ) (id : Option Nat) (weight : Nat) : ProverM (Option ClauseProof × ClauseStreamHeap σ) := do
  let next? ← MStream.next? s
  if let some (α?, stream') := next? then
    let nProbed :=
      if let some id := id then
        Q.status.nProbed.find! id
      else if weight != 0 then
        panic! "extractClause :: id is not given, but weight is not 0"
      else 0
    let mut weight := weight
    if let some (clause, _) := α? then
      weight := weight + (← penalty clause) * Nat.max 1 (nProbed - 64)
    else
      weight := weight + Nat.max 2 (nProbed - 16)
    let Q' :=
      if let some id := id then
        -- Only need to insert to weight heap, i.e., heap 0
        Q.insertToHeapN 0 (weight, id, stream')
      else
        let nextId := Q.nextId
        Q.insert stream' #[weight, nextId]
    return (α?, Q')
  else
    return (none, Q)

def ClauseStreamHeap.heuristicProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
  let mut i := 0
  let mut Q := Q
  let mut collectedClauses := #[]
  while i < kBest ∧ ¬ Q.isEmpty do
    let mut j := 0
    let mut maybeClause := none
    while j < kRetry ∧ ¬ Q.isEmpty do
      -- Delete min from weight heap
      let res := Q.deleteMinFromHeapN 0
      if let some ((prec, id, stream), Q') := res then
        let (mc, Q') ← ClauseStreamHeap.extractClause Q' stream (some id) prec
        if let some mc := mc then
          maybeClause := some mc
          Q := Q'
          break
        else
          Q := Q'
      j := j + 1
    if let some mc := maybeClause then
      collectedClauses := collectedClauses.push mc
    i := i + 1
  return (collectedClauses, Q)

def ClauseStreamHeap.fairProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (nOldest : Nat) (Q : ClauseStreamHeap σ) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
  let mut collectedClauses := #[]
  let mut oldestStream := #[]
  let mut Q := Q
  for _ in List.range nOldest do
    -- Delete min from weight heap
    let res := Q.deleteMinFromHeapN 0
    if let some (str, Q') := res then
      oldestStream := oldestStream.push str
      Q := Q'
    else
      break
  for (prec, id, stream) in oldestStream do
    let (mc, Q') ← ClauseStreamHeap.extractClause Q stream (some id) prec
    if let some mc := mc then
      collectedClauses := collectedClauses.push mc
    Q := Q'
  return (collectedClauses, Q)

def ClauseStreamHeap.forceProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
  let mut collectedClauses := #[]
  let mut Q := Q
  let mut iter := 0
  while collectedClauses.size == 0 ∧ Q.size != 0 ∧ iter < forceProbeRetry do
    let (clauses, Q') ← Q.fairProbe Q.size
    if clauses.size != 0 then
      collectedClauses := clauses
      break
    Q := Q'
    iter := iter + 1
  return (collectedClauses, Q)

-- Here `c` is `simplifiedGivenClause`
-- Note: This function is responsible for adding results of inference
--   rules to the passive set.
def ProverM.postProcessInferenceResult (cp : ClauseProof) : ProverM Unit := do
  let (given, c, proof) := cp
  match ← immediateSimplification given c with
  | some subsumingClause => -- subsumingClause subsumes c so we can remove c and only need to add subsumingClause
    removeClause given [subsumingClause]
    if c == subsumingClause then
      addNewToPassive c proof (List.map (fun p => p.clause) proof.parents)
    else
      throwError "Unable to find {subsumingClause} in resultClauses"
  | none => -- No result clause subsumes c, so add each result clause to the passive set
    addNewToPassive c proof (List.map (fun p => p.clause) proof.parents)

@[inline] def ProverM.runInferenceRule (x : RuleM (Array ClauseStream)) : ProverM (Array ClauseStream) := do
  let symbolPrecMap ← getSymbolPrecMap
  let highesetPrecSymbolHasArityZero ← getHighesetPrecSymbolHasArityZero
  let order := λ e1 e2 => Order.kbo e1 e2 symbolPrecMap highesetPrecSymbolHasArityZero
  let (streams, state) ← RuleM.run x (ctx := {order := order}) (s := {lctx := ← getLCtx, mctx := ← getMCtx})
  ProverM.setLCtx state.lctx
  return streams

def ProverM.performInferences (rules : List (Clause → MClause → Nat → RuleM (Array ClauseStream))) (given : Clause) : ProverM Unit := do
  let mut cs := #[]
  let cInfo ← getClauseInfo! given
  let cNum := cInfo.number
  for rule in rules do
    let curStreams ← runInferenceRule do
      let c ← loadClause given
      rule given c cNum
    cs := cs.append curStreams
  let mut Q ← getQStreamSet
  for stream in cs do
    let (mc, Q') ← Q.extractClause stream none 0
    Q := Q'
    if let some clauseProof := mc then
      postProcessInferenceResult clauseProof
  setQStreamSet Q

-- Run probe in ProverM
--   Take clause and proof from the stream, and run
--   `postProcessInferenceResult`
def ProverM.runProbe
  (probe : ClauseStreamHeap ClauseStream → ProverM (Array ClauseProof × ClauseStreamHeap ClauseStream)) := do
  let Q ← getQStreamSet
  let (arrcp, Q') ← probe Q
  setQStreamSet Q'
  let _ ← arrcp.mapM ProverM.postProcessInferenceResult