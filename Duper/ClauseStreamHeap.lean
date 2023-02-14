import Std.Data.BinomialHeap
import Duper.Util.StreamHeap
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



def ProverM.runMetaAsProverM (x : MetaM α) : ProverM α := do
  let lctx ← getLCtx
  let mctx ← getMCtx
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) do
    x
  ProverM.setMCtx state.mctx
  return res

-- Clause Streams

private abbrev ClauseProof := Clause × RuleM.Proof

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
    let (res, state) ← RuleM.run cs.yieldClause (ctx := {order := order}) (s := {lctx := ← getLCtx, mctx := u.mctx})
    ProverM.setLCtx state.lctx
    return some (res, {cs with ug := ug'})
  else
    return some (none, {cs with ug := ug'})

instance : OptionMStream ProverM ClauseStream ClauseProof where
  next? (s : ClauseStream) := s.takeAsProverM

def performInferences (rules : List (MClause → Nat → RuleM ClauseStream)) (c : Clause) : ProverM Unit := do
  let cInfo ← getClauseInfo! c
  let cNum := cInfo.number
  for rule in rules do
    sorry



-- Status of the stream heap
--   The hashmap `nProbed` records the number of times a stream was chosen for probing

structure StreamHeapStatus where
  nProbed : HashMap Nat Nat := HashMap.empty
  fairnessCounter : Nat     := 0

-- The stream heap, for interleaving between inference and unification
-- The size of `heaps` should be 2. The first heap is the
--   weight heap and the second heap is the age heap.
-- Note that `ClauseStreamHeap` keeps track of each streams' age
--   by itself.
-- `α` is the type of clause
-- `σ` is the type of the clause stream
abbrev ClauseStreamHeap σ [OptionMStream ProverM σ ClauseProof] := StreamHeap σ (Option ClauseProof) (β:=StreamHeapStatus)

abbrev ClauseStreamHeap.empty m σ [Monad m] [OptionMStream ProverM σ ClauseProof] : ClauseStreamHeap σ :=
  { map := HashMap.empty, heaps := #[BinomialHeap.empty, BinomialHeap.empty],
    nextId := 0, status := ⟨HashMap.empty, 0⟩ }

def penalty (c : Clause) : ProverM Nat := pure 1

-- Following `Making Higher-Order Superposition Work`
-- But returns the modified heap along with `maybe_clause`
def ClauseStreamHeap.extractClause {σ} [OptionMStream ProverM σ ClauseProof]
  -- If `id` is `none`, then this is a new stream, and `weight` should be `0`
  -- If `id` is `some ?`, then this is a clause popped from the heap, and
  --   `id` is its id.
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

def heuristicProbe {σ} [OptionMStream ProverM σ ClauseProof]
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

def fairProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) (nOldest : Nat) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
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

def forceProbe {σ} [OptionMStream ProverM σ ClauseProof]
  (Q : ClauseStreamHeap σ) : ProverM (Array ClauseProof × ClauseStreamHeap σ) := do
  let mut collectedClauses := #[]
  let mut Q := Q
  while collectedClauses.size == 0 do
    let (clauses, Q') ← fairProbe Q Q.size
    if clauses.size != 0 then
      collectedClauses := clauses
      break
    Q := Q'
  return (collectedClauses, Q)