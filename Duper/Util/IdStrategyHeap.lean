import Batteries.Data.BinomialHeap
import Lean

open Lean
open Batteries

namespace Duper

-- Stream with side effect
class MStream (m) [Monad m] (stream : Type _) (value : outParam (Type _)) : Type _ where
  next? : stream → m (Option (value × stream))

-- Stream with side effect and returning value of type `Option`
abbrev OptionMStream m [Monad m] stream value := MStream m stream (Option value)

-- `IdStrategyHeap` models operations on inference streams
-- `σ` : The type of the stream
-- `α` : Type of elements in the stream
-- We can't expect the monadic stream to be hashable, so we give
--   each stream a `id`.
structure IdStrategyHeap (σ : Type w) {β : Type v} where
  -- Map of `id` to clause heap
  map            : Std.HashMap Nat (Array Nat × σ) := Std.HashMap.empty
  -- The first `Nat` is the precedence, and the second `Nat` is the `id`
  heaps          : Array (BinomialHeap (Nat × Nat) fun c d => c.1 ≤ d.1) := #[]
  nextId         : Nat
  status         : β
  deriving Inhabited

def IdStrategyHeap.isEmpty (oh : IdStrategyHeap σ (β:=β)) := oh.map.isEmpty

def IdStrategyHeap.size (oh : IdStrategyHeap σ (β:=β)) := oh.map.size

def IdStrategyHeap.contains (oh : IdStrategyHeap σ (β:=β)) (id : Nat) := oh.map.contains id

-- We can only erase `id` from the stream
private def IdStrategyHeap.erase (oh : IdStrategyHeap σ (β:=β)) (id : Nat) : IdStrategyHeap σ (β:=β) :=
  {oh with map := oh.map.erase id}

-- Delete the minimal element from heap `n`
private partial def IdStrategyHeap.deleteMinFrom
  (oh : IdStrategyHeap σ (β:=β)) (n : Nat) : Option ((Array Nat × σ) × IdStrategyHeap σ (β:=β)) :=
  let heap := oh.heaps[n]?
  match heap with
  | some heap =>
    let res := heap.deleteMin
    match res with
    | some (σ', heap') =>
      let Q' := {oh with heaps := oh.heaps.set! n heap'}
      let id := σ'.2
      if let some res := oh.map[id]? then
        some (res, Q'.erase id)
      else
        Q'.deleteMinFrom n
    | none => none
  | none =>
    panic!"IdStrategyHeap.deleteMinFrom :: The id of selected heap >= number of heaps"

private def IdStrategyHeap.insert
  (oh : IdStrategyHeap σ (β:=β)) (x : σ) (ns : Array Nat) : IdStrategyHeap σ (β:=β) :=
  let nextId := oh.nextId
  let map' := oh.map.insert nextId (ns, x)
  if ns.size != oh.heaps.size then
    have : Inhabited (IdStrategyHeap σ (β:=β)) := ⟨oh⟩
    panic! "IdStrategyHeap.insert :: Size of heap array is not equal to size of input precedence array"
  else
    let zipped := oh.heaps.zip ns
    let heaps' := zipped.map (fun (heap, prec) => heap.insert (prec, nextId))
    {oh with map := map', heaps := heaps', nextId := nextId + 1}


-- Status of the stream heap
--   The hashmap `nProbed` records the number of times a stream was chosen for probing
-- This is put here because `ProverM` needs it

structure ClauseStreamHeapStatus where
  nProbed : Std.HashMap Nat Nat := Std.HashMap.empty
  fairnessCounter : Nat     := 0

def ClauseStreamHeapStatus.insertNProbed (cshs : ClauseStreamHeapStatus)
  (id : Nat) (nProbed : Nat) := {cshs with nProbed := cshs.nProbed.insert id nProbed}

def ClauseStreamHeapStatus.eraseNProbed (cshs : ClauseStreamHeapStatus)
  (id : Nat) := {cshs with nProbed := cshs.nProbed.erase id}

-- The stream heap, for interleaving between inference and unification
-- The size of `heaps` should be 2. The first heap is the
--   weight heap and the second heap is the age heap.
-- Note that `ClauseStreamHeap` keeps track of each streams' age
--   by itself.
-- `α` is the type of clause
-- `σ` is the type of the clause stream
abbrev ClauseStreamHeap σ := IdStrategyHeap σ (β:=ClauseStreamHeapStatus)

@[inline] def ClauseStreamHeap.increaseFairnessCounter (Q : ClauseStreamHeap σ) :=
  { Q with status := {Q.status with fairnessCounter := Q.status.fairnessCounter + 1}}

abbrev ClauseStreamHeap.empty σ : ClauseStreamHeap σ :=
  { map := Std.HashMap.empty, heaps := #[BinomialHeap.empty, BinomialHeap.empty],
    nextId := 0, status := ⟨Std.HashMap.empty, 0⟩ }

@[inline] def ClauseStreamHeap.insertWithNProbed
  (csh : ClauseStreamHeap σ) (x : σ) (ns : Array Nat) (nProbed : Nat) : ClauseStreamHeap σ :=
  let nextId := csh.nextId
  let map' := csh.map.insert nextId (ns, x)
  if ns.size != csh.heaps.size then
    have : Inhabited (ClauseStreamHeap σ) := ⟨csh⟩
    panic! "ClauseStreamHeap.insertWithNProbed :: Size of heap array is not equal to size of input precedence array"
  else
    let zipped := csh.heaps.zip ns
    let heaps' := zipped.map (fun (heap, prec) => heap.insert (prec, nextId))
    {csh with map := map', heaps := heaps', nextId := nextId + 1,
              status := csh.status.insertNProbed nextId nProbed}

@[inline] def ClauseStreamHeap.eraseWithNProbed (csh : ClauseStreamHeap σ) (id : Nat) :=
  {csh with map := csh.map.erase id, status := csh.status.eraseNProbed id}

-- Delete the minimal element from heap `n`, with "nProbed"
@[inline] partial def ClauseStreamHeap.deleteMinWithNProbed
  (oh : ClauseStreamHeap σ) (n : Nat) : Option ((Nat × Array Nat × σ) × ClauseStreamHeap σ) := Id.run <| do
  if oh.map.size == 0 then
    return none
  if let some heap := oh.heaps[n]? then
    let mut heap := heap
    while true do
      if let some (σ', heap') := heap.deleteMin then
        heap := heap'
        let id := σ'.2
        if let some res := oh.map[id]? then
          let nProbed := oh.status.nProbed[id]!
          let Q' := {oh with heaps := oh.heaps.set! n heap'}
          return some ((nProbed, res), ClauseStreamHeap.eraseWithNProbed Q' id)
        else
          continue
      else
        break
    panic! s!"ClauseStreamHeap.deleteMinWithNProbed :: Map of size {oh.map.size} is not empty, but deletion failed"
  else
    panic! s!"ClauseStreamHeap.deleteMinWithNProbed :: The id of selected heap >= number of heaps"
