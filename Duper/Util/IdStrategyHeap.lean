import Std.Data.BinomialHeap
import Lean

open Lean
open Std

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
  map            : HashMap Nat σ := HashMap.empty
  -- The first `Nat` is the precedence, and the second `Nat` is the `id`
  heaps          : Array (BinomialHeap (Nat × Nat × σ) fun c d => c.1 ≤ d.1) := #[]
  nextId         : Nat
  status         : β
  deriving Inhabited

def IdStrategyHeap.isEmpty (oh : IdStrategyHeap σ (β:=β)) := oh.map.isEmpty

def IdStrategyHeap.size (oh : IdStrategyHeap σ (β:=β)) := oh.map.size

def IdStrategyHeap.contains (oh : IdStrategyHeap σ (β:=β)) (id : Nat) := oh.map.contains id

-- We can only erase `id` from the stream
def IdStrategyHeap.erase (oh : IdStrategyHeap σ (β:=β)) (id : Nat) : IdStrategyHeap σ (β:=β) :=
  {oh with map := oh.map.erase id}

-- !!! Temporarily delete the minimal element from heap `n`
partial def IdStrategyHeap.deleteMinFromHeapN
  (oh : IdStrategyHeap σ (β:=β)) (n : Nat) : Option ((Nat × Nat × σ) × IdStrategyHeap σ (β:=β)) :=
  let heap := oh.heaps[n]?
  match heap with
  | some heap =>
    let res := heap.deleteMin
    match res with
    | some (σ', heap') =>
      let Q' := {oh with heaps := (oh.heaps.swapAt! n heap').snd}
      let id := σ'.2.1
      if oh.map.contains id then
        some (σ', Q'.erase id)
      else
        Q'.deleteMinFromHeapN n
    | none => none
  | none =>
    panic!"IdStrategyHeap.deleteMinFromHeapN :: The id of selected heap >= number of heaps"

def IdStrategyHeap.insert
  (oh : IdStrategyHeap σ (β:=β)) (x : σ) (ns : Array Nat) : IdStrategyHeap σ (β:=β) :=
  let nextId := oh.nextId
  let map' := oh.map.insert nextId x
  if ns.size != oh.heaps.size then
    have : Inhabited (IdStrategyHeap σ (β:=β)) := ⟨oh⟩
    panic! "IdStrategyHeap.insert :: Size of heap array is not equal to size of input precedence array"
  else
    let zipped := oh.heaps.zip ns
    let heaps' := zipped.map (fun (heap, prec) => heap.insert (prec, nextId, x))
    {oh with map := map', heaps := heaps', nextId := nextId + 1}

-- Insert an element to a specific heap in `heaps`
-- This is useful when we pop an element from one heap of `heaps` to examine it
def IdStrategyHeap.insertToHeapN
  (oh : IdStrategyHeap σ (β:=β)) (n : Nat) (elem : Nat × Nat × σ) : IdStrategyHeap σ (β:=β) :=
  let heap := oh.heaps[n]?
  match heap with
  | some heap =>
    let heap' := heap.insert elem
    {oh with heaps := (oh.heaps.swapAt! n heap').snd}
  | none =>
    have : Inhabited (IdStrategyHeap σ (β:=β)) := ⟨oh⟩
    panic!"IdStrategyHeap.insertToHeapN :: The id of selected heap >= number of heaps"



-- Status of the stream heap
--   The hashmap `nProbed` records the number of times a stream was chosen for probing
-- This is put here because `ProverM` needs it

structure ClauseStreamHeapStatus where
  nProbed : HashMap Nat Nat := HashMap.empty
  fairnessCounter : Nat     := 0

-- The stream heap, for interleaving between inference and unification
-- The size of `heaps` should be 2. The first heap is the
--   weight heap and the second heap is the age heap.
-- Note that `ClauseStreamHeap` keeps track of each streams' age
--   by itself.
-- `α` is the type of clause
-- `σ` is the type of the clause stream
abbrev ClauseStreamHeap σ := IdStrategyHeap σ (β:=ClauseStreamHeapStatus)

def ClauseStreamHeap.increaseFairnessCounter (Q : ClauseStreamHeap σ) :=
  { Q with status := {Q.status with fairnessCounter := Q.status.fairnessCounter + 1}}

abbrev ClauseStreamHeap.empty σ : ClauseStreamHeap σ :=
  { map := HashMap.empty, heaps := #[BinomialHeap.empty, BinomialHeap.empty],
    nextId := 0, status := ⟨HashMap.empty, 0⟩ }