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

-- `StreamHeap` models operations on inference streams
-- `m` : The monad which we operate in
-- `σ` : The type of the stream
-- `α` : Type of elements in the stream
-- We can't expect the monadic stream to be hashable, so we give
--   each stream a `id`.
structure StreamHeap (σ : Type w) (α : Type u) {β : Type v} where
  -- Map of `id` to clause heap
  map            : HashMap Nat σ := HashMap.empty
  -- The first `Nat` is the precedence, and the second `Nat` is the `id`
  heaps          : Array (BinomialHeap (Nat × Nat × σ) fun c d => c.1 ≤ d.1) := #[]
  nextId         : Nat
  status         : β
  deriving Inhabited

def StreamHeap.isEmpty (oh : StreamHeap σ α (β:=β)) := oh.map.isEmpty

def StreamHeap.size (oh : StreamHeap σ α (β:=β)) := oh.map.size

def StreamHeap.contains (oh : StreamHeap σ α (β:=β)) (id : Nat) := oh.map.contains id

-- We can only erase `id` from the stream
def StreamHeap.erase (oh : StreamHeap σ α (β:=β)) (id : Nat) : StreamHeap σ α (β:=β) :=
  {oh with map := oh.map.erase id}

-- !!! Temporarily delete the minimal element from heap `n`
partial def StreamHeap.deleteMinFromHeapN
  (oh : StreamHeap σ α (β:=β)) (n : Nat) : Option ((Nat × Nat × σ) × StreamHeap σ α (β:=β)) :=
  let heap := oh.heaps[n]?
  match heap with
  | some heap =>
    let res := heap.deleteMin
    match res with
    | some (σ', heap') =>
      let Q' := {oh with heaps := (oh.heaps.swapAt! n heap').snd}
      let id := σ'.2.1
      if oh.map.contains id then
        Q'.deleteMinFromHeapN n
      else
        some (σ', Q'.erase id)
    | none => none
  | none =>
    panic!"StreamHeap.deleteMinFromHeapN :: The id of selected heap >= number of heaps"

def StreamHeap.insert
  (oh : StreamHeap σ α (β:=β)) (x : σ) (ns : Array Nat) : StreamHeap σ α (β:=β) :=
  let nextId := oh.nextId
  let map' := oh.map.insert nextId x
  if ns.size != oh.heaps.size then
    have : Inhabited (StreamHeap σ α (β:=β)) := ⟨oh⟩
    panic! "StreamHeap.insert :: Size of heap array is not equal to size of input precedence array"
  else
    let zipped := oh.heaps.zip ns
    let heaps' := zipped.map (fun (heap, prec) => heap.insert (prec, nextId, x))
    {oh with map := map', heaps := heaps', nextId := nextId + 1}

-- Insert an element to a specific heap in `heaps`
-- This is useful when we pop an element from one heap of `heaps` to examine it
def StreamHeap.insertToHeapN
  (oh : StreamHeap σ α (β:=β)) (n : Nat) (elem : Nat × Nat × σ) : StreamHeap σ α (β:=β) :=
  let heap := oh.heaps[n]?
  match heap with
  | some heap =>
    let heap' := heap.insert elem
    {oh with heaps := (oh.heaps.swapAt! n heap').snd}
  | none =>
    have : Inhabited (StreamHeap σ α (β:=β)) := ⟨oh⟩
    panic!"StreamHeap.insertToHeapN :: The id of selected heap >= number of heaps"