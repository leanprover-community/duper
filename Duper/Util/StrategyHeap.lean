import Std.Data.BinomialHeap
import Lean

open Lean
open Std

namespace Duper

-- `StrategyHeap` models GivenClause Selection
structure StrategyHeap (α : Type u) {β : Type} [BEq α] [Hashable α] where
  set             : HashSet α := HashSet.empty -- Set of elements of `α`
  weightheap      : BinomialHeap (Nat × α) fun c d => c.1 ≤ d.1 := BinomialHeap.empty
  ageheap         : BinomialHeap (Nat × α) fun c d => c.1 ≤ d.1 := BinomialHeap.empty
  status          : β
  strategy        : β → Bool × β
  deriving Inhabited

@[inline] def StrategyHeap.isEmpty [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) := sh.set.isEmpty

@[inline] def StrategyHeap.contains [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) := sh.set.contains x

def StrategyHeap.toArray [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) := sh.set.toArray

def StrategyHeap.toList [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) := sh.set.toList

@[inline] def StrategyHeap.insert [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) (weight age : Nat) : StrategyHeap α (β:=β) :=
  {sh with set := sh.set.insert x,
           ageheap := sh.ageheap.insert (age, x),
           weightheap := sh.weightheap.insert (weight, x)}

@[inline] def StrategyHeap.erase [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) : StrategyHeap α (β:=β) :=
  {sh with set := sh.set.erase x}

@[inline] partial def StrategyHeap.pop? [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) : Option (α × StrategyHeap α (β:=β)) := Id.run <| do
  let (hid, status') := sh.strategy sh.status
  let mut heap := if hid then sh.weightheap else sh.ageheap
  while true do
    if let some (x, h') := heap.deleteMin then
      let x := x.2
      if sh.set.contains x then
        if hid then
          return (x, {sh with set := sh.set.erase x,
                              weightheap := heap,
                              status := status'})
        else
          return (x, {sh with set := sh.set.erase x,
                              ageheap := heap,
                              status := status'})
      else
        heap := h'
    else
      break
  return none

-- The clause heap, for givenClause selection
-- The size of `heaps` should be 2. The first heap is the
--   weight heap and the second heap is the age heap
abbrev FairAgeHeap (α : Type u) [BEq α] [Hashable α]
  := StrategyHeap α (β:=Nat)
  
abbrev FairAgeHeap.empty (α : Type u) [BEq α] [Hashable α] (fN : Nat) : FairAgeHeap α :=
  -- status : fairnessCounter
  -- true   : weight heap
  -- false  : age heap
  { status := 0, strategy := fun b => if b >= fN then (false, 0) else (true, b + 1)}

-- Test
private def heap₁ := Id.run <| do
  let mut fah := FairAgeHeap.empty Nat 3
  for i in List.range 40 do
    fah := fah.insert i (2 * i) (100 - (i - 20) * (i - 20))
  return fah

private def testheap₁ : IO Unit := do
  let mut heap₁ := heap₁
  for _ in List.range 50 do
    if let some (x, h') := heap₁.pop? then
      println! x
      heap₁ := h'
    else
      println! "No"

#eval testheap₁