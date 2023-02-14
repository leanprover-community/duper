import Std.Data.BinomialHeap
import Lean

open Lean
open Std

namespace Duper

-- `StrategyHeap` models GivenClause Selection

structure StrategyHeap (α : Type u) {β : Type} [BEq α] [Hashable α] where
  -- Set of elements of `α`
  set             : HashSet α := HashSet.empty
  -- The first "Nat" is the priority
  -- The second "Nat" is the id of the clause
  heaps           : Array (BinomialHeap (Nat × α) fun c d => c.1 ≤ d.1) := #[]
  status          : β
  -- The `Nat` in `Nat × β` is intended
  -- to represent the selected heap from the array `heaps`
  strategy        : β → Nat × β
  deriving Inhabited

def StrategyHeap.contains [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) := sh.set.contains x

def StrategyHeap.toArray [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) := sh.set.toArray

def StrategyHeap.toList [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) := sh.set.toList

def StrategyHeap.insert [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) (ns : Array Nat) : StrategyHeap α (β:=β) :=
  let set' := sh.set.insert x
  if ns.size != sh.heaps.size then
    have : Inhabited (StrategyHeap α) := ⟨sh⟩
    panic!"StrategyHeap.insert :: Size of heap array is not equal to size of input precedence array"
  else
    let zipped := sh.heaps.zip ns
    let heaps' := zipped.map (fun (heap, prec) => heap.insert (prec, x))
    {sh with set := set', heaps := heaps'}

def StrategyHeap.erase [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) : StrategyHeap α (β:=β) :=
  {sh with set := sh.set.erase x}

partial def StrategyHeap.pop? [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) : Option (α × StrategyHeap α (β:=β)) :=
  let (hid, status') := sh.strategy sh.status
  if hid >= sh.heaps.size then
    have : Inhabited (StrategyHeap α) := ⟨sh⟩
    panic!"The id of selected heap >= number of heaps"
  else
    if let some (x, h') := go hid sh.heaps[hid]! sh.set then
      (x, {sh with set := sh.set.erase x,
                   heaps := (sh.heaps.swapAt! hid h').2,
                   status := status'})
    else
      none
  where go id heap set :=
    if let some (x, h') := heap.deleteMin then
      if set.contains x.2 then
        some (x.2, h')
      else
        go id h' set
    else
      none

-- The clause heap, for givenClause selection
-- The size of `heaps` should be 2. The first heap is the
--   weight heap and the second heap is the age heap
abbrev FairAgeHeap (α : Type u) [BEq α] [Hashable α]
  := StrategyHeap α (β:=Nat)
  
abbrev FairAgeHeap.empty (α : Type u) [BEq α] [Hashable α] (fN : Nat) : FairAgeHeap α :=
  -- status : fairnessCounter
  -- heap 0 : weight heap
  -- heap 1 : age heap
  { status := 0, heaps := #[BinomialHeap.empty, BinomialHeap.empty],
    strategy := fun b => if b == fN - 1 then (1, 0) else (0, b + 1)}



-- Test
private def heap₁ := Id.run <| do
  let mut fah := FairAgeHeap.empty Nat 3
  for i in List.range 40 do
    fah := fah.insert i #[2 * i, 100 - (i - 20) * (i - 20)]
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