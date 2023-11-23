import Std.Data.BinomialHeap
import Lean

open Lean
open Std

namespace Duper

inductive ClauseSelectionStrategy where
  | Weight
  | Age
  | Generation
  deriving Inhabited

open ClauseSelectionStrategy

initialize
  registerTraceClass `ClauseSelection.debug

/-- `StrategyHeap` models GivenClause Selection. `StrategyHeap` contains 3 internal heaps: a weight heap, a
    generation heap, and an age heap.
    - The weight heap is used to select the "smallest" clause (with ties chosen arbitrarily). Here, "smallest" does
      not exactly refer to KBO size but instaed refers to size with penalties given by various clause selection heuristics.
      The "weight" of each clause, as used by this heap, is calculated in `Clause.selectionPrecedence` in Clause.lean.
    - The generation heap is used to select the clause that has been generated with the fewest inferences
      (with older clauses being preferred over younger as a tiebreaker).
    - The age heap is used to select the oldest clause.

    Only the age heap is required for fairness, but empirically, it is best to usually select the smallest clause,
    and we've also found the generation heap helpful for making sure that Duper considers large facts that can't
    be clausified all at once (for instance, if a clause has a lit `p ↔ q`, then two clauses will be generated via
    clausification and if `p` and `q` are large, it can take a very long time for the second one to be selected). -/
structure StrategyHeap (α : Type u) {β : Type} [BEq α] [Hashable α] where
  set             : HashSet α := HashSet.empty -- Set of elements of `α`
  weightheap      : BinomialHeap (Nat × α) fun c d => c.1 ≤ d.1 := BinomialHeap.empty
  generationheap  : BinomialHeap ((Nat × Nat) × α) fun c d => c.1.1 < d.1.1 || (c.1.1 = d.1.1 && c.1.2 ≤ d.1.2) := BinomialHeap.empty
  ageheap         : BinomialHeap (Nat × α) fun c d => c.1 ≤ d.1 := BinomialHeap.empty
  status          : β
  strategy        : β → ClauseSelectionStrategy × β
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
  (sh : StrategyHeap α (β:=β)) (x : α) (weight generation age : Nat) : StrategyHeap α (β:=β) :=
  {sh with set := sh.set.insert x,
           weightheap := sh.weightheap.insert (weight, x),
           ageheap := sh.ageheap.insert (age, x),
           generationheap := sh.generationheap.insert ((generation, age), x)}

@[inline] def StrategyHeap.erase [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) (x : α) : StrategyHeap α (β:=β) :=
  {sh with set := sh.set.erase x}

@[inline] partial def StrategyHeap.pop? [BEq α] [Hashable α]
  (sh : StrategyHeap α (β:=β)) : Option (α × StrategyHeap α (β:=β)) := Id.run <| do
  match sh.strategy sh.status with
  | (Weight, status') =>
    let mut heap := sh.weightheap
    while true do
      if let some (x, h') := heap.deleteMin then
        let x := x.2
        if sh.set.contains x then
          return (x, {sh with set := sh.set.erase x,
                              weightheap := h',
                              status := status'})
        else
          heap := h'
      else
        break
    return none
  | (Age, status') =>
    let mut heap := sh.ageheap
    while true do
      if let some (x, h') := heap.deleteMin then
        let x := x.2
        if sh.set.contains x then
          return (x, {sh with set := sh.set.erase x,
                              ageheap := h',
                              status := status'})
        else
          heap := h'
      else
        break
    return none
  | (Generation, status') =>
    let mut heap := sh.generationheap
    while true do
      if let some (x, h') := heap.deleteMin then
        let x := x.2
        if sh.set.contains x then
          return (x, {sh with set := sh.set.erase x,
                              generationheap := h',
                              status := status'})
        else
          heap := h'
      else
        break
    return none

/-- A strategy heap that uses a fairnessCounter for its status -/
abbrev FairAgeHeap (α : Type u) [BEq α] [Hashable α]
  := StrategyHeap α (β:=Nat)

abbrev FairAgeHeap.empty (α : Type u) [BEq α] [Hashable α] (fN : Nat) : FairAgeHeap α :=
  /- Choose weight heap most of the time. Choose generation heap when the fairness counter is fN - 1
     and choose the age heap when the fairness counter is fN. When the fairness counter reaches fN, reset
     back to 0. -/
  let strategy :=
    fun fairnessCounter =>
      if fairnessCounter = fN - 1 then (Generation, fN)
      else if fairnessCounter ≥ fN then (Age, 0)
      else (Weight, fairnessCounter + 1)
  { status := 0, strategy := strategy }

-- Test
private def heap₁ := Id.run <| do
  let mut fah := FairAgeHeap.empty Nat 3
  for i in List.range 40 do
    fah := fah.insert i (2 * i) 0 (100 - (i - 20) * (i - 20))
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
