-- This file contains problems from Auto's Examples/Set.lean file and serves to attempt to debug those examples
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Lattice
import Duper.Tactic

open Set

variable {α β : Type _}

section
variable (s t u : Set α)

#check subset_def
#check mem_inter_iff
#check mem_union
#check Set.ext

set_option maxHeartbeats 50000

-- If preprocessing eliminates ⊆ entirely, duper can solve easily
set_option trace.Misc.debug true in
set_option trace.Preprocessing.debug true in
theorem test1a (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]
  rw [subset_def] at h
  duper [mem_inter_iff, subset_def]

-- If duper is forced to use subset_def itself, it times out
theorem test1b (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  duper [mem_inter_iff, subset_def]

-- The above two tests indicate that duper should succeed on this test with auto's preprocessing, which
-- coincides with what we see in Auto's Examples/Set.lean

------------------------------------------------------------------------------------
set_option selFunction 0 in
theorem test2a : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def]

set_option selFunction 1 in
theorem test2b : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def]

set_option selFunction 2 in
theorem test2c : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def]

/-
For this problem, duper fails to solve the example using its default selection function which takes both
inequalities and equalities of the form `e = False` as selectable. However, if duper selects only actual
inequalities, or no literals at all (selection functions 1 and 2 respectively), then duper can solve the
problem
-/
------------------------------------------------------------------------------------
set_option selFunction 0 in
theorem test3a : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def]
  duper [mem_inter_iff, mem_union, subset_def]

set_option selFunction 1 in
theorem test3b : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def]
  duper [mem_inter_iff, mem_union, subset_def]

set_option selFunction 2 in
theorem test3c : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def]
  duper [mem_inter_iff, mem_union, subset_def]

/-
For this problem, duper fails to solve the example using its default selection function which takes both
inequalities and equalities of the form `e = False` as selectable. However, if duper selects only actual
inequalities, or no literals at all (selection functions 1 and 2 respectively), then duper can solve the
problem
-/
------------------------------------------------------------------------------------
#check mem_diff

set_option selFunction 0 in
theorem test4a : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def]
  duper [mem_diff, mem_union, subset_def]

set_option selFunction 1 in
theorem test4b : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def]
  duper [mem_diff, mem_union, subset_def]

set_option selFunction 2 in
theorem test4c : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def]
  duper [mem_diff, mem_union, subset_def]

/-
Duper is able to solve this problem regardless of selection function, but this does NOT coincide with what
we see in Auto's Examples/Set.lean. There, auto seems to not be able to solve this problem
-/
------------------------------------------------------------------------------------
#check Set.ext
-- This is not an example taken from Auto.lean but serves to showcase that Duper can explode if given Set.ext
set_option trace.Timeout.debug true in
set_option trace.Timeout.debug.fullActiveSet true in
theorem test5a : False := by
  duper [Set.ext] -- Duper times out without saturating

set_option includeHoistRules false in
set_option trace.Saturate.debug true in
theorem test5b : False := by
  duper [Set.ext] -- Duper still doesn't saturate even when hoist rules are removed

set_option firstOrderUnifierGenerator true in
set_option trace.Saturate.debug true in
theorem test5c : False := by
  duper [Set.ext] -- Duper saturates reasonably quickly if the first order unifier generator is used

/-
I don't know that any of the above behavior constitutes a bug per se, but it does pose an issue given
that we want Duper to be able to reasonably handle problems that may require lemmas like Set.ext
-/
------------------------------------------------------------------------------------
set_option selFunction 0 in
theorem test6a : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff]

set_option selFunction 1 in
theorem test6b : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff]

set_option selFunction 2 in
theorem test6c : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff]

set_option firstOrderUnifierGenerator true in
theorem test6d : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff]

/-
Duper can't get this no matter how I configure the options, despite it being so simple, but in Duper's
defense, Zipperposition took 6 seconds to get this, so this is maybe just a lot harder than we might think
-/
----------------------------------------------------------------------
set_option selFunction 0 in
theorem test7a : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff]

set_option selFunction 1 in
theorem test7b : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff]

set_option selFunction 2 in
theorem test7c : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff]

set_option firstOrderUnifierGenerator true in
set_option trace.Timeout.debug true in
set_option trace.Timeout.debug.fullActiveSet true in
set_option enableSuperpositionWatchClauses true in
set_option superpositionWatchClause1 13 in
set_option superpositionWatchClause2 32 in
set_option trace.Rule.superposition true in
theorem test7d : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff]

/-
Zipperposition is able to solve this problem quickly, but Duper doesn't seem to be able to solve this
problem under any configuration of options. I'm still in the process of investigating why this is the
case.
-/

-- There are more problems in Auto's Examples/Set.lean file, but I haven't closely examined/moved them here yet

end