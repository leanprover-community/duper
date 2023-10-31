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

-- If duper is forced to use subset_def itself, it times out
theorem test1_no_rewrite (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  sorry -- duper [mem_inter_iff, subset_def]

set_option selFunction 0 in
theorem test1a (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 0

set_option selFunction 1 in
theorem test1b (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 1

set_option selFunction 2 in
theorem test1c (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 2

set_option selFunction 3 in
theorem test1d (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 3

set_option selFunction 4 in
theorem test1e (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 4

set_option selFunction 5 in
theorem test1f (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 5

set_option selFunction 6 in
theorem test1g (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 6

set_option selFunction 7 in
theorem test1h (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 7

set_option selFunction 8 in
theorem test1i (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 8

set_option selFunction 9 in
theorem test1j (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  rw [subset_def] at h -- Mimics auto's definition aware preprocessing
  duper [h, mem_inter_iff, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 9

------------------------------------------------------------------------------------
set_option selFunction 0 in
theorem test2a : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Det timeout with selFunction 0

set_option selFunction 1 in
theorem test2b : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 1

set_option selFunction 2 in
theorem test2c : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 2

set_option selFunction 3 in
theorem test2d : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 3

set_option selFunction 4 in
theorem test2e : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 4

set_option selFunction 5 in
theorem test2f : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Det timeout with selFunction 5

set_option selFunction 6 in
theorem test2g : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 6

set_option selFunction 7 in
theorem test2h : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 7

set_option selFunction 8 in
theorem test2i : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 8

set_option selFunction 9 in
theorem test2j : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 9

------------------------------------------------------------------------------------
set_option selFunction 0 in
theorem test3a : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Det timeout with selFunction 0

set_option selFunction 1 in
theorem test3b : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 1

set_option selFunction 2 in
theorem test3c : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 2

set_option selFunction 3 in
theorem test3d : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 3

set_option selFunction 4 in
theorem test3e : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 4

set_option selFunction 5 in
theorem test3f : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 5

set_option selFunction 6 in
theorem test3g : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 6

set_option selFunction 7 in
theorem test3h : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 7

set_option selFunction 8 in
theorem test3i : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 8

set_option selFunction 9 in
theorem test3j : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_inter_iff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 9
------------------------------------------------------------------------------------
#check mem_diff

set_option selFunction 0 in
theorem test4a : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 0

set_option selFunction 1 in
theorem test4b : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 1

set_option selFunction 2 in
theorem test4c : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 2

set_option selFunction 3 in
theorem test4d : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 3

set_option selFunction 4 in
theorem test4e : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 4

set_option selFunction 5 in
theorem test4f : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 5

set_option selFunction 6 in
theorem test4g : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 6

set_option selFunction 7 in
theorem test4h : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 7

set_option selFunction 8 in
theorem test4i : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 8

set_option selFunction 9 in
theorem test4j : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rw [subset_def] -- Mimics auto's definition aware preprocessing
  duper [mem_diff, mem_union, subset_def] {portfolioInstance := 0} -- Succeeds with selFunction 9
------------------------------------------------------------------------------------
#check Set.ext

-- Note for this problem: Zipperposition (on default settings) took 6s to solve this

set_option selFunction 0 in
theorem test6a : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 0

set_option selFunction 1 in
theorem test6b : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 1

set_option selFunction 2 in
theorem test6c : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 2

set_option selFunction 3 in
theorem test6d : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 3

set_option selFunction 4 in
theorem test6e : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 4

set_option selFunction 5 in
theorem test6f : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 5

set_option selFunction 6 in
theorem test6g : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 6

set_option selFunction 7 in
theorem test6h : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 7

set_option selFunction 8 in
theorem test6i : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 8

set_option selFunction 9 in
theorem test6j : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 9
----------------------------------------------------------------------
-- Note for this problem: Zipperposition (on default settings) is able to solve this quite quickly,
-- so it should be much more obtainable than test6

set_option selFunction 0 in
theorem test7a : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 0

set_option selFunction 1 in
theorem test7b : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 1

set_option selFunction 2 in
theorem test7c : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 2

set_option selFunction 3 in
theorem test7d : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 3

theorem test7e : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 4

set_option selFunction 5 in
theorem test7f : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 5

set_option selFunction 6 in
theorem test7g : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 6

set_option selFunction 7 in
theorem test7h : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 7

set_option selFunction 8 in
theorem test7i : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 8

set_option selFunction 9 in
theorem test7j : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] {portfolioInstance := 0} -- Det timeout with selFunction 9

end
