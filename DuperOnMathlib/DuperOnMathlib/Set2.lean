/-
Some set theoretic identities. These can all be solved by unfolding definitions
and then using first-order logic.

These are adapted from Mathematics in Lean. The relevant definitions are in the #check commands.
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Lattice
import DuperOnMathlib.DuperInterface

open Set

-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zipperposition"
-- Standard SMT Configs
/-
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"
-/
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
set_option auto.native.solver.func "Auto.duperPort"

set_option auto.tptp true
set_option auto.native true
-- Print which duper portfolio instance ultimately succeeded
set_option printPortfolioInstance true

variable {α β : Type _}

section
variable (s t u : Set α)

#check subset_def
#check mem_inter_iff
#check mem_union
#check Set.ext

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  duper [mem_inter_iff, subset_def, h]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Success
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  duper [mem_inter_iff, mem_union, subset_def] {preprocessing := full}

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Success
set_option trace.Print_Proof true in
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  duper [mem_inter_iff, mem_union, subset_def] {preprocessing := full}

#check mem_diff

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  duper [mem_diff, mem_union, subset_def] {preprocessing := full}

-- zipperposition               : Success (Timeout for non-portfolio mode)
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s ∩ t = t ∩ s := by
  duper [Set.ext, mem_inter_iff]

-- zipperposition               : Success
-- auto (raw duper)             : Succees
-- auto (portfolio duper)       : Success
example : s ∩ t = t ∩ s := by
  apply Set.ext; duper [mem_inter_iff]

-- zipperposition               : Success (205 iterations and 0.196s for non-portfolio mode)
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s ∩ (s ∪ t) = s := by
  duper [Set.ext, mem_union, mem_inter_iff] -- Duper doesn't seem to find this even after a long time

-- zipperposition               : Success
-- auto (raw duper)             : Succees
-- auto (portfolio duper)       : Success
example : s ∩ (s ∪ t) = s := by
  apply Set.ext; duper [mem_union, mem_inter_iff]

-- zipperposition               : Success (1386 iterations 2.3s for non-portfolio mode)
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s ∪ s ∩ t = s := by
  duper [Set.ext, mem_union, mem_inter_iff] -- Duper doesn't seem to find this even after a long time

-- zipperposition               : Success
-- auto (raw duper)             : Succees
-- auto (portfolio duper)       : Success
example : s ∪ s ∩ t = s := by
  apply Set.ext; duper [mem_union, mem_inter_iff]

-- zipperposition               : Timeout
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s \ t ∪ t = s ∪ t := by
  duper [Set.ext, mem_union, mem_diff]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example : s \ t ∪ t = s ∪ t := by
  apply Set.ext; duper [mem_union, mem_diff]

-- zipperposition               : Timeout
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  duper [Set.ext, mem_union, mem_inter_iff, mem_diff]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Success
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Set.ext; duper [mem_union, mem_inter_iff, mem_diff]

#check mem_setOf

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
set_option auto.redMode "all" in
example : evens ∪ odds = univ := by
  duper

#check mem_empty_iff_false
#check mem_univ

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
set_option auto.redMode "all" in
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  duper [*]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
set_option auto.redMode "all" in
example (x : ℕ) : x ∈ (univ : Set ℕ) := by
  duper

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry

end

section
variable (s t : Set ℕ)

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  duper [h₀, h₁]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  duper [h]

section
variable (ssubt : s ⊆ t)

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  duper [h₀, h₁, ssubt, subset_def]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  duper [h, ssubt, subset_def]

end

end

section
variable {α I : Type _}
variable (A B : I → Set α)
variable (s : Set α)

open Set

#check mem_iUnion
#check mem_iInter

-- zipperposition               : Success (Timeout for non-portfolio mode)
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  apply Set.ext; duper [mem_inter_iff, mem_iUnion]

-- zipperposition               : Success (Timeout for non-portfolio mode)
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  apply Set.ext; duper [mem_inter_iff, mem_iInter]

-- zipperposition               : Success (246 iterations and 1.1s for non-portfolio mode)
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout (Success if the correct instance is chosen)
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  apply Set.ext; duper [mem_union, mem_iInter] {portfolioInstance := 2}

def primeset : Set ℕ :=
  { x | Nat.Prime x }

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
-- Note: If monomorphization is enabled, then an error is encountered: "unknown free variable '_uniq.9635399'"
example : (⋃ p ∈ primeset, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primeset, p ^ 2 ∣ x } := by
  apply Set.ext; intro x
  rw [mem_iUnion]; conv => enter [1, 1, i]; rw [mem_iUnion]
  duper [mem_setOf]

#check Nat.exists_prime_and_dvd

example : (⋂ p ∈ primeset, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  sorry

#check Nat.exists_infinite_primes

example : (⋃ p ∈ primeset, { x | x ≤ p }) = univ := by
  sorry

end

section
open Set

variable {α : Type _} (s : Set (Set α))

#check mem_iUnion₂
#check mem_iInter₂

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true

example : ⋃₀ s = ⋃ t ∈ s, t := by
  sorry

example : ⋂₀ s = ⋂ t ∈ s, t := by
  sorry

end
