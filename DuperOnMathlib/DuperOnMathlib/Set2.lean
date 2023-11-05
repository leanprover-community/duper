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
set_option auto.tptp.solver.name "zeport"
set_option auto.tptp.zeport.path "/home/indprinciple/Programs/zipperposition/portfolio/portfolio.fo.parallel.py"
-- Standard SMT Configs
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option auto.smt.solver.name "z3"
-- Standard Native Configs
set_option trace.auto.native.printFormulas true
set_option auto.native.solver.func "Auto.duperRaw"

set_option auto.tptp true
set_option auto.native true

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
  auto [mem_inter_iff, subset_def, h]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
set_option auto.native false in
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  auto [mem_inter_iff, mem_union, subset_def]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
set_option auto.native false in
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  auto [mem_inter_iff, mem_union, subset_def]

#check mem_diff

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  auto [mem_diff, mem_union, subset_def]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
set_option auto.native false in
example : s ∩ t = t ∩ s := by
  auto [Set.ext, mem_inter_iff]

-- zipperposition               : Success
-- auto (raw duper)             : Succees
-- auto (portfolio duper)       : Success
example : s ∩ t = t ∩ s := by
  apply Set.ext; auto [mem_inter_iff]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
set_option auto.native false in
example : s ∩ (s ∪ t) = s := by
  auto [Set.ext, mem_union, mem_inter_iff]

-- zipperposition               : Success
-- auto (raw duper)             : Succees
-- auto (portfolio duper)       : Success
example : s ∩ (s ∪ t) = s := by
  apply Set.ext; auto [mem_union, mem_inter_iff]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
set_option auto.native false in
example : s ∪ s ∩ t = s := by
  auto [Set.ext, mem_union, mem_inter_iff]

-- zipperposition               : Success
-- auto (raw duper)             : Succees
-- auto (portfolio duper)       : Success
example : s ∪ s ∩ t = s := by
  apply Set.ext; auto [mem_union, mem_inter_iff]

-- zipperposition               : Timeout
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s \ t ∪ t = s ∪ t := by
  auto [Set.ext, mem_union, mem_diff]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example : s \ t ∪ t = s ∪ t := by
  apply Set.ext; auto [mem_union, mem_diff]

-- zipperposition               : Timeout
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  auto [Set.ext, mem_union, mem_inter_iff, mem_diff]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
set_option auto.native false in
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Set.ext; auto [mem_union, mem_inter_iff, mem_diff]

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
  auto

#check mem_empty_iff_false
#check mem_univ

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
set_option auto.redMode "all" in
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  auto

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
set_option auto.redMode "all" in
example (x : ℕ) : x ∈ (univ : Set ℕ) := by
  auto

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry

end

section
variable (s t : Set ℕ)

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  auto [h₀, h₁]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  auto [h]

section
variable (ssubt : s ⊆ t)

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  auto [h₀, h₁, ssubt, subset_def]

-- zipperposition               : Success
-- auto (raw duper)             : Success
-- auto (portfolio duper)       : Success
example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  auto [h, ssubt, subset_def]

end

end

section
variable {α I : Type _}
variable (A B : I → Set α)
variable (s : Set α)

open Set

#check mem_iUnion
#check mem_iInter

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  apply Set.ext; auto [mem_inter_iff, mem_iUnion]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  apply Set.ext; auto [mem_inter_iff, mem_iInter]

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  apply Set.ext; auto [mem_union, mem_iInter]

def primeset : Set ℕ :=
  { x | Nat.Prime x }

-- zipperposition               : Success
-- auto (raw duper)             : Timeout
-- auto (portfolio duper)       : Timeout
example : (⋃ p ∈ primeset, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primeset, p ^ 2 ∣ x } := by
  apply Set.ext; intro x
  rw [mem_iUnion]; conv => enter [1, 1, i]; rw [mem_iUnion]
  auto [mem_setOf]

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
