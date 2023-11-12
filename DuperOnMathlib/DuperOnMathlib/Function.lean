-- import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import DuperOnMathlib.DuperInterface

/-
Taken from Mathematics in Lean. The solutions use definitional equality, so for a first-order
prover we need to add axioms to unfold the definitions.
-/

-- Standard TPTP Configs
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option auto.tptp.solver.name "zipperposition"

-- Standard Native Configs
set_option trace.auto.native.printFormulas true
set_option auto.native.solver.func "Auto.duperPort"

set_option auto.tptp true
set_option auto.native true
-- Print which duper portfolio instance ultimately succeeded
set_option printPortfolioInstance true

section

variable {α β : Type _}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h xs

-- Zipperposition (non-portfolio): 541 iterations and 1.345s
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  duper [subset_def, mem_image, mem_preimage]

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  duper [subset_def, mem_preimage, Injective.mem_set_image, h]

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xmem, rfl⟩
  exact xmem

-- Zipperposition (non-portfolio): 27 iterations in 0.083s
-- TODO: Figure out why auto can solve this with maxHeartbeats 1000000 and kStep 100 but duper can't
set_option maxHeartbeats 1000000 in
set_option kStep 100 in
example : f '' (f ⁻¹' u) ⊆ u := by
  auto [subset_def, mem_image, mem_preimage]

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq

-- Zipperposition (non-portfolio): ResourceOut
example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  duper [subset_def, mem_image, mem_preimage, h]

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, fxeq⟩
  use x, h xs

-- Zipperposition (non-portfolio): 73 iterations in 0.138s
example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  duper [subset_def, mem_image, h]

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x; apply h

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  duper [subset_def, mem_preimage, h]

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := rfl

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; duper [mem_union, mem_preimage]

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  . use x, xs
  . use x, xt

-- Zipperposition (non-portfolio): ResourceOut
example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  duper [mem_inter_iff, subset_def, mem_image]

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩
  use x₁
  constructor
  . use x₁s
    rw [← h fx₂eq]
    exact x₂t
  . rfl

-- Zipperposition (non-portfolio): ResourceOut
example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x; duper [mem_image, mem_diff]

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  fun x ↦ id

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x; duper [mem_preimage, mem_diff]

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

-- Zipperposition (non-portfolio): ResourceOut
example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; duper [mem_inter_iff, mem_image, mem_preimage]

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

-- Zipperposition (non-portfolio): ResourceOut
example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x; duper [mem_inter_iff, mem_image, mem_preimage]

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

-- Zipperposition (non-portfolio): 870 iterations in 1.644s
-- TODO: Figure out why auto can solve this with maxHeartbeats 800000 but Duper can't
set_option maxHeartbeats 800000 in -- Corresponds to 200000 heartbeats if portfolio mode were disabled
example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x; auto [mem_inter_iff, mem_image, mem_preimage]

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    exact ⟨x, xs, rfl⟩
  right; exact fxu

-- Zipperposition (non-portfolio): 387 iterations in 0.638s
-- TODO: Figure out why auto can solve this with maxHeartbeats 800000 but Duper can't
set_option maxHeartbeats 800000 in -- Corresponds to 200000 heartbeats if portfolio mode were disabled
example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x; auto [mem_union, mem_image, mem_preimage]

variable {I : Type _} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp; apply Iff.intro <;> duper

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp; duper

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp; duper [injf, Injective]

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

end

section
variable {α β : Type _} [Inhabited α]

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse]; rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h y ↦ h (inverse_spec _ ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩

-- Encounters a proof reconstruction error when monomorphization is enabled
example : Injective f ↔ LeftInverse (inverse f) f := by
  dsimp [Injective, LeftInverse]
  duper [inverse_spec] {preprocessing := no_preprocessing}

example : Surjective f ↔ RightInverse (inverse f) f :=
  ⟨fun h y ↦ inverse_spec _ (h _), fun h y ↦ ⟨inverse f y, h _⟩⟩

-- Zipperposition (non-portfolio): ResourceOut
example : Surjective f ↔ RightInverse (inverse f) f := by
  dsimp [Surjective, Function.RightInverse, LeftInverse]
  duper [inverse_spec]

end

section
variable {α : Type _}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

theorem Cantor' : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  have s_spec : ∀ i, i ∈ S ↔ i ∉ f i := by intros; rfl
  duper [surjf S, s_spec]

end
