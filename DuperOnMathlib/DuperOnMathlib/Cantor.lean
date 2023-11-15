import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import DuperOnMathlib.DuperInterface

open Function

variable {α : Type*}

theorem Cantor : ∀ f : α → Set α, ¬ Surjective f := by
  intro f Surjf
  rcases Surjf {i | i ∉ f i} with ⟨a, h⟩
  have : ¬ a ∉ f a := by
    -- nice
    duper [h, Set.mem_setOf_eq]
  apply this
  rw [h]
  exact this

theorem Cantor2 : ∀ f : α → Set α, ¬ Surjective f := by
  intro f Surjf
  rcases Surjf {i | i ∉ f i} with ⟨a, h⟩
  have : a ∈ f a ↔ a ∉ f a := by
    duper [h, Set.mem_setOf_eq]
  duper [this]

-- Nice!
theorem Cantor3 : ∀ f : α → Set α, ¬ Surjective f := by
  intro f Surjf
  have := Surjf {i | i ∉ f i}
  duper [Set.mem_setOf_eq, this]

namespace original

theorem Cantor : ∀ f : α → Set α, ¬ Surjective f := by
  intro f Surjf
  rcases Surjf {i | i ∉ f i} with ⟨a, h⟩
  have : ¬ a ∉ f a := by
    intro h'
    apply h'
    rw [h]
    exact h'
  apply this
  rw [h]
  exact this

theorem Cantor_alt : ∀ f : α → Set α, ¬ Surjective f := by
  intro f Surjf
  rcases Surjf {i | i ∉ f i} with ⟨a, h⟩
  have : a ∈ f a ↔ a ∉ f a := by
    nth_rewrite 1 [h]; rfl
  tauto

end original
