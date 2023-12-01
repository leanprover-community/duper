
import Mathlib.Data.Real.Basic
import Duper.Tactic

set_option autoImplicit true

namespace C03S02

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num


def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) := by
  simp only [FnUb] at *
  duper [FnUb, add_le_add, *]

section

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  duper [*, FnHasUb, FnUb, add_le_add]


example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  duper [*, FnHasLb, FnLb, add_le_add]

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, lbfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (lbfa x) h

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  duper [*, FnHasUb, FnUb, mul_le_mul_of_nonneg_left]

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  duper [*, FnHasUb, fnUb_add]

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  duper [*, FnHasUb, fnUb_add]

end

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  duper [*, FnHasUb, fnUb_add]


section

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

end

section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  duper [dvd_def, mul_assoc, *]

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  duper [dvd_def, mul_add, *]

end

section

open Function

example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring

example {c : ℝ} : Surjective fun x ↦ x + c := by
  duper [Surjective, sub_add_cancel]

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  duper [Surjective, div_mul_cancel, mul_comm, *]

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  have : (2 : ℝ)^2 = 4 := by norm_num
  duper [*, Surjective]

end

section
open Function
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  duper [Surjective, *]

end
