import Mathlib.Data.Real.Basic
import Duper.Tactic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

example (h : a < b) : ¬b < a := by
  duper [lt_trans, lt_irrefl, *]

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
 duper [*, FnHasUb, FnUb, gt_iff_lt, not_le]

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
 duper [*, FnHasLb, FnLb, gt_iff_lt, not_le]

example : ¬FnHasUb fun x ↦ x := by
  have : ∀ x : ℝ, x < x + 1  := by simp
  duper [*, FnHasUb, FnUb, gt_iff_lt, not_le, this]

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)


example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge (h h'')

-- Nice!
example (h : Monotone f) (h' : f a < f b) : a < b := by
  duper [lt_of_not_ge, not_lt_of_ge, Monotone, *]

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h'' h

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  duper [Monotone, not_lt_of_ge, *]

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leab
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
    set f := fun x : ℝ ↦ (0 : ℝ) with hf
    have h' : f 1 ≤ f 0 := le_refl _
    have : ¬ (1 : ℝ ) ≤ 0 := by linarith
    duper [Monotone, *]

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith [h _ h']

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  duper [*, le_of_not_gt, lt_irrefl]

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  duper [h]

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  duper [h]

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  duper [h]

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  duper [h]

example (h : ¬¬Q) : Q := by
  duper [h]

example (h : Q) : ¬¬Q := by
  duper [h]

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  duper [h, le_of_not_gt, FnHasUb, FnUb]

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  duper [FnHasUb, FnUb, h, le_of_not_gt]

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  duper [Monotone, h, le_of_not_gt]


example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  duper [h, lt_irrefl]

end
