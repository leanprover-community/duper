import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Duper.Tactic

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  duper [le_trans, *]

example (x : ℝ) : x ≤ x := by
  duper [le_refl]

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Nice!
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  duper [*, le_refl, le_trans, lt_of_le_of_lt, lt_of_lt_of_le, lt_trans]

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

example (h : a ≤ b) : exp a ≤ exp b := by
  duper [*, exp_le_exp]

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  duper [*, add_lt_add_of_lt_of_le, add_lt_add_of_le_of_lt, exp_lt_exp, le_refl]
/-
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
-/

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  duper [add_le_add_iff_left, exp_le_exp, *]
/-  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]
-/

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by duper [exp_pos, lt_add_iff_pos_right, zero_lt_one, lt_trans]
  have h₁ : 0 < 1 + exp b := by duper [exp_pos, lt_add_iff_pos_right, zero_lt_one, lt_trans]
  duper [log_le_log, add_le_add_left, exp_le_exp, *]

-- Ambitious:
-- example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
--   duper [exp_pos, lt_add_iff_pos_right, zero_lt_one, lt_trans, log_le_log, add_le_add_left, exp_le_exp, *]

/-
The book solution:
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  have h₁ : 0 < 1 + exp b := by linarith [exp_pos b]
  apply (log_le_log h₀ h₁).mpr
  apply add_le_add_left (exp_le_exp.mpr h)
-/


example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  duper [sub_le_sub_left, exp_le_exp, *]

-- hard for duper
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) :=
      add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff h]
    apply fact1
  rw [le_div_iff h]
  apply fact2

-- Here duper needs the arguments to `abs_le'`, but the `have` also struggles to find an instance
-- without the second argument
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  have := abs_le' (a := a * b) (b := (a ^ 2 + b ^ 2) / 2)
  duper [this, le_div_iff, h, fact1, fact2]

#check abs_le'.mpr
