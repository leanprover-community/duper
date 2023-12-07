import Mathlib.Data.Real.Basic
import Duper.Tactic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  duper [pow_two_nonneg, h, lt_of_le_of_lt]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 := by
  duper [h]

example (h : y < -1) : y > 0 ∨ y < -1 := by
  duper [h]

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  duper [le_or_gt, abs_of_nonneg, abs_of_neg]

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  . rw [abs_of_neg h]
    linarith

example (x : ℝ) : x ≤ |x| := by
  duper [le_or_gt, abs_of_nonneg, abs_of_neg, lt_trans, neg_lt_neg_iff, neg_zero, le_refl, le_of_lt]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  . rw [abs_of_neg h]

example (x : ℝ) : -x ≤ |x| := by
  duper [le_or_gt, abs_of_nonneg, abs_of_neg, le_trans, neg_le_neg_iff, neg_zero, le_refl]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  . rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · duper [abs_of_nonneg h, le_abs_self, add_le_add, le_trans]
  . duper [abs_of_neg h, neg_le_abs_self, add_le_add, neg_add]

-- Too much for duper.
-- example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
--   duper [le_or_gt 0 (x + y), abs_of_nonneg, le_abs_self, neg_le_abs_self, le_trans, abs_of_neg, add_le_add, neg_add]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left
      exact h'
    . intro h'
      rcases h' with h' | h'
      · exact h'
      . linarith
  rw [abs_of_neg h]
  constructor
  · intro h'
    right
    exact h'
  . intro h'
    rcases h' with h' | h'
    · linarith
    . exact h'

example : x < |y| ↔ x < y ∨ x < -y := by
  have : ∀ y : ℝ, y < 0 → y < -y := by intros; linarith
  have : ∀ y : ℝ, 0 ≤ y → -y ≤ y := by intros; linarith
  duper [*, le_or_gt 0 y, abs_of_neg, abs_of_nonneg, lt_trans, lt_of_lt_of_le]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      exact h'
    . intro h'
      rcases h' with ⟨-, h2⟩
      exact h2
  . rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      . linarith
    . intro h'
      linarith

example : |x| < y ↔ -y < x ∧ x < y := by
  have : ∀ y : ℝ, y < 0 → y < -y := by intros; linarith
  have : ∀ y : ℝ, 0 ≤ y → -y ≤ y := by intros; linarith
  duper [*, le_or_gt 0 x, abs_of_neg, abs_of_nonneg, lt_trans, lt_of_lt_of_le, lt_of_le_of_lt, neg_lt, neg_neg]

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  duper [lt_trichotomy, h]

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  duper [mul_assoc, mul_comm, dvd_mul_right, h, dvd_def]

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  duper [sq_nonneg, h, add_le_add, le_trans, zero_le_one, zero_add]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  . left
    exact eq_of_sub_eq_zero h1

-- Nice!
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = (x + 1) * (x - 1) := by ring
  duper [h, h', sub_self, eq_zero_or_eq_zero_of_mul_eq_zero, eq_neg_iff_add_eq_zero, eq_of_sub_eq_zero]

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  . left
    exact eq_of_sub_eq_zero h1

-- Nice!
example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
  duper [h, h', sub_self, eq_zero_or_eq_zero_of_mul_eq_zero, eq_neg_iff_add_eq_zero, eq_of_sub_eq_zero]

example (P : Prop) : ¬¬P → P := by
  duper

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  duper
