import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Duper.Tactic

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

-- Duper can simulate ring by throwing everything at it.
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  have : (2 : R) = 1 + 1 := by norm_num
  duper [hyp, hyp', this, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, add_mul, mul_add, one_mul, mul_one]
/-
  rw [hyp, hyp']
  ring
-/

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by duper [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by duper [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  duper [add_assoc, add_left_neg, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  duper [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  duper [h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  duper [h, add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    duper [mul_add, add_zero, add_zero]
  duper [add_left_cancel, h]

-- Wow! This is tricky -- it's great that duper gets it.
theorem mul_zero' (a : R) : a * 0 = 0 := by
  duper [mul_add, add_zero, add_left_cancel]

theorem zero_mul (a : R) : 0 * a = 0 := by
  duper [add_mul, zero_add, add_right_cancel]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  duper [neg_add_cancel_left, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  duper [add_comm, h, neg_eq_of_add_eq_zero]

theorem neg_zero : (-0 : R) = 0 := by
  duper [neg_eq_of_add_eq_zero, add_zero]

theorem neg_neg (a : R) : - -a = a := by
  duper [neg_eq_of_add_eq_zero, add_left_neg]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b := by
  duper [sub_eq_add_neg]

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  duper [sub_eq_add_neg, add_right_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  duper [one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    duper [mul_assoc, mul_left_inv, one_mul, mul_left_inv]
  duper [h, mul_assoc, mul_left_inv, one_mul]

-- Wow! Duper gets it by itself!
theorem mul_right_inv' (a : G) : a * a⁻¹ = 1 := by
  duper [mul_assoc, mul_left_inv, one_mul, mul_left_inv]

-- this is tricky!
theorem mul_one (a : G) : a * 1 = a := by
  duper [mul_left_inv, mul_assoc, mul_right_inv, one_mul]

-- Wow!
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  duper [one_mul, mul_left_inv, mul_assoc, mul_right_inv]

end MyGroup

-- For comparison: the manual proofs

namespace MyGroup'

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← mul_left_inv a, ← mul_assoc, mul_right_inv, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← mul_left_inv (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_right_inv, one_mul, mul_right_inv, mul_one]

end MyGroup'

end

end
