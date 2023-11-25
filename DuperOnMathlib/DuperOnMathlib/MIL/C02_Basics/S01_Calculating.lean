import Mathlib.Data.Real.Basic
import Duper.Tactic

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  duper [mul_comm, mul_assoc]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  duper [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  duper [mul_comm, mul_assoc]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  duper [mul_comm, mul_assoc]
/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  duper [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  duper [mul_comm, mul_assoc]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  duper [mul_comm, mul_assoc, h, h']

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  duper [mul_comm, mul_assoc, h]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  duper [mul_comm, mul_assoc, hyp, hyp', sub_self]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  duper [mul_assoc, h, h']

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  duper [mul_assoc, h, h']

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  -- duper needs help here
  simp only [mul_add, add_mul]
  -- if we add `add_mul` to the next line, duper times out
  duper [add_assoc, mul_comm, two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  duper [add_mul, mul_add, add_comm, mul_comm, add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  -- simp [add_mul, mul_add, mul_sub, pow_two, mul_comm, ←sub_sub]
  -- simp only [add_mul, mul_add, mul_sub, sub_mul, pow_two, ←sub_sub, mul_comm, add_sub_cancel]
  -- duper [add_mul, mul_add, mul_sub, sub_mul, pow_two, sub_sub, mul_comm, add_sub_cancel]
  simp only [add_mul, mul_add, mul_sub, sub_mul]
  -- trying to move any of the above to duper fails
  duper [pow_two, sub_sub, add_sub_cancel, mul_comm]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  duper [hyp, hyp', mul_comm d a, two_mul, mul_assoc]
/-
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
-/

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  duper [h, add_mul]
