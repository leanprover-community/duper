import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Duper.Tactic

open BigOperators
open Finset

example (s : Finset ℝ) : ∑ i in s, (i + 1) = ∑ i in s, i + ∑ i in s, 1 := by
  rw [sum_add_distrib]

example (s : Finset ℝ) : ∑ i in s, (i + 1) = ∑ i in s, i + ∑ i in s, 1 := by
  duper [sum_add_distrib]

example (s : Finset ℝ) : ∑ i in s, (i + 1) = ∑ i in s, i + s.card := by
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]

example (s : Finset ℝ) : ∑ i in s, (i + 1) = ∑ i in s, i + s.card := by
  duper [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]

example (s : Finset ℝ) : ∑ i in s, 2 * i = 2 * ∑ i in s, i := by
  simp only [mul_sum]

example (s : Finset ℝ) : ∑ i in s, 2 * i = 2 * ∑ i in s, i := by
  duper [mul_sum]

example (s : Finset ℝ) : ∑ i in s, (i^2 + 2 * i + 1) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
  simp only [sum_add_distrib]
  rw [←mul_sum]

example (s : Finset ℝ) : ∑ i in s, (i^2 + 2 * i + 1) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
  rw [sum_add_distrib, sum_add_distrib, ←mul_sum]

example (s : Finset ℝ) : ∑ i in s, (i^2 + 2 * i + 1) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
  duper [sum_add_distrib, @mul_sum _ _ s 2 (fun i => i)]

-- fails
-- example (s : Finset ℝ) : ∑ i in s, (i^2 + 2 * i + 1) =
--     ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
--   duper [sum_add_distrib, mul_sum]

-- but this succeeds
example (s : Finset ℝ) : ∑ i in s, (i^2 + 2 * i) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i := by
  duper [sum_add_distrib, mul_sum]

-- fails
-- example (s : Finset ℝ) (n : ℝ) : ∑ i in s, (i^2 + 2 * i + n) =
--     ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, n := by
--   duper [sum_add_distrib, mul_sum]

-- fails
-- example (s : Finset ℝ) (n : ℝ) : ∑ i in s, (n + i^2 + 2 * i) =
--     ∑ i in s, n + ∑ i in s, i^2 + 2 * ∑ i in s, i := by
--   duper [sum_add_distrib, mul_sum]

-- fails
-- example (s : Finset ℝ) (n : ℝ) : ∑ i in s, (i^2 + 2 * n + 1) =
--     ∑ i in s, i^2 + 2 * ∑ i in s, n + ∑ i in s, 1 := by
--   duper [sum_add_distrib, mul_sum]

section
variable {α : Type*} [CommRing α]

example (s : Finset α) : ∑ i in s, (i + 1) = ∑ i in s, i + ∑ i in s, 1 := by
  rw [sum_add_distrib]

example (s : Finset α) : ∑ i in s, (i + 1) = ∑ i in s, i + ∑ i in s, 1 := by
  duper [sum_add_distrib]

example (s : Finset α) : ∑ i in s, (i + 1) = ∑ i in s, i + s.card := by
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]

example (s : Finset α) : ∑ i in s, (i + 1) = ∑ i in s, i + s.card := by
  duper [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]

example (s : Finset α) : ∑ i in s, 2 * i = 2 * ∑ i in s, i := by
  simp only [mul_sum]

example (s : Finset α) : ∑ i in s, 2 * i = 2 * ∑ i in s, i := by
  duper [mul_sum]

example (s : Finset α) : ∑ i in s, (i^2 + 2 * i + 1) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
  simp only [sum_add_distrib]
  rw [←mul_sum]

example (s : Finset α) : ∑ i in s, (i^2 + 2 * i + 1) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
  rw [sum_add_distrib, sum_add_distrib, ←mul_sum]

example (s : Finset α) : ∑ i in s, (i^2 + 2 * i + 1) =
    ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
  duper [sum_add_distrib, @mul_sum _ _ s 2 (fun i => i)]

--fails
-- example (s : Finset α) : ∑ i in s, (i^2 + 2 * i + 1) =
--     ∑ i in s, i^2 + 2 * ∑ i in s, i + ∑ i in s, 1 := by
--   duper [sum_add_distrib, mul_sum]


end
