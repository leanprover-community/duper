import Mathlib.Data.Real.Basic
import Duper.Tactic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- Nice!
example : min a b = min b a := by
  duper [le_antisymm, le_min, min_le_left, min_le_right]
/-
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
-/

example : max a b = max b a := by
  duper [le_antisymm, max_le, le_max_left, le_max_right]

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right

example : min (min a b) c = min a (min b c) := by
  have h1 := @le_min ℝ _
  have h2 := @min_le_left ℝ _
  have h3 := @min_le_right ℝ _
  have h4 := @le_trans ℝ _
  have h5 := @le_refl ℝ _
  apply le_antisymm
  . -- duper [le_trans, le_min, min_le_left, min_le_right, le_refl]
    sorry
  . -- duper [le_trans, le_min, min_le_left, min_le_right, le_refl]
    sorry

example : min (min a b) c = min a (min b c) := by
  have h1 := @le_min ℝ _
  have h2 := @min_le_left ℝ _
  have h3 := @min_le_right ℝ _
  have h4 := @le_trans ℝ _
  apply le_antisymm
  . -- duper [le_trans, le_min, min_le_left, min_le_right, le_refl]
    sorry
  . -- duper [le_trans, le_min, min_le_left, min_le_right, le_refl]
    sorry

/-
Because these next two work, I suspect that Duper is just running out of time on the longer one.
How do I give it more time?
-/
example : min (min a b) c = min a (min b c) := by
  have h1 := @le_min ℝ _
  have h2 := @min_le_left ℝ _
  have h3 := @min_le_right ℝ _
  have h4 := @le_trans ℝ _
  apply le_antisymm
  · apply le_min
    · duper [*]
    duper [*]
  apply le_min
  · duper [*]
  duper [*]

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · duper [le_min, min_le_left, min_le_right, le_trans]
    duper [le_min, min_le_left, min_le_right, le_trans]
  apply le_min
  · duper [le_min, min_le_left, min_le_right, le_trans]
  duper [le_min, min_le_left, min_le_right, le_trans]

-- this doesn't help.
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · duper [le_min, min_le_left, min_le_right, le_trans] {portfolioInstance := 1}
    duper [le_min, min_le_left, min_le_right, le_trans] {portfolioInstance := 1}
  apply le_min
  · duper [le_min, min_le_left, min_le_right, le_trans] {portfolioInstance := 1}
  duper [le_min, min_le_left, min_le_right, le_trans] {portfolioInstance := 1}

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  duper [le_min, add_le_add_right, min_le_left, min_le_right]

-- The manual version.
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

-- Wow!
example : min a b + c = min (a + c) (b + c) := by
  duper [le_antisymm, add_neg_cancel_right, le_refl, le_trans, aux, sub_eq_add_neg, add_le_add_right]

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

-- The manual version
example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel]

-- Wow!
example : |a| - |b| ≤ |a - b| := by
  duper [sub_add_cancel, sub_le_sub_right, abs_add, add_sub_cancel]

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z := by
  duper [dvd_trans, *]

example : x ∣ y * x * z := by
  duper [dvd_mul_of_dvd_left, dvd_mul_left]

example : x ∣ x ^ 2 := by
  duper [pow_two, dvd_mul_left]
   --apply dvd_mul_left

/-
Duper struggles a bit with this one.
-/

-- The manual version
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h1 := @dvd_add ℕ _
  have h2 := @dvd_mul_of_dvd_right ℕ _
  have h3 := @dvd_mul_left ℕ _
  have h4 := @dvd_mul_right ℕ _
  simp only [pow_two]
  -- duper [h1, h2, h3, h4, h]  -- doesn't work
  apply h1
  duper [h1, h2, h3, h4]
  duper [h2, h]

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  simp only [pow_two]
  -- duper [h1, h2, h3, h4, h]  -- doesn't work
  apply dvd_add
  -- Interestingly, if you add `h` to the next line, it fails.
  -- Also, the instantiation of `dvd_add` is needed.
  -- Also, if you delete the `simp only` above, it also fails.
  duper [pow_two, @dvd_add ℕ _, dvd_mul_of_dvd_right, dvd_mul_left, dvd_mul_right]
  duper [dvd_mul_of_dvd_right, h]

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

-- Nice!
example : Nat.gcd m n = Nat.gcd n m := by
  duper [Nat.dvd_antisymm, Nat.dvd_gcd, Nat.gcd_dvd_left, Nat.gcd_dvd_right]

end
