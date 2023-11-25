import Mathlib.Topology.MetricSpace.Basic
import Duper.Tactic

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  duper [le_antisymm_iff, le_inf, inf_le_left, inf_le_right]

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    . duper [le_antisymm_iff, le_inf, inf_le_left, inf_le_right, le_trans]
    . duper [le_antisymm_iff, le_inf, inf_le_left, inf_le_right, le_trans]
  . apply le_inf
    . duper [le_antisymm_iff, le_inf, inf_le_left, inf_le_right, le_trans]
    . duper [le_antisymm_iff, le_inf, inf_le_left, inf_le_right, le_trans]

example : x ⊔ y = y ⊔ x := by
  duper [le_antisymm_iff, sup_le, le_sup_left, le_sup_right]

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . apply sup_le
    . duper [le_antisymm_iff, sup_le, le_sup_left, le_sup_right, le_trans]
    . duper [le_antisymm_iff, sup_le, le_sup_left, le_sup_right, le_trans]
  . apply sup_le
    . duper [le_antisymm_iff, sup_le, le_sup_left, le_sup_right, le_trans]
    . duper [le_antisymm_iff, sup_le, le_sup_left, le_sup_right, le_trans]

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb1' : x ⊓ (x ⊔ y) = x := by
  duper [le_antisymm, inf_le_left, le_inf, le_refl, le_sup_left]

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

theorem absorb2' : x ⊔ x ⊓ y = x := by
  duper [le_antisymm, le_sup_left, sup_le, le_refl, inf_le_left]

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a]
  -- If we add the redundant lemma `sup_assoc` to this, it fails.
  duper [h, absorb1, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

-- First, the manual version

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1

-- Now, with duper

example (h : a ≤ b) : 0 ≤ b - a := by
  duper [sub_self, sub_eq_add_neg, add_comm, add_comm, add_le_add_left, h]

example (h : 0 ≤ b - a) : a ≤ b := by
  duper [add_zero, sub_add_cancel, add_comm, add_le_add_left, h]

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  duper [mul_nonneg, aux1, aux2, sub_mul, *]

-- Ambitious:

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  -- try replacing `aux2` with the facts used to prove it
  -- duper [mul_nonneg, aux1, add_zero, sub_add_cancel, add_comm, add_le_add_left, sub_mul, *]
  -- try replacing `aux1` with the facts used to prove it
  -- duper [mul_nonneg, sub_self, sub_eq_add_neg, add_comm, add_comm, add_le_add_left, aux2, sub_mul, *]
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

-- manual proof
example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

example (x y : X) : 0 ≤ dist x y := by
  have : 0 ≤ dist x y + dist y x := by
    duper [dist_self, dist_triangle]
  linarith [dist_comm x y]

end
