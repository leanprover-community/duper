import Duper.Tactic

namespace Seq

instance : Neg Nat := sorry

def even_fun (f : Nat → Nat) := ∀ x, f (-x) = f x

instance : Add (Nat → Nat) := (⟨fun f g x => f x + g x⟩ :  Add (Nat → Nat))

theorem add_apply (f g : Nat → Nat) (x : Nat) : (f + g) x = f x + g x := sorry

example (f g : Nat → Nat) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  unfold even_fun at *
  duper [add_apply f g]

-- This should be fairly easy, too, by unfolding even_fun as above.
-- example (f g : Nat → Nat) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
--   duper [even_fun, add_apply f g]

example (f g : Nat → Nat) (hf : ∀ x, f (-x) = f x) : even_fun f := by
  unfold even_fun at *
  exact hf

-- This should be very easy
example (f g : Nat → Nat) (hf : ∀ x, f (-x) = f x) : even_fun f := by
  duper [even_fun]

example (mq : Nat) (ef : (Nat → Nat) → Prop)
        (f : Nat → Nat)
        (h₁ : ∀ a, f a = f (-a))
        (h₂ : ∀ (a : Nat → Nat), ef a = True ∨ a (-mq) ≠ a mq)
        (h₃ : ef f = False) : False := by duper

example (mq : (Nat → Nat) → Nat) (ef : (Nat → Nat) → Prop)
        (n : Nat → Nat)
        (f : Nat → Nat)
        (h₁ : ∀ a, f a = f (- a))
        (h₂ : ∀ (a : Nat → Nat), ef a = True ∨ a (- (mq a)) ≠ a (mq a))
        (h₃ : ef f = False) : False := by duper

example (mq : (Nat → Nat) → Nat) (ef : (Nat → Nat) → Prop)
        (n : Nat → Nat)
        (f : Nat → Nat)
        (h₁ : ∀ a, f a = f (n a))
        (h₂ : ∀ (a : Nat → Nat), ef a = True ∨ a (n (mq a)) ≠ a (mq a))
        (h₃ : ef f = False) : False := by duper


end Seq
