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
example (f g : Nat → Nat) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  duper [even_fun, add_apply f g]

end Seq
