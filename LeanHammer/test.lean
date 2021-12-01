import LeanHammer.Tactic

set_option trace.Meta.debug true
set_option trace.Prover.debug true
set_option trace.Rule.debug true
-- set_option pp.all true

constant a : Nat
constant b : Nat
constant f : Nat → Nat

example --(h : ∃ x, x ≠ c ∨ a = b) 
(h : ¬ ∃ x, x = f a ∨ ∀ x, ∃ y, y = f a ∧ x = b)-- (h :  c = b ∧ a = b) 
: False := by
  prover


example (h : ∀ y x, x ≠ a ∨ y ≠ b)
: False := by
  prover


example  (h : a ≠ b)  (h : a = b)
: False := by
  prover