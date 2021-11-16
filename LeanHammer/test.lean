import LeanHammer.Tactic

set_option trace.Meta.debug true
set_option trace.Prover.debug true
-- set_option pp.all true

constant a : Nat
constant b : Nat

example --(h : ∃ x, x ≠ c ∨ a = b) 
(h : ¬ ∃ x, x = a ∨ ∀ x, ∃ y, y = a ∧ x = b)-- (h :  c = b ∧ a = b) 
: False := by
  prover


example (h : ∀ y x, x ≠ a ∨ y ≠ b)
: False := by
  prover