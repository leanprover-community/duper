import LeanHammer.Tactic




set_option trace.Meta.debug true
set_option trace.Prover.debug true
-- set_option pp.all true

example (h : ∃ x, x ≠ c ∨ a = b) (h : ∀ y, ∃ x, x ≠ a ∧ y ≠ a) (h :  c = b ∧ a = b) : False := by
  prover