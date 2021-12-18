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
  all_goals
    sorry


example (h : ∀ (x y : Nat), y ≠ x)
: False := by
  prover
  all_goals
    sorry

theorem eq_True : h = True ↔ h := by
  apply Iff.intro 
  · intro hh
    rw [hh]
    exact True.intro
  · intro hh
    apply propext
    apply Iff.intro
    exact fun _ => True.intro
    exact fun _ => hh

example  (h : a ≠ b)  (h : a = b)
: False := by
  prover
  · exact (fun h => h rfl)
  · intro h
    rw [h]
    exact (fun g => g)
  · exact eq_True.1
  · exact eq_True.2 (by assumption)
  · exact eq_True.1
  · exact eq_True.2 (by assumption)
