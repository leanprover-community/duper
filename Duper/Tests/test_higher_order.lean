import Duper.Tactic
import Duper.TPTP

set_option maxHeartbeats 20000
tptp NUM020_1 "../TPTP-v8.0.0/Problems/NUM/NUM020^1.p"
  by duper

tptp AGT033 "../TPTP-v8.0.0/Problems/AGT/AGT033^1.p" by sorry

set_option trace.Meta.debug true in
tptp ANA047 "../TPTP-v8.0.0/Problems/ANA/ANA047^1.p" by sorry

tptp DAT113 "../TPTP-v8.0.0/Problems/DAT/DAT113^1.p" by sorry

-- Higher order tests
example
  (three six : (Nat → Nat) → Nat → Nat)
  (succ : ((Nat → Nat) → Nat → Nat) → ((Nat → Nat) → Nat → Nat))
  (hsucc_ax: succ = fun N X Y => X (N X Y))
  (plus mult : ((Nat → Nat) → Nat → Nat) → ((Nat → Nat) → Nat → Nat) → ((Nat → Nat) → Nat → Nat))
  (hmult_ax: mult = fun M N X Y => M (N X) Y)
  (hthree_ax: three = fun X Y => X (X (X Y)))
  (hthm: ¬∃ N, mult N three = three) : False := by duper

-- Ex27 is example 27 from https://matryoshka-project.github.io/pubs/hosup_report.pdf
set_option trace.Print_Proof true in
set_option trace.Rule.neHoist true in
set_option trace.ProofReconstruction true in
theorem ex27 (t : Type) (g : Prop → t) (h : t → t) (A B : t)
  (eq1 : A ≠ B)
  (eq2 : ∀ y : t → t, h (y B) ≠ h (g False) ∨ h (y A) ≠ h (g True)) : False :=
  by duper
