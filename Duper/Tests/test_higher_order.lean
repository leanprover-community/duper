import Duper.Tactic
import Duper.TPTP

set_option maxHeartbeats 20000
tptp NUM020_1 "../TPTP-v8.0.0/Problems/NUM/NUM020^1.p"
  by duper

tptp AGT033 "../TPTP-v8.0.0/Problems/AGT/AGT033^1.p" by sorry

-- Higher order tests
example
  (three six : (Nat → Nat) → Nat → Nat)
  (succ : ((Nat → Nat) → Nat → Nat) → ((Nat → Nat) → Nat → Nat))
  (hsucc_ax: succ = fun N X Y => X (N X Y))
  (plus mult : ((Nat → Nat) → Nat → Nat) → ((Nat → Nat) → Nat → Nat) → ((Nat → Nat) → Nat → Nat))
  (hmult_ax: mult = fun M N X Y => M (N X) Y)
  (hthree_ax: three = fun X Y => X (X (X Y)))
  (hthm: ¬∃ N, mult N three = three) : False := by duper