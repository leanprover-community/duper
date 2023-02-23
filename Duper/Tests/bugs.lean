import Duper.TPTP
import Duper.Tactic


set_option maxHeartbeats 20000 in
tptp COM035_5 "../TPTP-v8.0.0/Problems/COM/COM025_5.p"
  by duper

set_option maxSaturationTime 5 in
tptp SYN007 "../TPTP-v8.0.0/Problems/SYN/SYN007+1.014.p"
  by duper

-- Previously: Type mismatch caused by incorrect manipulation of
-- universe levels in `ArgCong`

example : ((∀ (A : Type) (f : Nat → A) (x : Nat), f x = f x) = True) := by duper

universe u
theorem test : Nonempty PUnit.{u} := inferInstance