import Duper.TPTP
import Duper.Tactic


set_option maxHeartbeats 20000
tptp COM035_5 "../TPTP-v8.0.0/Problems/COM/COM025_5.p"
  by duper


-- Previously: Type mismatch caused by incorrect manipulation of
-- universe levels in `ArgCong`

set_option trace.Meta.debug true in
example : ((∀ (A : Type) (f : Nat → A) (x : Nat), f x = f x) = True) := by duper
