import Duper.TPTP
import Duper.Tactic


-- set_option maxHeartbeats 20000 in
-- tptp COM035_5 "../TPTP-v8.0.0/Problems/COM/COM025_5.p"
--   by duper

-- tptp SYN007 "../TPTP-v8.0.0/Problems/SYN/SYN007+1.014.p"
--   by duper

set_option trace.Prover.debug true in
tptp SYN072 "../TPTP-v8.0.0/Problems/SYN/SYN072+1.p"
  by duper
-- Prover saturated

-- Previously: Type mismatch caused by incorrect manipulation of
-- universe levels in `ArgCong`
example : ((∀ (A : Type) (f : Nat → A) (x : Nat), f x = f x) = True) := by duper

universe u
theorem test : Nonempty PUnit.{u} := inferInstance