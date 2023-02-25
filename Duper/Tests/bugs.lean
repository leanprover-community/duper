import Duper.TPTP
import Duper.Tactic


-- set_option maxHeartbeats 20000 in
-- tptp COM035_5 "../TPTP-v8.0.0/Problems/COM/COM025_5.p"
--   by duper

tptp SEU139 "../TPTP-v8.0.0/Problems/SEU/SEU139+1.p"
  by duper
-- error when reconstructing clausification

-- Previously: Type mismatch caused by incorrect manipulation of
-- universe levels in `ArgCong`
example : ((∀ (A : Type) (f : Nat → A) (x : Nat), f x = f x) = True) := by duper

universe u
theorem test : Nonempty PUnit.{u} := inferInstance
example : Nonempty PUnit.{1} := test.{1}        -- works
example : Nonempty PUnit.{1} := by duper [test] -- fails