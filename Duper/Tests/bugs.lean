import Duper.TPTP
import Duper.Tactic

tptp COM025_5 "../TPTP-v8.0.0/Problems/COM/COM025_5.p"
  by duper

tptp HWV042 "../TPTP-v8.0.0/Problems/HWV/HWV042_1.p"
  by duper

set_option maxTPTPProblemLines 10000 in
tptp ITP222 "../TPTP-v8.0.0/Problems/ITP/ITP222_2.p"
  by sorry

set_option maxTPTPProblemLines 10000 in
tptp ITP010_7 "../TPTP-v8.0.0/Problems/ITP/ITP010_7.p"
  by sorry

-- Previously: Type mismatch caused by incorrect manipulation of
-- universe levels in `ArgCong`
example : ((∀ (A : Type) (f : Nat → A) (x : Nat), f x = f x) = True) := by duper

universe u
theorem test : Nonempty PUnit.{u} := inferInstance
example : Nonempty PUnit.{1} := test.{1}        -- works
example : Nonempty PUnit.{1} := by duper [test] -- fails