import Duper.TPTP
import Duper.Tactic

-- precCompare not working properly
/-
[Rule.superposition] Comparing skS.0 0 ?m.4692, skS.0 1 ?m.4692 ?m.4693, result: < 

[Rule.superposition] Comparing skS.0 1 ?m.4692 ?m.4693, skS.0 0 ?m.4692, result: <
-/
set_option trace.Prover.saturate true in
set_option trace.Rule.superposition true in
tptp SEU139 "../TPTP-v8.0.0/Problems/SEU/SEU139+1.p"
  by duper

-- precCompare bug
set_option trace.Meta.debug true in
set_option trace.Prover.saturate true in
tptp NUM020_1 "../TPTP-v8.0.0/Problems/NUM/NUM020^1.p"
  by duper

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