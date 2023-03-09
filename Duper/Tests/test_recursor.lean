import Duper.Tactic
import Duper.TPTP

set_option trace.Meta.debug true in
set_option trace.Prover.debug true in
def rec₁ : False := by
  duper [Nat.rec]

#check Nat.rec