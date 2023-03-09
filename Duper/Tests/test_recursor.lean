import Duper.Tactic
import Duper.TPTP

set_option trace.Meta.debug true in
set_option trace.Prover.debug true in
def rec₁ : False := by
  duper [Nat.rec]

#check Nat.rec

namespace Color1

inductive Color :=
| red : Color

example : @Color.rec (fun _ => Nat) a .red = a := by duper [Color.rec]

end Color1

namespace Color2

inductive Color :=
| red : Color
| green : Color

set_option trace.DUnif.result true
set_option dUnifDbgOn true
set_option trace.Superposition.debug true
set_option trace.Saturate.debug true

example : @Color.rec (fun _ => Nat) a b .red = a := by duper [Color.rec]


end Color2
