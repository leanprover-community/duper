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


def test : Color → Color
| .red => .green
| .green => .red

set_option pp.match false
#print test
#print test.match_1
#print Color.casesOn

-- Not sure why this does not work:
example : test .red = .green := by duper [test, test.match_1, Color.rec, Color.casesOn]

end Color2


set_option simultaneousSuperposition false -- TODO: There is a bug in simultaneous sup that prevents this example from working
set_option trace.DUnif.result true
set_option dUnifDbgOn true
set_option trace.Superposition.debug true
set_option trace.Saturate.debug true
-- set_option maxHeartbeats 200
example : @Nat.rec (fun _ => Bool) a b Nat.zero = a := by duper [Nat.rec]

