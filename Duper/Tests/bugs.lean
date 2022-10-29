import Duper.TPTP
import Duper.Tactic

set_option maxHeartbeats 20000

tptp PUZ137_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ137_8.p"
  by duper -- Prover saturated (from PUZ_tests.lean)

tptp COM003_1 "../TPTP-v8.0.0/Problems/COM/COM003_1.p"
  by duper -- Prover saturated (since commit 87a238ff1b76b041ef9df88557f3ceb9c4b6c89a) (from TPTP_test.lean)

tptp PUZ031_1_modified "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p" by 
  have inhabited_plant : Inhabited plant := sorry
  duper -- Error when reconstructing clausification

theorem escaped_mvar_test_working {a : Type} [Inhabited a] : (∃ a' : a, a' = a') :=
  by duper -- Works because a' appears in the there exists statement

theorem escaped_mvar_test_broken {a : Type} [Inhabited a] : (∃ a' : a, true) :=
  by duper -- Fails because a' does not appear in the there exists statement

theorem escaped_mvar_test2_working {a : Type} [Inhabited a] (h : ¬ (false = true)) : ¬(∀ a' : a, ¬(a' = a')) :=
  by duper -- Works because a' appears in the forall statement

theorem escaped_mvar_test2_broken {a : Type} [Inhabited a] (h : ¬ (false = true)) : ¬(∀ a' : a, false) :=
  by duper -- Fails because a' does not appear in the forall statement





-- By Indprinciple
-- Not sure whether these are known bugs

axiom f : Nat → Nat
axiom g : Nat → Nat
axiom i : Int → Nat
axiom a : Nat

set_option trace.Meta.debug true in
example (h : ∀ a, ∀ b, ∀ c, ∃ d, f a = b ∧ g c = d) :
  ∀ a, ∀ b, ∀ c, ∃ d, f a = b ∧ g c = d := by duper

set_option trace.Meta.debug true in
set_option trace.Print_Proof true in
def qk : ∀ x : Nat, x = x := by duper

set_option trace.Meta.debug true in
theorem escaped_mvar_test_broken {a : Type} [Inhabited a] : (∃ a' : a, true) :=
  by duper

#check 2

set_option trace.Meta.debug true in
tptp NUM931_5 "../TPTP-v8.0.0/Problems/NUM/NUM931_5.p" by duper

set_option trace.Meta.debug true in
tptp PUZ135_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ135_1.p"
  by duper -- Det timeout