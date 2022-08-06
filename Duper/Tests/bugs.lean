import Duper.TPTP
import Duper.Tactic

set_option maxHeartbeats 10000

tptp PUZ082_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ082_8.p"
  by duper PUZ082_8

tptp PUZ012_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ012_1.p"
  by duper PUZ012_1 -- Succeeds if PUZ082_8 above is uncommented, and times out if PUZ082_8 above is commented out

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

-- See super_test at the end of test.lean file