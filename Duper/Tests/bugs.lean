import Duper.TPTP
import Duper.Tactic

-- set_option maxHeartbeats 20000

tptp PUZ137_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ137_8.p"
  by duper -- Prover saturated (from PUZ_tests.lean)

tptp PUZ031_1_modified "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p" by 
  have inhabited_plant : Inhabited plant := sorry
  have inhabited_snail : Inhabited snail := sorry
  have inhabited_grain : Inhabited grain := sorry
  have inhabited_bird : Inhabited bird := sorry
  have inhabited_fox : Inhabited fox := sorry
  have inhabited_wolf : Inhabited wolf := sorry
  duper
  -- If these instances are not provided, duper will fail
  -- Previously: Error when reconstructing clausification

example (x : Type u) (f g : Type u → Type v) (H : f = g) : f x = g x :=
  by duper
-- Previously: Type mismatch caused by incorrect manipulation of
-- universe levels in `ArgCong`

example (x y z : Type 2) (f g h : Type 2 → Type 4) (H : f = g ∨ g = h ∨ h = f) :
  f x = g x ∨ g y = h y ∨ h z = f z := by duper