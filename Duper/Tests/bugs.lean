import Duper.TPTP
import Duper.Tactic

set_option maxHeartbeats 20000

tptp PUZ137_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ137_8.p"
  by duper -- Prover saturated (from PUZ_tests.lean)

tptp COM003_1 "../TPTP-v8.0.0/Problems/COM/COM003_1.p"
  by duper -- (deterministic) timeout

tptp PUZ031_1_modified "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p" by 
  have inhabited_plant : Inhabited plant := sorry
  have inhabited_snail : Inhabited snail := sorry
  have inhabited_grain : Inhabited grain := sorry
  have inhabited_bird : Inhabited bird := sorry
  have inhabited_fox : Inhabited fox := sorry
  have Inhabited_wolf : Inhabited wolf := sorry
  duper -- If these instances are not provided, duper will fail
  -- Previously: Error when reconstructing clausification

theorem escaped_mvar_test_working {a : Type} [Inhabited a] : (∃ a' : a, a' = a') :=
  by duper -- Works because a' appears in the there exists statement

theorem escaped_mvar_test_broken {a : Type} [Inhabited a] : (∃ a' : a, true) :=
  by duper -- Works
  -- Previously: Fails because a' does not appear in the there exists statement

theorem escaped_mvar_test2_working {a : Type} [Inhabited a] (h : ¬ (false = true)) : ¬(∀ a' : a, ¬(a' = a')) :=
  by duper -- Works because a' appears in the forall statement

theorem escaped_mvar_test2_broken {a : Type} [Inhabited a] (h : ¬ (false = true)) : ¬(∀ a' : a, false) :=
  by duper -- Works
  -- Previously: Fails because a' does not appear in the forall statement





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
tptp COM003_1_copy "../TPTP-v8.0.0/Problems/COM/COM003_1.p"
  by duper -- (deterministic) timeout

#check Lean.Meta.whnf

set_option trace.Meta.debug true in
example (Group : Type)
        (mult : Group → Group → Group)
        (inverse : Group → Group)
        (cube : Group → Group)
        (e : Group)
        (left_identity : ∀ (x : Group), mult e x = x)
        (left_inverse : ∀ (x : Group), mult (inverse x) x = e)
        (associativity : ∀ (x y z : Group), mult (mult x y) z = mult x (mult y z))
        (cube_definition : ∀ x, cube x = mult x (mult x x))
        (cube_injective : ∀ x y, cube x = cube y → x = y)
        (cube_surjective : ∀ x, ∃ y, x = cube y)
        (cube_homomorphism : ∀ x y, cube (mult x y) = mult (cube x) (cube y))
        : ∀ x y, mult x y = mult y x := by duper




-- MWE of
/-
  Lean server printed an error:
    PANIC at Lean.MetavarContext.getDecl Lean.MetavarContext:370:17: unknown metavariable
-/

set_option trace.Meta.debug true in
example (A : Type) [Inhabited A] (f g : A → A) (h : ∀ a, ∃ b, f a = g b) :
  ∀ a, ∃ b, f a = g b := by
  duper

-- Unknown metavariable error during proof reconstruction
-- Error happens here:
/-
Reconstructing proof for #5: (∃ b, f #0 = g b) = True, Rule Name: clausification

...

[Meta.debug] Reconstructing skolems _uniq.178491 -> _uniq.178491

-- Happens here

[Meta.debug] Reconstructed skolem definition
fun (_ : _uniq.178491) => Duper.Inhabited.some.{1} _uniq.178491 _uniq.178492
  (fun (x : _uniq.178491) => Eq.{1} _uniq.178491 (_uniq.178493 _) (_uniq.178494 x)) 

Reconstructing proof for #6: (f #0 = g (sk.8 #0)) = True, Rule Name: clausification
-/