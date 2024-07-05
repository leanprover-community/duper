import Duper.Tactic
import Duper.TPTP

-- set_option pp.all true
-- set_option pp.rawOnError true
set_option duper.printPortfolioInstance true
set_option duper.printTimeInformation true

axiom a : Nat
axiom b : Nat
axiom c : Nat
axiom d : Nat
axiom zero : Nat
axiom one : Nat
axiom div : Nat → Nat → Nat
axiom mul : Nat → Nat → Nat
axiom add : Nat → Nat → Nat
axiom inv : Nat → Nat
axiom f : Nat → Nat
axiom g : Nat → Nat
axiom h : Nat → Nat
axiom p : Nat → Prop
axiom q : Prop
axiom isZero : Nat → Prop

theorem test0000 (one : Nat) (isZero : Nat → Prop) (div mul add : Nat → Nat → Nat)
(div_self : ∀ x, ¬ isZero x → div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), ¬ isZero y → div x y = mul x (inv y)) :
∀ (x y : Nat), ¬ isZero y → div (add x y) y = add (div x y) one := by duper [*]
#print axioms test0000

-- Contradiction found. Time: 647ms
theorem test0018 (a1 a2 a3 a4 a5 a6 : Nat)
(h1 :
f (f (f (f (f (f (f (f a5))))))) = d ∨
f (f (f (f (f (f (f a4)))))) = d ∨
f (f (f (f (f (f a3))))) = d ∨
f (f (f (f (f a2)))) = d ∨
f (f (f (f a1))) = d ∨
f (f (f a)) = d ∨ f (f b) = d ∨ f c = d)
(h2 : f (f (f (f (f (f (f (f a5))))))) ≠ d)
(h2 : f (f (f (f (f (f (f a4)))))) ≠ d)
(h2 : f (f (f (f (f (f a3))))) ≠ d)
(h2 : f (f (f (f (f a2)))) ≠ d)
(h2 : f (f (f (f a1))) ≠ d)
(h2 : f (f (f a)) ≠ d)
(h3 : f (f b) ≠ d)
(h4 : f c ≠ d)
: False := by duper [*]

#print test0018

theorem test00008
(div_self : ∀ x, x ≠ zero → mul x (inv x) = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z)) :
∀ (x y : Nat), y ≠ zero → mul (add x y) (inv y) = add (mul x (inv y)) one := by duper [*]

theorem test00008'
(div_self : ∀ x, x ≠ zero → div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), y ≠ zero → div x y = mul x (inv y)) :
∀ (x y : Nat), y ≠ zero → mul (add x y) (inv y) = add (mul x (inv y)) one := by duper [*]

theorem test
(div_self : ∀ x, div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), div x y = mul x (inv y)) :
∀ (x y : Nat), div (add x y) y = add (div x y) one := by duper [*]

-- #print test
-- #print axioms test

example --(h : ∃ x, x ≠ c ∨ a = b)
(h : ¬ ∃ x, x = f a ∨ ∀ x, ∃ y, y = f a ∧ x = b)-- (h :  c = b ∧ a = b)
: False := by duper [*]

set_option trace.Meta.debug true in
theorem test00
(ax1 : a ≠ a ∨ ¬ (∀ x : Nat, x = x) ∨ b ≠ b)
: False := by duper [*]


#print test00

theorem test0
(ax1 : f a = b → f c ≠ b)
(ax2 : ¬ ∃ x, f x ≠ b ∧ c = c)
: False := by duper [*]

#print test0

theorem test1
(div_self : ∀ x, f x = a)
(div_self : ∀ x, f x ≠ a)
: False := by duper [*]

#print test1

theorem test1'
(div_self : ∀ x y z : Nat, f x ≠ f x ∨ g y ≠ g y ∨ h z ≠ h z)
: False := by duper [*]

theorem test2
: ∀ (x : Nat), x = x := by duper

#print test2

theorem test3 (f g : α → α) : (∀ x, f x = g x) = (∀ x, f x = g x) := by duper

theorem puzzle1 {ι : Type} (johanna : ι) (bill : ι) (peanuts : ι)
  (food : ι → Prop) (alive : ι → Prop)
  (likes : ι → ι → Prop) (eats : ι → ι → Prop) (was_killed_by : ι → ι → Prop)
  (h1 : ∀ x, food x → likes johanna x)
  (h2 : ∀ x, (∃ y, eats y x ∧ ¬ was_killed_by y x) → food x)
  (h3 : eats bill peanuts)
  (h4 : alive bill)
  (h5 : ∀ y, alive y → ∀ x, ¬ was_killed_by y x) :
likes johanna peanuts := by duper [*]

#print puzzle1

#print axioms puzzle1

/- Leaving this test commented out because we expect it to time out
set_option maxHeartbeats 10000 in
theorem puzzle2 {ι : Type} (Tarr : ι) (Fether : ι)
  (Doctor : ι → Prop) (Peculiar : ι → Prop) (Sane : ι → Prop)
  (bestFriend : ι → ι) (Special : ι → Prop)
  (h4 : ∀x, Peculiar x = (Sane x = ¬ Doctor x))
  (h5 : ∀x, Special x = (∀y, ¬ Doctor y = (Sane y = Peculiar x)))
  (h7 : ∀x, ∀y, (Sane x = Special y) → (Sane (bestFriend x) = ¬ Doctor y))
  (h8 : Sane Tarr = ∀x, Doctor x → Sane x)
  (h10 : Sane Fether = ∀x, Doctor x → ¬ Sane x)
  (h12 : Sane Fether = Sane Tarr) :
False := by duper
-/

-- Time 29717ms
theorem test0011 (one : Nat) (div mul add : Nat → Nat → Nat)
(div_self : ∀ x, div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), div x y = mul x (inv y)) :
∀ (x y : Nat), div (add x y) y = add (div x y) one := by duper [*]
#print test0011
#print axioms test0011

--###############################################################################################################################
--Clausifying prop inequality tests
theorem propInequalityTest1 {p : Prop} {q : Prop} (h : p ≠ q) : p ∨ q :=
  by duper [*]

theorem propInequalityTest2 {p : Prop} {q : Prop} (h : p ≠ q) : ¬p ∨ ¬q :=
  by duper [*]

#print propInequalityTest1 -- clause 4 uses clausify_prop_inequality2
#print axioms propInequalityTest1
#print propInequalityTest2 -- clause 3 uses clausify_prop_inequality1
#print axioms propInequalityTest2

--###############################################################################################################################
--Iff clausification tests
theorem iffClausificationTest1 {p : Prop} {q : Prop} (h : p ↔ q) : (p → q) ∧ (q → p) :=
  by duper [h]

theorem iffClausificationTest2 {p : Prop} {q : Prop} (h : ¬(p ↔ q)) : (p → ¬q) ∧ (q → ¬p) :=
  by duper [h]

#print iffClausificationTest1
#print iffClausificationTest2
#print axioms iffClausificationTest1
#print axioms iffClausificationTest2
--###############################################################################################################################
--Aside from being an interesting thing to prove on its own, the barber_paradox tests rely on the first case of Iff clausification and
--on the soundness of ClausifyPropEq's reconstructed proofs
/-
List of problems pertaining to the barber paradox:
- Duper is unable to synthesize the type "Inhabited person" unless it is given an argument of that type or an argument of type person
- General issues with using duper in larger tactic-style proofs (mdata isn't handled properly)
-/

set_option trace.Meta.debug true in
theorem barber_paradox1 {person : Type} {person_inhabited : Inhabited person} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False :=
  by duper [*]

theorem barber_paradox2 {person : Type} {shaves : person → person → Prop} {b : person}
  (h : ∀ p : person, (shaves b p ↔ (¬shaves p p))) : False :=
  by duper [*]

theorem barber_paradox3 {person : Type} {shaves : person → person → Prop} {b : person}
  (h1 : ∀ p : person, (shaves b p ↔ (¬ shaves p p))) (h2 : shaves b b ∨ ¬ shaves b b) : False :=
  by duper [h1]

theorem barber_paradox4 {person : Type} {person_inhabited : Inhabited person} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p → (¬ shaves p p)) ∧ ((¬ shaves p p) → shaves b p)) : False :=
  by duper [*]

theorem barber_paradox5 {person : Type} {shaves : person → person → Prop} {b : person}
  (h : shaves b b ↔ ¬shaves b b) : False :=
  by duper [*]

#print barber_paradox1
#print axioms barber_paradox1
#print axioms barber_paradox2
#print axioms barber_paradox3
#print axioms barber_paradox4
#print axioms barber_paradox5

--inline tests are to expose the issues that arise when we try to call duper in the midst of a larger tactic-style proof
theorem barber_paradox_inline0 {person : Type} {person_inhabited : Inhabited person} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p → (¬ shaves p p)) ∧ ((¬ shaves p p) → shaves b p)) : False := by
  cases h with
  | intro b h' =>
    duper [h']

theorem barber_paradox_inline1 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    duper [*]

theorem barber_paradox_inline2 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    duper [h' b]

theorem barber_paradox_inline3 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    have h'_b := h' b
    clear h'
    duper [h'_b]

#print barber_paradox_inline0
#print axioms barber_paradox_inline0
#print axioms barber_paradox_inline1
#print axioms barber_paradox_inline2
#print axioms barber_paradox_inline3

--###############################################################################################################################
-- syntacticTautologyDeletion2 and elimResolvedLit tests
/-
Prover becomes saturated as expected, but the point is just to confirm that trace.duper.simp.debug is printing that the correct clause is being removed
for the correct reason

theorem syntacticTautologyDeletionTest {t : Type} (a : t) (b : t) (c : t)
  (h : a = b ∨ a = c ∨ b ≠ a) : False := by duper
-/

theorem elimResolvedLitTest {t : Type} (a : t) (b : t) (c : t)
  (h : a = b ∨ a = c ∨ b ≠ b) : a = b ∨ a = c := by duper [h]

theorem elimResolvedLitTest2 {t : Type} (a : t) (b : t) (c : t)
  (h : b ≠ b ∨ a = b ∨ a ≠ a ∨ a = c ∨ b ≠ b ∨ c ≠ c) : a = b ∨ a = c := by duper [h]

theorem elimResolvedLitTest3 {t : Type} (a : t) (b : t) (c : t)
  (h : a ≠ a ∨ b ≠ b ∨ c ≠ c) : a = a ∨ b = b ∨ c = c := by duper

#print elimResolvedLitTest
#print axioms elimResolvedLitTest
#print axioms elimResolvedLitTest2
#print axioms elimResolvedLitTest3

--###############################################################################################################################
-- equalityFactoring tests (Trying to test each equality_factoring_soundness theorem)

theorem equalityFactoringTest1 {α : Type} (s t u v : α)
  (h1 : s = t ∨ s = v) : t ≠ v ∨ s = v :=
  by duper [*]

theorem equalityFactoringTest2 {α : Type} (s t u v : α)
  (h1 : s = t ∨ u = s) : t ≠ u ∨ u = s :=
  by duper [*]

theorem equalityFactoringTest3 {α : Type} (s t v : α)
  (h1 : s = t ∨ t = v) : s ≠ v ∨ t = v :=
  by duper [*]

/-
  Note to self: The only difference between equalityFactoringTest3 and equalityFactoringTest4 is the order of s t and v as arguments. This fact influences
  something in how they are compared to each other in Order.lean (I think it has an effect on VarBalance), which is why equalityFactoringTest3 uses
  equality_factoring_soundness2 and equalityFactoringTest4 uses equality_factoring_soundness4
-/
theorem equalityFactoringTest4 {α : Type} (v t s : α)
  (h1 : s = t ∨ t = v) : s ≠ v ∨ t = v :=
  by duper [*]

theorem equalityFactoringTest5 {α : Type} (s t u v : α)
  (h1 : s = t ∨ u = t) : s ≠ u ∨ u = t :=
  by duper [*]

#print equalityFactoringTest1 -- This proof uses equality_factoring_soundness1 (in the commit where this test is added, it is used in clause 5)
#print equalityFactoringTest2 -- This proof uses equality_factoring_soundness2 (in the commit where this test is added, it is used in clause 13)
#print equalityFactoringTest3 -- This proof uses equality_factoring_soundness2 (again) (in the commit where this test is added, it is used in clause 5)
#print equalityFactoringTest4 -- This proof uses equality_factoring_soundness3 (in the commit where this test is added, it is used in clause 5)
#print equalityFactoringTest5 -- This proof uses equality_factoring_soundness4 (in the commit where this test is added, it is used in clause 5)

#print axioms equalityFactoringTest1
#print axioms equalityFactoringTest2
#print axioms equalityFactoringTest3
#print axioms equalityFactoringTest4
#print axioms equalityFactoringTest5

--###############################################################################################################################
-- This test previously failed due to a bug in how we removed clauses
theorem removeClausesTest {α : Type} [Inhabited α] (x y : α) (c : α → Prop)
  (h1 : ∀ a b : α, a = b) : c x = c y := by duper [*]

--###############################################################################################################################
theorem COM002_2_test (state : Type) (follows fails : state → state → Prop) (p3 p6 : state)
  (h0 : ∀ (Start_state Goal_state : state), ¬(fails Goal_state Start_state ∧ follows Goal_state Start_state))
  (h1 : follows p6 p3) : ¬fails p6 p3 := by duper [*]

theorem COM002_2_test2 (state label statement : Type) (p8 : state) (loop : label) (goto : label → statement)
  (follows fails : state → state → Prop) (labels : label → state → Prop) (has : state → statement → Prop)
  (h0 : ∀ s1 s2 : state, ∀ l1 : label, ¬(fails s1 s2 ∧ has s2 (goto l1) ∧ labels l1 s1))
  (h1 : has p8 (goto loop)) : ∀ s1 : state, ¬(fails s1 p8 ∧ labels loop s1) := by duper [*]

/- Saturates because the goal is "False" rather than anything coherent, but the final active set is:
[fails p3 #0 = True ∨ fails #0 p3 = True,
 fails #2 #1 = False ∨ has #1 (goto #0) = False ∨ labels #0 #2 = False,
 has p3 (goto #0) = False ∨ labels #0 p3 = False,
 has p3 (goto #1) = False ∨ labels #1 #0 = False ∨ fails p3 #0 = True,
 fails p3 #1 = True ∨ has p3 (goto #0) = False ∨ labels #0 #1 = False,
 has #1 (goto #0) = False ∨ labels #0 p3 = False ∨ fails #1 p3 = True,
 fails #1 p3 = True ∨ has #1 (goto #0) = False ∨ labels #0 p3 = False,
 has #2 (goto #1) = False ∨ labels #1 p3 = False ∨ has p3 (goto #0) = False ∨ labels #0 #2 = False,
 fails p3 p3 = True]

theorem COM002_2_test3 (state label statement : Type) (p3 : state) (goto : label → statement)
  (follows fails : state → state → Prop) (labels : label → state → Prop) (has : state → statement → Prop)
  (h0 : ∀ s1 s2 : state, ∀ l1 : label, ¬(fails s1 s2 ∧ has s2 (goto l1) ∧ labels l1 s1))
  (h1 : ∀ s : state, fails p3 s ∨ fails s p3) : False := by duper
-/

--###############################################################################################################################
tptp KRS003_1 "../TPTP-v8.0.0/Problems/KRS/KRS003_1.p"
  by duper [*]

#print axioms KRS003_1

tptp PUZ012_1 "../TPTP-v8.0.0/Problems/PUZ/PUZ012_1.p"
  by duper [*]

#print PUZ012_1
--###############################################################################################################################
-- Tests that (in the current commit at least) use positive simplify reflect
set_option trace.duper.rule.simplifyReflect true in
tptp NUN004_5 "../TPTP-v8.0.0/Problems/NUN/NUN004_5.p"
  by duper [*]

set_option trace.duper.rule.simplifyReflect true in
tptp ITP209_2 "../TPTP-v8.0.0/Problems/ITP/ITP209_2.p"
  by duper [*]

--###############################################################################################################################
-- Example from super
theorem super_test (p q : i → i → Prop) (a b c d : i) :
  (∀x y z, p x y ∧ p y z → p x z) →
  (∀x y z, q x y ∧ q y z → q x z) →
  (∀x y, q x y → q y x) →
  (∀x y, p x y ∨ q x y) →
  p a b ∨ q c d :=
by duper

--###############################################################################################################################
-- Miscellaneous tests
example (h : ∀ a, ∀ b, ∀ c, ∃ d, f a = b ∧ g c = d) :
  ∀ a, ∀ b, ∀ c, ∃ d, f a = b ∧ g c = d := by duper [*]

-- Checks that duper can handle existential quantification where the variable doesn't appear in the body
example (h : ∃ y : Nat, False) : False := by duper [*]
example (h : (∃ y : Nat, True) = False) : False := by duper [*]

-- Checks that duper can handle universal quantification where the variable doesn't appear in the body
example (h : ∀ y : Nat, False) : False := by duper [*]
example (h : (∀ y : Nat, True) = False) : False := by duper [*]

-- Checks β/η reduction
example : (let f := (fun x => (x, x)); (fun x => f x) 1) = (1, 1) := by duper
example : ((fun (x y : Nat) => x + y) = Nat.add → False) → False := by duper
example : x + Nat.zero = x := by duper [Nat.add]
theorem test_duper_with_fact : 1 + 1 = 2 := by duper
theorem test_duper_with_facts : 1 + 1 + 1 + 1 = 4 := by duper

--###############################################################################################################################
-- Tests for providing facts to duper

theorem comm_test : Nat.add x y = Nat.add y x := by duper [Nat.add_comm]
theorem assoc_test : Nat.add (Nat.add x y) z = Nat.add x (Nat.add y z) := by duper [Nat.add_assoc]

--###############################################################################################################################
-- Hoist tests (note: forallHoist and existsHoist are only truly tested if identBoolHoist is diabled)

set_option trace.duper.printProof true in
theorem eqHoistTest (a b : Nat) (f : Prop → Prop) (h : f (a = b)) : ∃ p : Prop, f p :=
  by duper [h]

set_option trace.duper.printProof true in
theorem neHoistTest (a b : Nat) (f : Prop → Prop) (h : f (a ≠ b)) : ∃ p : Prop, f p :=
  by duper [*]

set_option trace.duper.printProof true in
theorem existsHoistTest1 (f : Prop → Nat) : f (∃ (x : Nat), x = Nat.zero) = f True := by duper

set_option trace.duper.printProof true in
set_option trace.duper.rule.existsHoist true in
theorem existsHoistTest2 (f : Prop → Nat) : ∀ y : Nat, f (∃ x : Nat, x = y) = f True := by duper

set_option trace.duper.printProof true in
set_option trace.duper.rule.existsHoist true in
theorem existsHoistTest3 (f : Prop → Nat) (h : ∀ z : Nat, ∀ y : Nat, f (∃ x : Nat, (x = y ∧ x = z)) ≠ f True) : False := by duper [*]

set_option trace.duper.printProof true in
theorem existsHoistTest4 (f : Prop → Nat)
  (h : ∀ x : Nat, f (∃ y : Nat, ∀ a : Nat, ∃ b : Nat, x = y ↔ a = b) ≠ f True) : False := by duper [*]

set_option trace.duper.printProof true in
theorem existsHoistTest5 (f : Prop → Nat)
  (h : ∀ x : Nat, ∃ y : Nat, f ((∃ z : Nat, z = x) ∧ (∃ z : Nat, z = y)) ≠ f True) : False := by duper [*]

set_option trace.duper.printProof true in
set_option trace.duper.rule.existsHoist true in
theorem existsHoistTest6 (f : Prop → Nat) : ∀ y : Nat, f (∃ x : Nat, 0 = 0) = f True := by duper

set_option trace.duper.printProof true in
set_option trace.duper.rule.existsHoist true in
theorem existsHoistTest7 (f : Prop → Nat) : ∀ y : Nat, f (∃ x : Nat, y = y) = f True := by duper

set_option trace.duper.printProof true in
theorem forallHoistTest1 (f : Prop → Nat) : f (∀ (x : Nat), x ≠ Nat.zero) = f False := by duper

set_option trace.duper.printProof true in
theorem forallHoistTest2 (f : Prop → Nat)
  (h : ∀ x : Nat, f (∀ y : Nat, x = y) ≠ f False) : False := by duper [*]

set_option trace.duper.printProof true in
theorem forallHoistTest3 (f : Prop → Nat)
  (h : ∃ x : Nat, f (∀ y : Nat, x = y) ≠ f False) : False := by duper [*]

set_option trace.duper.printProof true in
theorem forallHoistTest4 (f : Prop → Nat)
  (h : ∀ x : Nat, ∀ y : Nat, f (∀ z : Nat, x = z ↔ y = z) ≠ f False) : False := by duper [*]

set_option trace.duper.printProof true in
theorem forallHoistTest5 (f : Prop → Nat)
  (h : ∀ x : Nat, ∃ y : Nat, f (∀ z : Nat, x = z ∧ y = z) ≠ f False) : False := by duper [*]

--###############################################################################################################################
-- Tests that were previously in bugs.lean
example (f : Prop → Nat) :
  f (∀ (x : Nat), x ≠ Nat.zero) = f False := by duper

example (f : Prop → Nat) :
  f (f (∀ (x : Nat), x ≠ Nat.zero) = f False) = f True := by duper

example (f g : Nat → Nat) (h : ∀ a, ∃ d, f a = d) :
  ∀ a, ∃ d, f a = d := by duper

set_option trace.Meta.debug true in
example : ((∀ (f : Nat → Nat) (x : Nat), f x = f x) = True) := by duper

example (A : Type) (x : A) : (∃ x : A, x = x) := by duper

example (x : Type u) (f g : Type u → Type v) (H : f = g) : f x = g x :=
  by duper [*]

example (x y z : Type u) (f g : Type u → Type u → Type u → Type v) (H : f = g) : f x y z = g x y z :=
  by duper [*]

tptp PUZ137_8 "../TPTP-v8.0.0/Problems/PUZ/PUZ137_8.p"
  by duper [*]

tptp PUZ031_1_modified "../TPTP-v8.0.0/Problems/PUZ/PUZ031_1.p" by
  have inhabited_plant : Inhabited plant := sorry
  have inhabited_snail : Inhabited snail := sorry
  have inhabited_grain : Inhabited grain := sorry
  have inhabited_bird : Inhabited bird := sorry
  have inhabited_fox : Inhabited fox := sorry
  have inhabited_wolf : Inhabited wolf := sorry
  have inhabited_animal : Inhabited animal := sorry
  have inhabited_caterpillar : Inhabited caterpillar := sorry
  duper [*]
  -- If these instances are not provided, duper will fail

tptp SEU123 "../TPTP-v8.0.0/Problems/SEU/SEU123+1.p"
  by duper [*]

set_option trace.duper.rule.superposition true in
tptp SEU139 "../TPTP-v8.0.0/Problems/SEU/SEU139+1.p"
  by duper [*]

--###############################################################################################################################
-- Tests that were previously in morebugs.lean
namespace Axioms

axiom X : Type
axiom f : (X → Prop) → Prop

theorem about (s : X → Prop) : f s :=
sorry

example (s : X → Prop) : f s :=
by duper [about]

end Axioms
--###############################################################################################################################
/- BoolSimp tests -/

theorem boolSimpRule26TestDep₁ (a b y z r : Prop) (dep : a → Prop) (h : ((x : a) → b → dep x → (dep x ∨ y ∨ z)) = r) : r :=
  by duper [*]

theorem boolSimpRule27TestDep₁ (a b c y z r : Prop) (f : a ∧ b ∧ c → Prop) (h : ((x : a ∧ b ∧ c) → (y ∨ f x ∨ c ∨ z)) = r) : r :=
  by duper [*]

/- Negative BoolSimp tests -/

namespace NegativeBoolSimpTests

axiom f.{u} : Sort u → Nat

def neg₁ : (f (Nat → Nat) = f (Nat → Nat)) := by duper

-- A positive example
def pos₁ : (f (Nat → False) = f False) := by duper

axiom g.{u} : ∀ (α : Sort u), α → Nat

def neg₂ : g (Nat → True) (fun _ => True.intro) = g (Nat → True) (fun _ => True.intro) :=
  by duper

def neg3 : g (True → True) (fun _ => True.intro) = g (True → True) (fun _ => True.intro) :=
  by duper

end NegativeBoolSimpTests

/- ClauseStreamHeap tests -/
tptp MGT008 "../TPTP-v8.0.0/Problems/MGT/MGT008+1.p"
  by duper [*]

example (f : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat)
  (g : Nat → Nat → Nat → Nat → Nat → Nat)
  (inertia : TPTP.iota → TPTP.iota → TPTP.iota → Prop)
  (goodInertia goodChance : TPTP.iota → Prop)
  (organization: TPTP.iota → TPTP.iota → Prop)
  -- good inertia implies good survival chance
  (dummy: ∀ (Y T2 I2 P2 : TPTP.iota), organization Y T2 ∧ inertia Y I2 T2 ∧ goodInertia I2 → goodChance P2)
  : ∃ x : Nat,
       f (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) (g x x x x x)
     = f (g 1 x x x x) (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) :=
  by duper

example
(inertia : TPTP.iota → TPTP.iota → TPTP.iota → Prop)
(goodInertia goodChance : TPTP.iota → Prop)
(dummy: TPTP.iota → TPTP.iota → TPTP.iota → TPTP.iota → Prop)
(organization: TPTP.iota → TPTP.iota → Prop)
(h1: ∀ (X T : TPTP.iota), organization X T → ∃ I, inertia X I T)
(h2: ∀ (Y I2 T2 : TPTP.iota),
-- good size implies good inertia
  organization Y T2 → inertia Y I2 T2 →
    goodInertia I2)
-- good inertia implies good survival chance
(h3: ∀ (Y T2 I2 P2 : TPTP.iota),
  (((organization Y T2 ∧ inertia Y I2 T2))) ∧
      goodInertia I2 →
    goodChance P2)
-- to show: good size implies good survival chance
(h4: ¬∀ (X Y P1 P2 S2 T1 T2 : TPTP.iota),
    organization Y T2 → dummy X P1 T1 S2 →
      goodChance P2) : False := by duper [*]

-- Universe level tests

namespace UniverseTest

axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

set_option trace.duper.printProof true in
def unitst₁ : f.{max u v} (Sort (max u v)) ∧ f.{v} (Sort v) := by
  duper [ftrue]

axiom fmoretrue.{u} : ∀ (x : Type u), f x

set_option trace.duper.printProof true in
def unitst₂ : ∀ (x : Type v), f x := by
  duper [fmoretrue]

axiom exftrue.{u} : ∃ (x : Type u), f x

set_option trace.duper.proofReconstruction true in
def skuniverse.{u} : ∃ (x : Type u), f x := by
  duper [exftrue]

end UniverseTest


-- Recursor tests

namespace RecursorTests

inductive Color1 :=
| red : Color1

example : @Color1.rec (fun _ => Nat) a .red = a := by duper [Color1.rec]

example : ∀ a b, @Nat.rec (fun _ => Bool) a b Nat.zero = a := by duper [Nat.rec]

example : ∀ a b, @Nat.rec (fun _ => Bool) a b Nat.zero = a := by duper [Nat.rec]

end RecursorTests
--###############################################################################################################################
-- Tests interaction with instances
instance : Neg Nat := sorry
-- @Neg.neg instNegNat gets reduced to (sorryAx (Neg Nat)).1, so working with this instance requires that Order.lean support projections

def even_int_fun (f : Int → Int) := ∀ x, f (-x) = f x
def even_nat_fun (f : Nat → Nat) := ∀ x, f (-x) = f x

instance : Add (Int → Int) := (⟨fun f g x => f x + g x⟩ : Add (Int → Int))
instance : Add (Nat → Nat) := (⟨fun f g x => f x + g x⟩ : Add (Nat → Nat))

example (f : Int → Int) (hf : ∀ x, f (-x) = f x) : even_int_fun f := by -- The goal is the same as hf
  duper [hf, even_int_fun]

example (f : Nat → Nat) (hf : ∀ x, f (-x) = f x) : even_nat_fun f := by -- The goal is the same as hf
  duper [hf, even_nat_fun]
--###############################################################################################################################
-- Tests duper's ability to derive that types are nonempty
example (p : α → β → Prop) (h : ∀ (x : α), ∃ y, p x y) : ∃ (f : α → β), ∀ x, p x (f x) :=
  by duper [*]

example (p : α → β → Prop) (h : ∀ (x : α), ∀ (z : Nat), ∃ y, p x y) : ∃ (f : α → β), ∀ x, p x (f x) :=
  by duper [*]

example (p : α → β → Prop) (h : ∀ (x : α), ∃ (z : Nat), ∃ y, p x y) : ∃ (f : α → β), ∀ x, p x (f x) :=
  by duper [*]

example (h : Nonempty (α → β)) : (∀ n : Nat, ∀ a : α, ∃ b : β, True) = True :=
  by duper [h]

example (h : Nonempty (α → β) = True) : (∀ n : Nat, ∀ a : α, ∃ b : β, True) = True :=
  by duper [*]

example (h : Nonempty (α → β) = True) : ∀ n : Nat, ∀ a : α, ∃ b : β, True :=
  by duper [h]

example (h : Nonempty ((α → β) → γ)) : ∀ f : α → β, ∃ y : γ, True :=
  by duper [h]

example (h1 : Nonempty ((α → β) → γ)) (h2 : ∀ x : α, Nonempty β) : ∃ y : γ, true :=
  by duper [*]

example (h1 : ∀ f : α → β, Nonempty γ) (h2 : ∀ x : α, Nonempty β) : ∃ y : γ, true :=
  by duper [h1, h2]

example (p : α → β → γ → Prop) (q : α → β → γ) (h : ∀ (x : α) (y : β), p x y (q x y)) :
  ∃ (f : α → β → γ), ∀ x y, p x y (f x y) :=
  by duper [h]

example (p : Prop) (h : Nonempty p = True) : p := by duper [*]

example (p : Prop) (h : Nonempty (PProd p α) = True) : p := by duper [*]

example (p : Prop) (h : Nonempty (PProd α p) = True) : p := by duper [*]

example (p : Prop) (h : ∃ hp : p, True) : p := by duper [*]

example (h : Nonempty (α × β)) : Nonempty α := by duper [*]

example (h : Nonempty (α × β)) : Nonempty β := by duper [*]

-- Test duper's ability to deal with projections
theorem proj_test (h1 : ∀ x : Nat, x > 0 → ∃ y : Fin x, y.1 = 0) (h2 : 3 > 0) : ∃ z : Fin 3, z.1 = 0 := by
  duper [h1, h2]

def sk (a b : Nat) (c : Nat × Nat) (h1 : c = (a, b)) : c.1 = a := by
  duper [h1]

#print sk
--###############################################################################################################################
-- This test previously failed due to a bug in ArgCong
example (a b : Nat) (matrix : Fin a → Fin b → Nat)
  (transpose : ∀ n : Nat, ∀ m : Nat, (Fin n → Fin m → Nat) → (Fin m → Fin n → Nat))
  (h : ∀ n : Nat, ∀ m : Nat, (fun x => transpose n m (transpose m n x)) = (fun x => x)) :
  transpose b a (transpose a b matrix) = matrix := by
  duper [h]

--###############################################################################################################################
-- Inductive datatype tests

inductive myType
| const1 : myType
| const2 : myType

inductive myType2 (t : Type _)
| const3 : t → myType2 t
| const4 : t → myType2 t

inductive myType3
| const5 : myType3
| const6 : myType3 → myType3

inductive myType4 (t1 t2 : Type _)
| const7 : t1 → t2 → myType4 t1 t2

inductive myEmpty (t1 : Type _) (t2 : Type _)

open myType myType2 myType3 myType4

example : const1 ≠ const2 := by
  duper

example : const3 (Type 8) ≠ const4 (Type 8) := by
  duper

example : const5 ≠ const6 const5 := by
  duper

example : [] ≠ [2] := by
  duper

example (p : Prop) (t1 t2 : Type a) (t3 t4 : Type b) (h : p = True ∨ const7 t1 t3 = const7 t2 t4) :
  ¬p → t1 = t2 ∧ t3 = t4 := by
  duper [h]

example (p : Prop) (a b c : Nat) (h : [0, 1, 2] = [a, b, c] ∨ p = True) :
  ¬p → 0 = a ∧ 1 = b ∧ 2 = c := by duper [h]

example (a b x y : Nat) (f : Nat → Nat)
  (h1 : ∀ z1 z2 : Nat, z1 ≠ z2 → f z1 ≠ f z2)
  (h2 : [0, a, x, 3] ≠ [0, b, y, 3]) :
  f a ≠ f b ∨ f x ≠ f y := by
  duper [h1, h2] {portfolioInstance := 7}

example (x y : Nat) (h : [x] ≠ [y]) : x ≠ y := by
  duper [h] {portfolioInstance := 7}

set_option duper.collectDatatypes true in
example : ¬∃ x : Empty, True := by
  duper

set_option duper.collectDatatypes true in
example : ¬∃ x : (myEmpty Prop Type), True := by
  duper
