import Duper.Tactic

-- set_option trace.Meta.debug true
-- set_option trace.Prover.saturate true
-- set_option trace.Prover.debug true
-- set_option trace.Rule.debug true
-- set_option pp.all true

constant a : Nat
constant b : Nat
constant c : Nat
constant d : Nat
constant zero : Nat
constant one : Nat
constant div : Nat → Nat → Nat
constant mul : Nat → Nat → Nat
constant add : Nat → Nat → Nat
constant inv : Nat → Nat
constant f : Nat → Nat
constant g : Nat → Nat
constant h : Nat → Nat
constant p : Nat → Prop
constant q : Prop
constant isZero : Nat → Prop

-- theorem test0000 (one : Nat) (isZero : Nat → Prop) (div mul add : Nat → Nat → Nat)
-- (div_self : ∀ x, ¬ isZero x → div x x = one)
-- (add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
-- (div_def : ∀ (x y : Nat), ¬ isZero y → div x y = mul x (inv y)) :
-- ∀ (x y : Nat), ¬ isZero y → div (add x y) y = add (div x y) one := by duper
-- #print axioms test0000

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
: False := by duper

#print test0018

-- theorem test00008
-- (div_self : ∀ x, x ≠ zero → mul x (inv x) = one)
-- (add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z)) :
-- -- (div_def : ∀ (x y : Nat), y ≠ zero → div x y = mul x (inv y)) :
-- ∀ (x y : Nat), y ≠ zero → mul (add x y) (inv y) = add (mul x (inv y)) one := by duper


-- theorem test00008
-- (div_self : ∀ x, x ≠ zero → div x x = one)
-- (add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
-- (div_def : ∀ (x y : Nat), y ≠ zero → div x y = mul x (inv y)) :
-- ∀ (x y : Nat), y ≠ zero → mul (add x y) (inv y) = add (mul x (inv y)) one := by duper

-- #print test
-- #print axioms test

-- theorem test 
-- (div_self : ∀ x, div x x = one)
-- (add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
-- (div_def : ∀ (x y : Nat), div x y = mul x (inv y)) :
-- ∀ (x y : Nat), div (add x y) y = add (div x y) one := by duper

-- #print test
-- #print axioms test

-- example --(h : ∃ x, x ≠ c ∨ a = b) 
-- (h : ¬ ∃ x, x = f a ∨ ∀ x, ∃ y, y = f a ∧ x = b)-- (h :  c = b ∧ a = b) 
-- : False := by
--   prover
--   all_goals
--     sorry
#check fun h => Eq.mpr h True.intro
#check propext

theorem test00
(ax1 : a ≠ a ∨ ¬ (∀ x : Nat, x = x) ∨ b ≠ b)
: False := by duper

#print test00

theorem test0
(ax1 : f a = b → f c ≠ b)
(ax2 : ¬ ∃ x, f x ≠ b ∧ c = c)
: False := by duper

#print test0

theorem test1
(div_self : ∀ x, f x = a)
(div_self : ∀ x, f x ≠ a)
: False := by duper


#print test1

theorem test1'
(div_self : ∀ x y z : Nat, f x ≠ f x ∨ g y ≠ g y ∨ h z ≠ h z)
: False := by duper

theorem test2
: ∀ (x : Nat), x = x := by duper

#print test2


theorem puzzle1 {ι : Type} (johanna : ι) (bill : ι) (peanuts : ι)
  (food : ι → Prop) (alive : ι → Prop) 
  (likes : ι → ι → Prop) (eats : ι → ι → Prop) (was_killed_by : ι → ι → Prop)
  (h1 : ∀ x, food x → likes johanna x)
  (h2 : ∀ x, (∃ y, eats y x ∧ ¬ was_killed_by y x) → food x)
  (h3 : eats bill peanuts)
  (h4 : alive bill)
  (h5 : ∀ y, alive y → ∀ x, ¬ was_killed_by y x) :
likes johanna peanuts := by duper

#print puzzle1

#print axioms puzzle1
-- set_option trace.Meta.debug true

-- set_option trace.Prover.saturate true

-- set_option trace.Prover.debug true
-- set_option trace.Rule.debug true
-- set_option pp.all true

-- theorem puzzle2 {ι : Type} (Tarr : ι) (Fether : ι) 
--   (Doctor : ι → Prop) (Peculiar : ι → Prop) (Sane : ι → Prop)
--   (bestFriend : ι → ι) (Special : ι → Prop)
--   (h4 : ∀x, Peculiar x = (Sane x = ¬ Doctor x))
--   (h5 : ∀x, Special x = (∀y, ¬ Doctor y = (Sane y = Peculiar x)))
--   (h7 : ∀x, ∀y, (Sane x = Special y) → (Sane (bestFriend x) = ¬ Doctor y))
--   (h8 : Sane Tarr = ∀x, Doctor x → Sane x)
--   (h10 : Sane Fether = ∀x, Doctor x → ¬ Sane x)
--   (h12 : Sane Fether = Sane Tarr) : 
-- False := by duper


-- Time 29717ms
theorem test0011 (one : Nat) (div mul add : Nat → Nat → Nat)
(div_self : ∀ x, div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), div x y = mul x (inv y)) :
∀ (x y : Nat), div (add x y) y = add (div x y) one := by duper
#print test0011

set_option trace.Prover.saturate false

--###############################################################################################################################
--Clausifying prop inequality tests
set_option trace.Simp.debug true
theorem propInequalityTest1 {p : Prop} {q : Prop} (h : p ≠ q) : p ∨ q :=
  by duper

theorem propInequalityTest2 {p : Prop} {q : Prop} (h : p ≠ q) : ¬p ∨ ¬q :=
  by duper

#print propInequalityTest1 -- clause 4 uses clausify_prop_inequality2
#print axioms propInequalityTest1
#print propInequalityTest2 -- clause 3 uses clausify_prop_inequality1
#print axioms propInequalityTest2

set_option trace.Simp.debug false
--###############################################################################################################################
--Iff clausification tests
set_option trace.Simp.debug true
set_option trace.Prover.debug true

theorem iffClausificationTest1 {p : Prop} {q : Prop} (h : p ↔ q) : (p → q) ∧ (q → p) :=
  by duper

theorem iffClausificationTest2 {p : Prop} {q : Prop} (h : ¬(p ↔ q)) : (p → ¬q) ∧ (q → ¬p) :=
  by duper

#print iffClausificationTest1
#print iffClausificationTest2
#print axioms iffClausificationTest1
#print axioms iffClausificationTest2

set_option trace.Simp.debug false
set_option trace.Prover.debug false
--###############################################################################################################################
--Aside from being an interesting thing to prove on its own, the barber_paradox tests rely on the first case of Iff clausification and
--on the soundness of ClausifyPropEq's reconstructed proofs
/-
List of problems pertaining to the barber paradox:
- Duper is unable to synthesize the type "Inhabited person" unless it is given an argument of that type or an argument of type person
- General issues with using duper in larger tactic-style proofs (mdata isn't handled properly)
-/

theorem barber_paradox1 {person : Type} {person_inhabited : Inhabited person} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := 
  by duper

theorem barber_paradox2 {person : Type} {shaves : person → person → Prop} {b : person}
  (h : ∀ p : person, (shaves b p ↔ (¬shaves p p))) : False := 
  by duper

theorem barber_paradox3 {person : Type} {shaves : person → person → Prop} {b : person}
  (h1 : ∀ p : person, (shaves b p ↔ (¬ shaves p p))) (h2 : shaves b b ∨ ¬ shaves b b) : False :=
  by duper

theorem barber_paradox4 {person : Type} {person_inhabited : Inhabited person} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p → (¬ shaves p p)) ∧ ((¬ shaves p p) → shaves b p)) : False :=
  by duper

theorem barber_paradox5 {person : Type} {shaves : person → person → Prop} {b : person}
  (h : shaves b b ↔ ¬shaves b b) : False :=
  by duper

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
    duper

theorem barber_paradox_inline1 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    duper

theorem barber_paradox_inline2 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    have h'_b := h' b
    duper

set_option trace.Prover.debug true
set_option trace.Meta.debug true
set_option trace.Prover.saturate true
set_option maxHeartbeats 1000

theorem barber_paradox_inline3 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    have h'_b := h' b
    clear h'
    duper

set_option trace.Prover.debug false
set_option trace.Meta.debug false
set_option trace.Prover.saturate false

#print barber_paradox_inline0
#print axioms barber_paradox_inline0
#print axioms barber_paradox_inline1
#print axioms barber_paradox_inline2
#print axioms barber_paradox_inline3

--###############################################################################################################################
-- syntacticTautologyDeletion2 and elimResolvedLit tests
/-
Prover becomes saturated as expected, but the point is just to confirm that trace.Simp.debug is printing that the correct clause is being removed
for the correct reason

theorem syntacticTautologyDeletionTest {t : Type} (a : t) (b : t) (c : t)
  (h : a = b ∨ a = c ∨ b ≠ a) : False := by duper
-/

theorem elimResolvedLitTest {t : Type} (a : t) (b : t) (c : t)
  (h : a = b ∨ a = c ∨ b ≠ b) : a = b ∨ a = c := by duper

theorem elimResolvedLitTest2 {t : Type} (a : t) (b : t) (c : t)
  (h : b ≠ b ∨ a = b ∨ a ≠ a ∨ a = c ∨ b ≠ b ∨ c ≠ c) : a = b ∨ a = c := by duper

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
  by duper

theorem equalityFactoringTest2 {α : Type} (s t u v : α) 
  (h1 : s = t ∨ u = s) : t ≠ u ∨ u = s :=
  by duper

set_option trace.Prover.debug true

theorem equalityFactoringTest3 {α : Type} (s t v : α)
  (h1 : s = t ∨ t = v) : s ≠ v ∨ t = v :=
  by duper

/-
  Note to self: The only difference between equalityFactoringTest3 and equalityFactoringTest4 is the order of s t and v as arguments. This fact influences
  something in how they are compared to each other in Order.lean (I think it has an effect on VarBalance), which is why equalityFactoringTest3 uses
  equality_factoring_soundness2 and equalityFactoringTest4 uses equality_factoring_soundness4
-/
theorem equalityFactoringTest4 {α : Type} (v t s : α)
  (h1 : s = t ∨ t = v) : s ≠ v ∨ t = v :=
  by duper

theorem equalityFactoringTest5 {α : Type} (s t u v : α)
  (h1 : s = t ∨ u = t) : s ≠ u ∨ u = t :=
  by duper

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