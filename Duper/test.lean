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
--Iff clausification tests
set_option trace.Simp.debug true

theorem iffClausificationTest1 {p : Prop} {q : Prop} (h : p ↔ q) : (p → q) ∧ (q → p) :=
  by duper

theorem iffClausificationTest2 {p : Prop} {q : Prop} (h : ¬(p ↔ q)) : (p → ¬q) ∧ (q → ¬p) :=
  by duper

#print iffClausificationTest1
#print iffClausificationTest2
#print axioms iffClausificationTest1
#print axioms iffClausificationTest2 --NOTE: Currently, iffClausificationTest2 uses sorryAx because clausificationStepLit in Clausification.lean does not
                                     --yet produce proof reconstructions for Prop inequalities 

set_option trace.Simp.debug false
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

#print barber_paradox1
#print axioms barber_paradox1
#print axioms barber_paradox2
#print axioms barber_paradox3
#print axioms barber_paradox4

--inline tests are to expose the issues that arise when we try to call duper in the midst of a larger tactic-style proof
theorem barber_paradox_inline1 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    -- duper gives the output: "unknown metavariable '?_uniq.53070'"
    sorry

theorem barber_paradox_inline2 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    have h'_b := h' b
    -- duper gives the output: "unknown metavariable '?_uniq.53173'". Duper also gives a bunch of panic statements about precCompare
    sorry

theorem barber_paradox_inline3 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := by
  cases h with
  | intro b h' =>
    have h'_b := h' b
    clear h'
    --duper yields a bunch of PANIC statements in the output concerning [mdata noImplicitLambda:1 False] not begin implemented in precCompare in Duper.Order:151:10
    --duper then has a deterministic timeout given long enough (at superposition, though I don't think it matters)
    sorry

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