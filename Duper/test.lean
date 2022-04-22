import Duper.Tactic

-- set_option trace.Meta.debug true
-- set_option trace.Prover.saturate true
set_option trace.Prover.debug true
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
set_option trace.Prover.saturate true
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