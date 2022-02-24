import Duper.Tactic

-- set_option trace.Meta.debug true
-- set_option trace.Prover.saturate true
-- set_option trace.Prover.debug true
-- set_option trace.Rule.debug true
-- set_option pp.all true

constant a : Nat
constant b : Nat
constant c : Nat
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



theorem test 
(div_self : ∀ x, div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), div x y = mul x (inv y)) :
∀ (x y : Nat), div (add x y) y = add (div x y) one := by duper

#print test
#print axioms test

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


-- example (a : Nat)
-- (h1 : ∀ (x : Nat), f x = a)
-- (h2 : ¬ ∀ (x : Nat), f x = a)
-- : False := by
--   duper
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry
--   · sorry

-- set_option maxHeartbeats 500
-- example 
-- (neg_conj : ¬ ∀ (x y : Nat), mul (add x y) (inv y) = add (mul x (inv y)) (mul y (inv y)))
-- (add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
-- (div_def : ∀ (x y : Nat), div x y = mul x (inv y))
-- : False := by
--   duper
--   all_goals
--     sorry

-- example (h : ∀ (x y : Nat), y ≠ x)
-- : False := by
--   duper
--   all_goals
--     sorry

-- theorem eq_True : h = True ↔ h := by
--   apply Iff.intro 
--   · intro hh
--     rw [hh]
--     exact True.intro
--   · intro hh
--     apply propext
--     apply Iff.intro
--     exact fun _ => True.intro
--     exact fun _ => hh

-- example  (h : ∀ x, f x ≠ b ∨ f x ≠ b)  (h : f c = b)
-- : False := by
--   duper
--   done



-- example  (h : a = b) (h : a ≠ b)
-- : False := by
--   duper
--   · exact (fun h => h rfl)
--   · intro h
--     rw [h]
--     exact (fun g => g)
--   · exact eq_True.1
--   · exact eq_True.2 (by assumption)
--   · exact eq_True.1
--   · exact eq_True.2 (by assumption)
