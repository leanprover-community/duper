import LeanHammer.Tactic

set_option trace.Meta.debug true
set_option trace.Prover.saturate true
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
constant p : Nat → Prop

-- example --(h : ∃ x, x ≠ c ∨ a = b) 
-- (h : ¬ ∃ x, x = f a ∨ ∀ x, ∃ y, y = f a ∧ x = b)-- (h :  c = b ∧ a = b) 
-- : False := by
--   prover
--   all_goals
--     sorry


theorem test 
(div_self : ∀ x, div x x = one)
(add_mul : ∀ (x y z : Nat), mul (add x y) z = add (mul x z) (mul y z))
(div_def : ∀ (x y : Nat), div x y = mul x (inv y))
(neg_conj : ¬ ∀ (x y : Nat), div (add x y) y = add (div x y) one)
: False := by prover

#print test

-- example (a : Nat)
-- (h1 : ∀ (x : Nat), f x = a)
-- (h2 : ¬ ∀ (x : Nat), f x = a)
-- : False := by
--   prover
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
--   prover
--   all_goals
--     sorry

-- example (h : ∀ (x y : Nat), y ≠ x)
-- : False := by
--   prover
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
--   prover
--   done



-- example  (h : a = b) (h : a ≠ b)
-- : False := by
--   prover
--   · exact (fun h => h rfl)
--   · intro h
--     rw [h]
--     exact (fun g => g)
--   · exact eq_True.1
--   · exact eq_True.2 (by assumption)
--   · exact eq_True.1
--   · exact eq_True.2 (by assumption)
