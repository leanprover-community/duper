import Duper.Tactic
import Duper.TPTP

-- Tests where the prover should saturate

axiom a : Nat
axiom b : Nat
axiom c : Nat
axiom d : Nat
axiom f : Nat → Nat

theorem test0018saturate (a1 a2 a3 a4 a5 a6 : Nat)
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
: False := by duper [*]

-- Tests where duper should time out
-- This example is intended to test duper's ability of
--   handling dependent types. It should fail with
--   "deterministic timeout".
-- If it fails in any other way, it's an indication of a bug.

set_option trace.Meta.debug true in
def rec₁ : False := by
  duper [Nat.rec]