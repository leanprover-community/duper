import Duper.Tactic
import Duper.TPTP
import Auto.Tactic

-- This file is for documenting bugs in Duper's current invocation of the monomorphization procedure.

-- Note: This example fails if inhabitation reasoning is enabled (see bug 5 in bugs.lean) or if monomorphization is enabled
example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper {portfolioInstance := 6, inhabitationReasoning := false}

example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper {portfolioInstance := 1, inhabitationReasoning := false}

-- allNative_direct :: Cannot find external proof of nonempty #0
tptp SEU123 "../TPTP-v8.0.0/Problems/SEU/SEU123+1.p"
  by duper [*] {portfolioInstance := 6}

tptp SEU123_new "../TPTP-v8.0.0/Problems/SEU/SEU123+1.p"
  by duper [*] {portfolioInstance := 1}

-- unexpected bound variable #0
theorem boolSimpRule27TestDep₁ (a b c y z r : Prop) (f : a ∧ b ∧ c → Prop) (h : ((x : a ∧ b ∧ c) → (y ∨ f x ∨ c ∨ z)) = r) : r :=
  by duper [*] {portfolioInstance := 6}

theorem boolSimpRule27TestDep₁_new (a b c y z r : Prop) (f : a ∧ b ∧ c → Prop) (h : ((x : a ∧ b ∧ c) → (y ∨ f x ∨ c ∨ z)) = r) : r :=
  by duper [*] {portfolioInstance := 1}

namespace NegativeBoolSimpTests

axiom f.{u} : Sort u → Nat

-- reifTermCheckType :: LamTerm (¬ ((!0 (∀ x0 : Nat, !1)) = (!0 (∀ x0 : Nat, !1)))) is not type correct
def neg₁ : (f (Nat → Nat) = f (Nat → Nat)) := by duper {portfolioInstance := 6}

def neg₁_new : (f (Nat → Nat) = f (Nat → Nat)) := by duper {portfolioInstance := 1}

end NegativeBoolSimpTests

axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

-- prover saturated
def unitst₁ : f.{max u v} (Sort (max u v)) ∧ f.{v} (Sort v) := by
  duper [ftrue] {portfolioInstance := 6}

def unitst₁_new : f.{max u v} (Sort (max u v)) ∧ f.{v} (Sort v) := by
  duper [ftrue] {portfolioInstance := 1}

axiom fmoretrue.{u} : ∀ (x : Type u), f x

-- prover saturated
def unitst₂ : ∀ (x : Type v), f x := by
  duper [fmoretrue] {portfolioInstance := 6}

def unitst₂_new : ∀ (x : Type v), f x := by
  duper [fmoretrue] {portfolioInstance := 1}

axiom exftrue.{u} : ∃ (x : Type u), f x

-- prover saturated
def skuniverse.{u} : ∃ (x : Type u), f x := by
  duper [exftrue] {portfolioInstance := 6}

def skuniverse_new.{u} : ∃ (x : Type u), f x := by
  duper [exftrue] {portfolioInstance := 1}

-- prover saturated (presumably because monomorphization procedure doesn't use nonempty lemmas in the same way duper does)
example (h : Nonempty (α → β)) : (∀ n : Nat, ∀ a : α, ∃ b : β, True) = True :=
  by duper [h] {portfolioInstance := 6}

example (h : Nonempty (α → β)) : (∀ n : Nat, ∀ a : α, ∃ b : β, True) = True :=
  by duper [h] {portfolioInstance := 1}
