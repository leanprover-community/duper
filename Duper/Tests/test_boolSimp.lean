import Duper.Tactic
import Duper.TPTP

-- Note: These tests only effectively test boolSimp when identBoolHoist is disabled
set_option trace.Rule.boolSimp true

theorem boolSimpRule1Test (p : Prop) (h : (p ∨ p ∨ p ∨ p) = q) : p = q :=
  by duper

theorem boolSimpRule2Test (p q : Prop) (h : (¬p ∨ p) = q) : q :=
  by duper

theorem boolSimpRule2SymTest (p q : Prop) (h : (p ∨ ¬p) = q) : q :=
  by duper

theorem boolSimpRule3Test (p q : Prop) (h : (p ∨ True) = q) : q :=
  by duper

theorem boolSimpRule3SymTest (p q : Prop) (h : (True ∨ p) = q) : q :=
  by duper

theorem boolSimpRule4Test (p q : Prop) (h : (p ∨ False) = (q ∨ False)) : p = q :=
  by duper

theorem boolSimpRule4SymTest (p q : Prop) (h : (False ∨ p) = (False ∨ q)) : p = q :=
  by duper

theorem boolSimpRule5Test (p q : Prop) (h : p = (q = q)) : p :=
  by duper

theorem boolSimpRule6Test (p q : Prop) (h : (p = True) = (q = True)) : p = q :=
  by duper

theorem boolSimpRule6SymTest (p q : Prop) (h : (True = p) = (True = q)) : p = q :=
  by duper

theorem boolSimpRule7Test (p q : Prop) (h : p = Not False) : p :=
  by duper

theorem boolSimpRule8Test (p : Prop) (h : (p ∧ p ∧ p ∧ p) = q) : p = q :=
  by duper

theorem boolSimpRule9Test (p q : Prop) (h : (¬p ∧ p) = q) : ¬q :=
  by duper

theorem boolSimpRule9SymTest (p q : Prop) (h : (p ∧ ¬p) = q) : ¬q :=
  by duper

theorem boolSimpRule10Test (p q : Prop) (h : (p ∧ True) = q) : p = q :=
  by duper

theorem boolSimpRule10SymTest (p q : Prop) (h : (True ∧ p) = q) : p = q :=
  by duper

theorem boolSimpRule11Test (p q : Prop) (h : (p ∧ False) = q) : ¬q :=
  by duper

theorem boolSimpRule11SymTest (p q : Prop) (h : (False ∧ p) = q) : ¬q :=
  by duper

theorem boolSimpRule12Test (p q : Prop) (h : p = (q ≠ q)) : ¬p :=
  by duper

theorem boolSimpRule13Test (p q : Prop) (h : (p = False) = (q = False)) : p = q :=
  by duper

theorem boolSimpRule13SymTest (p q : Prop) (h : (False = p) = (False = q)) : p = q :=
  by duper

theorem boolSimpRule14Test (p q : Prop) (h : p = Not True) : ¬p :=
  by duper

theorem boolSimpRule15Test (p q : Prop) (h : (¬¬p) = q) : p = q :=
  by duper

theorem boolSimpRule16Test (p q : Prop) (h : (True → p) = q) : p = q :=
  by duper

theorem boolSimpRule17Test (p q : Prop) (h : (False → p) = q) : q :=
  by duper

theorem boolSimpRule18Test (p q : Prop) (h : (p → False) = (q → False)) : p = q :=
  by duper

theorem boolSimpRule19Test (p q : Prop) (h : (p → True) = q) : q :=
  by duper

theorem boolSimpRule19Test2 (α) (q : Prop) (h : (∀ _ : α, True) = q) : q :=
  by duper

theorem boolSimpRule20Test (p q : Prop) (h : (p → ¬p) = (q → ¬q)) : p = q :=
  by duper

theorem boolSimpRule21Test (p q : Prop) (h : (¬p → p) = (¬q → q)) : p = q :=
  by duper

theorem boolSimpRule22Test (p q : Prop) (h : (p → p) = q) : q :=
  by duper

theorem boolSimpRule23Test (f : Prop → Prop) (q : Prop) (hq : q) (h : (∀ p : Prop, f p) = q) : f True :=
  by duper

theorem boolSimpRule24Test (f : Prop → Prop) (q : Prop) (hq : q) (h : (∃ p : Prop, f p) = q) : (f True) ∨ (f False) :=
  by duper

theorem boolSimpRule25Test (p q r : Prop) (h : (p → ¬q → q → p → False) = r) : r :=
  by duper

theorem boolSimpRule26Test (a b c shared x y z r : Prop) (h : (a → b → shared → c → (x ∨ shared ∨ y ∨ z)) = r) : r :=
  by duper

theorem boolSimpRule26TestDep₁ (a b y z r : Prop) (dep : a → Prop) (h : ((x : a) → b → dep x → (dep x ∨ y ∨ z)) = r) : r :=
  by duper

theorem boolSimpRule27Test (a b c shared x y z r : Prop) (h : ((a ∧ b ∧ shared ∧ c) → (x ∨ shared ∨ y ∨ z)) = r) : r :=
  by duper

theorem boolSimpRule27TestDep₂ (a b c y z r : Prop) (f : a ∧ b ∧ c → Prop) (h : ((x : a ∧ b ∧ c) → (y ∨ f x ∨ c ∨ z)) = r) : r :=
  by duper

theorem boolSimpRule28Test (p q r : Prop) (h : (p ↔ r) = (q ↔ r)) : p = q :=
  by duper


-- Negative tests

namespace Negative

axiom f.{u} : Sort u → Nat

def neg₁ : (f (Nat → Nat) = f (Nat → Nat)) := by duper

-- A positive example
def pos₁ : (f (Nat → False) = f False) := by duper

axiom g.{u} : ∀ (α : Sort u), α → Nat

-- These two examples fail when boolSimp is enabled, but I don't think that adding guards to
-- boolSimp will fix that, since both instances in which boolSimp is applied are reasonable
-- (∀ _ : Nat, True) in general should be turned into True, as should (True → True)
def neg₂ : g (Nat → True) (fun _ => True.intro) = g (Nat → True) (fun _ => True.intro) :=
  by duper

def neg3 : g (True → True) (fun _ => True.intro) = g (True → True) (fun _ => True.intro) :=
  by duper

end Negative