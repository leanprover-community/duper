import Duper.Tactic
import Duper.TPTP

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