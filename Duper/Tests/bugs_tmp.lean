import Duper.TPTP
import Duper.Tactic

theorem boolSimpRule1Test (p : Prop) (h : (p ∨ p ∨ p ∨ p) = q) : p = q :=
  by duper

theorem boolSimpRule2Test (p q : Prop) (h : (¬p ∨ p) = q) : q :=
  by duper