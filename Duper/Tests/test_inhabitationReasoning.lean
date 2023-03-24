import Duper.Tactic
import Duper.TPTP

set_option trace.typeInhabitationReasoning.debug true

theorem optionTest1 (t : Type) (f : Option t) : ∃ x : Option t, True := by duper

theorem optionTest2 : ∀ t : Type, ∃ x : Option t, True := by duper

theorem nonemptyHypTest (t : Type) (eh : Nonempty t = True ∧ True) (h : ∀ x : t, False ≠ False) : False := by duper

-- Needs to synthesize Inhabited (Fin x)
theorem finTest (x : Nat) (f : Fin x → Fin x)
  (h : ∃ y : Fin x, ∀ z : Fin x, (f y ≠ y) ∧ (f z = y)) : False := by duper

-- Needs to synthesize Inhabited (Fin default)
theorem finTest2
  (h : ∀ x : Nat, ∃ f : Fin x → Fin x, ∃ y : Fin x, ∀ z : Fin x, (f y ≠ y) ∧ (f z = y)) : False := by duper

-- Needs to synthesize Inhabited (Fin [anonymous]) (pretty sure [anonymous] is a skolem var)
theorem finTest3 (mult_Nats : ∃ y : Nat, y ≠ 0)
  (h : ∀ x : Nat, x ≠ 0 → ∃ f : Fin x → Fin x, ∃ y : Fin x, ∀ z : Fin x, (f y ≠ y) ∧ (f z = y)) : False := by duper

-- Needs to synthesize Inhabited person
theorem barber_paradox1 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False := 
  by duper

-- Currently causes the output: "(kernel) let-declaration type mismatch 'clause.5.0'"
theorem letDecBug {t : Type} (h : (∀ p : t, p = p) = False) : False := 
  by duper

-- Interesting type inhabited examples (they require more advanced reasoning about type inhabitation)
example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper -- Fails because we currently do not infer that A is nonempty from the fact that B and B → A are nonempty

example : ∃ (A : Type) (B : A → Type) (f : ∀ (a : A), B a) (x : A), (f x = f x) = True :=
  by duper