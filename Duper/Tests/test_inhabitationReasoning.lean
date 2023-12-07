import Duper.Tactic
import Duper.TPTP

set_option inhabitationReasoning true
set_option trace.duper.typeInhabitationReasoning.debug true
set_option throwPortfolioErrors true

theorem optionTest1 (t : Type) (f : Option t) : ∃ x : Option t, True := by duper

theorem optionTest2 : ∀ t : Type, ∃ x : Option t, True := by duper

theorem nonemptyHypTest (t : Type) (eh : Nonempty t = True ∧ True) (h : ∀ x : t, False ≠ False) : False := by duper [eh, h]

-- Needs to synthesize Inhabited (Fin x)
theorem finTest (x : Nat) (f : Fin x → Fin x)
  (h : ∃ y : Fin x, ∀ z : Fin x, (f y ≠ y) ∧ (f z = y)) : False := by duper [h]

-- Needs to synthesize Inhabited (Fin default)
set_option trace.duper.saturate.debug true in
theorem finTest2
  (h : ∀ x : Nat, ∃ f : Fin x → Fin x, ∃ y : Fin x, ∀ z : Fin x, (f y ≠ y) ∧ (f z = y)) : False := by
  duper [h] {portfolioInstance := 7}

-- Needs to synthesize Inhabited (Fin [anonymous]) (pretty sure [anonymous] is a skolem var)
set_option trace.duper.saturate.debug true in
theorem finTest3 (mult_Nats : ∃ y : Nat, y ≠ 0)
  (h : ∀ x : Nat, x ≠ 0 → ∃ f : Fin x → Fin x, ∃ y : Fin x, ∀ z : Fin x, (f y ≠ y) ∧ (f z = y)) : False := by
  duper [h]

-- Needs to synthesize Inhabited person
set_option trace.duper.proofReconstruction true in
theorem barber_paradox1 {person : Type} {shaves : person → person → Prop}
  (h : ∃ b : person, ∀ p : person, (shaves b p ↔ (¬ shaves p p))) : False :=
  by duper [h]

theorem letDecBug {t : Type} (h : (∀ p : t, p = p) = False) : False :=
  by duper [h]

-- Interesting type inhabited examples (they require more advanced reasoning about type inhabitation)
example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper

set_option trace.duper.saturate.debug true in
example : ∃ (A : Type) (B : A → Type) (f : ∀ (a : A), B a) (x : A), (f x = f x) = True :=
  by duper

set_option trace.duper.proofReconstruction true in
example : ((∀ (A : Type) (f : Nat → A) (x : Nat), f x = f x) = True) :=
  by duper
