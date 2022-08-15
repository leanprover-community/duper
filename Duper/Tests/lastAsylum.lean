import Duper.TPTP
import Duper.Tactic

-- inhabitants
axiom Inhab : Type

axiom Fether   : Inhab
axiom Tarr     : Inhab
axiom Jones    : Inhab
axiom Smith    : Inhab
axiom A        : Inhab
axiom B        : Inhab
axiom C        : Inhab
axiom D        : Inhab
axiom Sane     : Inhab → Prop
axiom Doctor   : Inhab → Prop
axiom Peculiar : Inhab → Prop
axiom Special  : Inhab → Prop
axiom bf       : Inhab → Inhab

axiom ax1 : ∀ x, Peculiar x ↔ (Sane x ↔ ¬ Doctor x)
axiom ax2 : ∀ x, Special x ↔ ∀ y, (¬ Doctor y ↔ (Sane y ↔ Peculiar x))
axiom ax3 : ∀ x y, (Sane x ↔ Special y) → (Sane (bf x) ↔ ¬ Doctor y)
axiom ax4 : Sane Tarr ↔ ∀ x, Doctor x → Sane x
axiom ax5 : Sane Fether ↔ ∀ x, ¬ Doctor x → ¬ (Sane x)
axiom ax6 : Sane Fether ↔ Sane Tarr

example
  (ax1 : ∀ x, Peculiar x ↔ (Sane x ↔ ¬ Doctor x))
  (ax2 : ∀ x, Special x ↔ ∀ y, (¬ Doctor y ↔ (Sane y ↔ Peculiar x)))
  (ax3 : ∀ x y, (Sane x ↔ Special y) → (Sane (bf x) ↔ ¬ Doctor y))
  (ax4 : Sane Tarr ↔ ∀ x, Doctor x → Sane x)
  (ax5 : Sane Fether ↔ ∀ x, ¬ Doctor x → ¬ (Sane x))
  (ax6 : Sane Fether ↔ Sane Tarr)
  : False := sorry --by duper -- timeout

theorem asylum_one
  (h1 : Sane Jones ↔ Doctor Smith)
  (h2 : Sane Smith ↔ ¬ Doctor Jones)
  : ∃ x : Inhab, (¬ Sane (x) ∧ Doctor (x)) ∨ (Sane (x) ∧ ¬ Doctor (x)) := by duper

#print axioms asylum_one

theorem asylum_seven
  (h1 : Sane A ↔ ¬ Sane B)
  (h2 : Sane B ↔ Doctor A)
  : (¬ Sane A ∨ Doctor A) ∨ (Sane A ∧ ¬ Doctor A) := by duper

#print axioms asylum_seven

theorem asylum_nine
  (h1 : Sane A ↔ (Sane B ↔ Sane C))
  (h2 : Sane B ↔ (Sane A ↔ Sane D))
  (h3 : Sane C ↔ ¬ (Doctor C ∧ Doctor D))
  (h4 : A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) :
  (∃ x : Inhab, Sane x ∧ ¬ Doctor x) ∨
  (∃ x : Inhab, ∃ y : Inhab, x ≠ y ∧ (¬ Sane x) ∧ Doctor x ∧ (¬ Sane y) ∧ Doctor y) :=
  by duper

#print axioms asylum_nine
#print asylum_nine