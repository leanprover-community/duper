import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction
import Duper.Util.Misc

set_option linter.unusedVariables false

namespace Duper

open Lean
open Lean.Meta
open RuleM
open Meta
open SimpResult
open Comparison

initialize Lean.registerTraceClass `duper.rule.boolSimp

/--
  Rules 1 through 15 are from Leo-III. Rules 16 through 22 and 25 through 27 are from "Superposition with
  First-Class Booleans and Inprocessing Clausification." Rules 23, 24, and 28 were made just for duper.
  Rules with the `b` suffix operate on `Bool`, rules without the `b` suffix operate on `Prop`.
-/
inductive BoolSimpRule
  | rule1 -- s ∨ s ↦ s
  | rule1b -- s || s ↦ s
  | rule2 -- ¬s ∨ s ↦ True
  | rule2b -- !s || s ↦ true
  | rule2Sym -- s ∨ ¬s ↦ True
  | rule2bSym -- s || !s ↦ true
  | rule3 -- s ∨ True ↦ True
  | rule3b -- s || true ↦ true
  | rule3Sym -- True ∨ s ↦ True
  | rule3bSym -- true || s ↦ true
  | rule4 -- s ∨ False ↦ s
  | rule4b -- s || false ↦ s
  | rule4Sym -- False ∨ s ↦ s
  | rule4bSym -- false || s ↦ s
  | rule5 -- s = s ↦ True
  | rule5b -- s == s ↦ true
  | rule6 -- s = True ↦ s
  | rule6b -- s == true ↦ s
  | rule6Sym -- True = s ↦ s
  | rule6bSym -- true == s ↦ s
  | rule7 -- Not False ↦ True
  | rule7b -- !false ↦ true
  | rule8 -- s ∧ s ↦ s
  | rule8b -- s && s ↦ s
  | rule9 -- ¬s ∧ s ↦ False
  | rule9b -- !s && s ↦ false
  | rule9Sym -- s ∧ ¬s ↦ False
  | rule9bSym -- s && !s ↦ false
  | rule10 -- s ∧ True ↦ s
  | rule10b -- s && true ↦ s
  | rule10Sym -- True ∧ s ↦ s
  | rule10bSym -- true && s ↦ s
  | rule11 -- s ∧ False ↦ False
  | rule11b -- s && false ↦ false
  | rule11Sym -- False ∧ s ↦ False
  | rule11bSym -- false && s ↦ false
  | rule12 -- s ≠ s ↦ False
  | rule12b -- s != s ↦ false
  | rule13 -- s = False ↦ ¬s
  | rule13b -- s == false ↦ !s
  | rule13Sym -- False = s ↦ ¬s
  | rule13bSym -- false == s ↦ !s
  | rule14 -- Not True ↦ False
  | rule14b -- !true ↦ false
  | rule15 -- ¬¬s ↦ s
  | rule15b -- !!s ↦ s
  | rule16 -- True → s ↦ s
  | rule17 -- False → s ↦ True
  | rule18 -- s → False ↦ ¬s
  | rule19 -- s → True ↦ True (we generalize this to (∀ _ : α, True) ↦ True)
  | rule20 -- s → ¬s ↦ ¬s
  | rule21 -- ¬s → s ↦ s
  | rule22 -- s → s ↦ True
  | rule23 -- ∀ p : Prop, f(p) ↦ f True ∧ f False
  | rule23b -- ∀ b : Bool, f(b) ↦ f true ∧ f false (assuming `f : Bool → Prop`)
  | rule24 -- ∃ p : Prop, f(p) ↦ f True ∨ f False
  | rule24b -- ∃ b : Bool, f(b) ↦ f true ∨ f false (assuming `f : Bool → Prop`)
  | rule25 -- (s1 → s2 → ... → sn → v) ↦ True if there exists i and j such that si = ¬sj
  | rule26 -- (s1 → s2 → ... → sn → v1 ∨ ... ∨ vm) ↦ True if there exists i and j such that si = vj
  | rule27 -- (s1 ∧ s2 ∧ ... ∧ sn → v1 ∨ ... ∨ vm) ↦ True if there exists i and j such that si = vj
  | rule28 -- s1 ↔ s2 ↦ s1 = s2
deriving Repr

open BoolSimpRule

def BoolSimpRule.format (boolSimpRule : BoolSimpRule) : MessageData :=
  match boolSimpRule with
  | rule1 => m!"rule1"
  | rule1b => m!"rule1b"
  | rule2 => m!"rule2"
  | rule2b => m!"rule2b"
  | rule2Sym => m!"rule2Sym"
  | rule2bSym => m!"rule2bSym"
  | rule3 => m!"rule3"
  | rule3b => m!"rule3b"
  | rule3Sym => m!"rule3Sym"
  | rule3bSym => m!"rule3bSym"
  | rule4 => m!"rule4"
  | rule4b => m!"rule4b"
  | rule4Sym => m!"rule4Sym"
  | rule4bSym => m!"rule4bSym"
  | rule5 => m!"rule5"
  | rule5b => m!"rule5b"
  | rule6 => m!"rule6"
  | rule6b => m!"rule6b"
  | rule6Sym => m!"rule6Sym"
  | rule6bSym => m!"rule6bSym"
  | rule7 => m!"rule7"
  | rule7b => m!"rule7b"
  | rule8 => m!"rule8"
  | rule8b => m!"rule8b"
  | rule9 => m!"rule9"
  | rule9b => m!"rule9b"
  | rule9Sym => m!"rule9Sym"
  | rule9bSym => m!"rule9bSym"
  | rule10 => m!"rule10"
  | rule10b => m!"rule10b"
  | rule10Sym => m!"rule10Sym"
  | rule10bSym => m!"rule10bSym"
  | rule11 => m!"rule11"
  | rule11b => m!"rule11b"
  | rule11Sym => m!"rule11Sym"
  | rule11bSym => m!"rule11bSym"
  | rule12 => m!"rule12"
  | rule12b => m!"rule12b"
  | rule13 => m!"rule13"
  | rule13b => m!"rule13b"
  | rule13Sym => m!"rule13Sym"
  | rule13bSym => m!"rule13bSym"
  | rule14 => m!"rule14"
  | rule14b => m!"rule14b"
  | rule15 => m!"rule15"
  | rule15b => m!"rule15b"
  | rule16 => m!"rule16"
  | rule17 => m!"rule17"
  | rule18 => m!"rule18"
  | rule19 => m!"rule19"
  | rule20 => m!"rule20"
  | rule21 => m!"rule21"
  | rule22 => m!"rule22"
  | rule23 => m!"rule23"
  | rule23b => m!"rule23b"
  | rule24 => m!"rule24"
  | rule24b => m!"rule24b"
  | rule25 => m!"rule25"
  | rule26 => m!"rule26"
  | rule27 => m!"rule27"
  | rule28 => m!"rule28"

instance : ToMessageData BoolSimpRule := ⟨BoolSimpRule.format⟩

theorem rule1Theorem (p : Prop) : (p ∨ p) = p := by simp
theorem rule1bTheorem (b : Bool) : (b || b) = b := by simp
theorem rule2Theorem (p : Prop) : (¬p ∨ p) = True := by
  apply @Classical.byCases p
  . intro hp
    apply eq_true
    exact Or.intro_right _ hp
  . intro hnp
    apply eq_true
    exact Or.intro_left _ hnp
theorem rule2bTheorem (b : Bool) : (!b || b) = true := by simp
theorem rule2SymTheorem (p : Prop) : (p ∨ ¬p) = True := by
  by_cases h : p
  . apply eq_true
    exact Or.intro_left _ h
  . apply eq_true
    exact Or.intro_right _ h
theorem rule2bSymTheorem (b : Bool) : (b || !b) = true := by simp
theorem rule3Theorem (p : Prop) : (p ∨ True) = True := by simp
theorem rule3bTheorem (b : Bool) : (b || true) = true := by simp
theorem rule3SymTheorem (p : Prop) : (True ∨ p) = True := by simp
theorem rule3bSymTheorem (b : Bool) : (true || b) = true := by simp
theorem rule4Theorem (p : Prop) : (p ∨ False) = p := by simp
theorem rule4bTheorem (b : Bool) : (b || false) = b := by simp
theorem rule4SymTheorem (p : Prop) : (False ∨ p) = p := by simp
theorem rule4bSymTheorem (b : Bool) : (false || b) = b := by simp
theorem rule5Theorem (p : α) : (p = p) = True := by simp
theorem rule5bTheorem (b : Bool) : (b == b) = true := by simp
theorem rule6Theorem (p : Prop) : (p = True) = p := by simp
theorem rule6bTheorem (b : Bool) : (b == true) = b := by simp
theorem rule6SymTheorem (p : Prop) : (True = p) = p := by simp
theorem rule6bSymTheorem (b : Bool) : (true == b) = b := by simp
theorem rule7Theorem : Not False = True := by simp
theorem rule7bTheorem : (!false) = true := by simp
theorem rule8Theorem (p : Prop) : (p ∧ p) = p := by simp
theorem rule8bTheorem (b : Bool) : (b && b) = b := by simp
theorem rule9Theorem (p : Prop) : (¬p ∧ p) = False := by simp
theorem rule9bTheorem (b : Bool) : (!b && b) = false := by simp
theorem rule9SymTheorem (p : Prop) : (p ∧ ¬p) = False := by simp
theorem rule9bSymTheorem (b : Bool) : (b && !b) = false := by simp
theorem rule10Theorem (p : Prop) : (p ∧ True) = p := by simp
theorem rule10bTheorem (b : Bool) : (b && true) = b := by simp
theorem rule10SymTheorem (p : Prop) : (True ∧ p) = p := by simp
theorem rule10bSymTheorem (b : Bool) : (true && b) = b := by simp
theorem rule11Theorem (p : Prop) : (p ∧ False) = False := by simp
theorem rule11bTheorem (b : Bool) : (b && false) = false := by simp
theorem rule11SymTheorem (p : Prop) : (False ∧ p) = False := by simp
theorem rule11bSymTheorem (b : Bool) : (false && b) = false := by simp
theorem rule12Theorem (p : α) : (p ≠ p) = False := by simp
theorem rule12bTheorem (b : Bool) : (b != b) = false := by simp
theorem rule13Theorem (p : Prop) : (p = False) = ¬p := by simp
theorem rule13bTheorem (b : Bool) : (b == false) = !b := by simp
theorem rule13SymTheorem (p : Prop) : (False = p) = ¬p := by simp
theorem rule13bSymTheorem (b : Bool) : (false == b) = !b := by simp
theorem rule14Theorem : Not True = False := by simp
theorem rule14bTheorem : (!true) = false := by simp
theorem rule15Theorem (p : Prop) : (¬¬p) = p := by rw [Classical.not_not]
theorem rule15bTheorem (b : Bool) : (!!b) = b := by simp
theorem rule16Theorem (p : Prop) : (True → p) = p := by simp
theorem rule17Theorem (p : Prop) : (False → p) = True := by simp
theorem rule18Theorem (p : Prop) : (p → False) = ¬p := by rfl
theorem rule19Theorem (α) : (∀ _ : α, True) = True := by simp
theorem rule20Theorem (p : Prop) : (p → ¬p) = ¬p := by simp
theorem rule21Theorem (p : Prop) : (¬p → p) = p := by
  by_cases h : p
  . rw [eq_true h]
    simp
  . rw [eq_false h]
    simp
theorem rule22Theorem (p : Prop) : (p → p) = True := by simp
theorem rule23Theorem (f : Prop → Prop) : (∀ p : Prop, f p) = (f True ∧ f False) := by
  by_cases h : ∀ p : Prop, f p
  . rw [eq_true h]
    apply Eq.symm
    apply eq_true
    constructor
    . exact h True
    . exact h False
  . rw [eq_false h]
    apply Eq.symm
    apply eq_false
    intro h2
    have h3 : (∀ p : Prop, f p) := by
      intro p
      by_cases hp : p
      . rw [eq_true hp]
        exact h2.1
      . rw [eq_false hp]
        exact h2.2
    exact h h3
theorem rule23bTheorem (f : Bool → Prop) : (∀ b : Bool, f b) = (f true ∧ f false) := by
  by_cases h : ∀ b : Bool, f b
  . rw [eq_true h]
    apply Eq.symm
    apply eq_true
    constructor
    . exact h True
    . exact h False
  . rw [eq_false h]
    apply Eq.symm
    apply eq_false
    intro h2
    have h3 : (∀ b : Bool, f b) := by
      intro b
      by_cases hb : b
      . rw [hb]
        exact h2.1
      . rw [Bool.not_eq_true] at hb
        rw [hb]
        exact h2.2
    exact h h3
theorem rule24Theorem (f : Prop → Prop) : (∃ p : Prop, f p) = (f True ∨ f False) := by
  by_cases h : ∃ p : Prop, f p
  . rw [eq_true h]
    apply Eq.symm
    apply eq_true
    cases h with
    | intro p h =>
      cases Classical.propComplete p with
      | inl p_eq_true =>
        rw [p_eq_true] at h
        exact Or.inl h
      | inr p_eq_false =>
        rw [p_eq_false] at h
        exact Or.inr h
  . rw [eq_false h]
    apply Eq.symm
    apply eq_false
    intro h2
    cases h2 with
    | inl f_true =>
      have h2 : ∃ p : Prop, f p := Exists.intro True f_true
      exact h h2
    | inr f_false =>
      have h2 : ∃ p : Prop, f p := Exists.intro False f_false
      exact h h2
theorem rule24bTheorem (f : Bool → Prop) : (∃ b : Bool, f b) = (f true ∨ f false) := by
  by_cases h : ∃ b : Bool, f b
  . rw [eq_true h]
    apply Eq.symm
    apply eq_true
    cases h with
    | intro b h =>
      by_cases hb : b
      . rw [hb] at h
        exact Or.inl h
      . simp only [Bool.not_eq_true] at hb
        rw [hb] at h
        exact Or.inr h
  . rw [eq_false h]
    apply Eq.symm
    apply eq_false
    intro h2
    simp only [not_exists] at h
    cases h2 with
    | inl f_true => exact h true f_true
    | inr f_false => exact h false f_false
theorem rule28Theorem (p1 : Prop) (p2 : Prop) : (p1 ↔ p2) = (p1 = p2) := by simp

partial def mkRule25Theorem (e : Expr) (counter : Nat) (i : Nat) (j : Nat) : MetaM Expr := do
  match e.consumeMData with
  | Expr.forallE _ t b _ =>
    let innerBody ← mkRule25Theorem b (counter + 1) i j
    return .lam Name.anonymous t innerBody default
  | _ =>
    let iIdx := (counter - 1) - i
    let jIdx := (counter - 1) - j
    return mkApp2 (mkConst ``False.elim [levelZero]) e (mkApp (Expr.bvar iIdx) (Expr.bvar jIdx))

/-- Assuming e has the form e1 ∨ e2 ∨ ... ∨ en, returns an array #[e1, e2, ... en].
    Note: If e has the form (e1a ∨ e1b) ∨ e2 ∨ ... en, then the disjunction (e1a ∨ e1b) will
    be considered e1 (and the disjunction e1 will not be broken down further). This decision is made
    to reflect the form of the disjunction assumed by ProofReconstruction.lean's `orIntro` -/
partial def getDisjunctiveGoals (e : Expr) (goals : Array Expr) : Array Expr :=
  match e.consumeMData with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 => getDisjunctiveGoals e2 (goals.push e1)
  | _ => goals.push e

partial def mkRule26Theorem (e : Expr) (counter : Nat) (i : Nat) (j : Nat) : MetaM Expr := do
  match e.consumeMData with
  | Expr.forallE _ t b _ =>
    let innerBody ← mkRule26Theorem b (counter + 1) i j
    return .lam Name.anonymous t innerBody default
  | _ =>
    let goals := getDisjunctiveGoals e #[]
    let iIdx := (counter - 1) - i
    orIntro goals j (Expr.bvar iIdx)

partial def mkRule27Theorem (e : Expr) (i : Nat) (j : Nat) : MetaM Expr := do
  match e.consumeMData with
  | Expr.forallE _ t b _ =>
    let hyps := getConjunctiveHypotheses t
    let goals := getDisjunctiveGoals b #[]
    let iHypProof ← andGet hyps i (Expr.bvar 0)
    let innerBody ← orIntro goals j iHypProof
    return .lam Name.anonymous t innerBody default
  | _ => throwError "{e} has the wrong shape for rule27"

/-- s ∨ s ↦ s -/
def applyRule1 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e1 == e2 then some e1
    else none
  | _ => none

/-- s || s ↦ s -/
def applyRule1b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) e1) e2 =>
    if e1 == e2 then some e1
    else none
  | _ => none

/-- ¬s ∨ s ↦ True -/
def applyRule2 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e1 == Expr.app (Expr.const ``Not []) e2 then some (mkConst ``True)
    else none
  | _ => none

/-- !s || s ↦ true -/
def applyRule2b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) e1) e2 =>
    if e1 == Expr.app (Expr.const ``not []) e2 then some (mkConst ``true)
    else none
  | _ => none

/-- s ∨ ¬s ↦ True -/
def applyRule2Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``Not []) e1 then some (mkConst ``True)
    else none
  | _ => none

/-- s || !s ↦ true -/
def applyRule2bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``not []) e1 then some (mkConst ``true)
    else none
  | _ => none

/-- s ∨ True ↦ True -/
def applyRule3 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) _) e2 =>
    if e2 == mkConst ``True then some (mkConst ``True)
    else none
  | _ => none

/-- s || true ↦ true -/
def applyRule3b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) _) e2 =>
    if e2 == mkConst ``true then some (mkConst ``true)
    else none
  | _ => none

/-- True ∨ s ↦ True -/
def applyRule3Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) _ =>
    if e1 == mkConst ``True then some (mkConst ``True)
    else none
  | _ => none

/-- true || s ↦ true -/
def applyRule3bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) e1) _ =>
    if e1 == mkConst ``true then some (mkConst ``true)
    else none
  | _ => none

/-- s ∨ False ↦ s -/
def applyRule4 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e2 == mkConst ``False then some e1
    else none
  | _ => none

/-- s || false ↦ s -/
def applyRule4b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) e1) e2 =>
    if e2 == mkConst ``false then
      some e1
    else none
  | _ => none

/-- False ∨ s ↦ s -/
def applyRule4Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e1 == mkConst ``False then some e2
    else none
  | _ => none

/-- false || s ↦ s -/
def applyRule4bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``or _) e1) e2 =>
    if e1 == mkConst ``false then some e2
    else none
  | _ => none

/-- s = s ↦ True -/
def applyRule5 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e1 == e2 then some (mkConst ``True)
    else none
  | _ => none

/-- s == s ↦ true -/
def applyRule5b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) e2 =>
    if e1 == e2 then some (mkConst ``true)
    else none
  | _ => none

/-- s = True ↦ s -/
def applyRule6 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e2 == mkConst ``True then some e1
    else none
  | _ => none

/-- s == true ↦ s -/
def applyRule6b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) e2 =>
    if e2 == mkConst ``true then some e1
    else none
  | _ => none

/-- True = s ↦ s -/
def applyRule6Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e1 == mkConst ``True then some e2
    else none
  | _ => none

/-- true == s ↦ s -/
def applyRule6bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) e2 =>
    if e1 == mkConst ``true then some e2
    else none
  | _ => none

/-- Not False ↦ True -/
def applyRule7 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) (Expr.const ``False _) => some (mkConst ``True)
  | _ => none

/-- !false ↦ True -/
def applyRule7b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``not _) (Expr.const ``false _) => some (mkConst ``true)
  | _ => none

/-- s ∧ s ↦ s -/
def applyRule8 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e1 == e2 then some e1
    else none
  | _ => none

/-- s && s ↦ s -/
def applyRule8b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) e1) e2 =>
    if e1 == e2 then some e1
    else none
  | _ => none

/-- ¬s ∧ s ↦ False -/
def applyRule9 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e1 == Expr.app (Expr.const ``Not []) e2 then some (mkConst ``False)
    else none
  | _ => none

/-- !s && s ↦ false -/
def applyRule9b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) e1) e2 =>
    if e1 == Expr.app (Expr.const ``not []) e2 then some (mkConst ``false)
    else none
  | _ => none

/-- s ∧ ¬s ↦ False -/
def applyRule9Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``Not []) e1 then some (mkConst ``False)
    else none
  | _ => none

/-- s && !s ↦ false -/
def applyRule9bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``not []) e1 then some (mkConst ``false)
    else none
  | _ => none

/-- s ∧ True ↦ s -/
def applyRule10 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e2 == mkConst ``True then some e1
    else none
  | _ => none

/-- s && true ↦ s -/
def applyRule10b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) e1) e2 =>
    if e2 == mkConst ``true then some e1
    else none
  | _ => none

/-- True ∧ s ↦ s -/
def applyRule10Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e1 == mkConst ``True then some e2
    else none
  | _ => none

/-- true && s ↦ s -/
def applyRule10bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) e1) e2 =>
    if e1 == mkConst ``true then some e2
    else none
  | _ => none

/-- s ∧ False ↦ False -/
def applyRule11 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) _) e2 =>
    if e2 == mkConst ``False then some (mkConst ``False)
    else none
  | _ => none

/-- s && false ↦ false -/
def applyRule11b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) _) e2 =>
    if e2 == mkConst ``false then some (mkConst ``false)
    else none
  | _ => none

/-- False ∧ s ↦ False -/
def applyRule11Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) _ =>
    if e1 == mkConst ``False then some (mkConst ``False)
    else none
  | _ => none

/-- false && s ↦ false -/
def applyRule11bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``and _) e1) _ =>
    if e1 == mkConst ``false then some (mkConst ``false)
    else none
  | _ => none

/-- s ≠ s ↦ False -/
def applyRule12 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _) e1) e2 =>
    if e1 == e2 then some (mkConst ``False)
    else none
  | _ => none

/-- s != s ↦ False -/
def applyRule12b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``bne _) _) _) e1) e2 =>
    if e1 == e2 then some (mkConst ``false)
    else none
  | _ => none

/-- s = False ↦ ¬s -/
def applyRule13 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e2 == mkConst ``False then some (mkApp (mkConst ``Not) e1)
    else none
  | _ => none

/-- s == false ↦ !s -/
def applyRule13b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) e2 =>
    if e2 == mkConst ``false then some (mkApp (mkConst ``not) e1)
    else none
  | _ => none

/-- False = s ↦ ¬s -/
def applyRule13Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e1 == mkConst ``False then some (mkApp (mkConst ``Not) e2)
    else none
  | _ => none

/-- false == s ↦ !s -/
def applyRule13bSym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) e2 =>
    if e1 == mkConst ``false then some (mkApp (mkConst ``not) e2)
    else none
  | _ => none

/-- Not True ↦ False -/
def applyRule14 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) (Expr.const ``True _) => some (mkConst ``False)
  | _ => none

/-- !true ↦ false -/
def applyRule14b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``not _) (Expr.const ``true _) => some (mkConst ``false)
  | _ => none

/-- ¬¬s ↦ s -/
def applyRule15 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.const ``Not _) e') => some e'
  | _ => none

/-- !!s ↦ s -/
def applyRule15b (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``not _) (Expr.app (Expr.const ``not _) e') => some e'
  | _ => none

/-- True → s ↦ s -/
def applyRule16 (e : Expr) : Option Expr :=
  match e with
  | Expr.forallE _ t b _ =>
    if t == mkConst ``True then some b
    else none
  | _ => none

/-- False → s ↦ True -/
def applyRule17 (e : Expr) : Option Expr :=
  match e with
  | Expr.forallE _ t _ _ =>
    if t == mkConst ``False then some (mkConst ``True)
    else none
  | _ => none

/-- s → False ↦ ¬s -/
def applyRule18 (e : Expr) : RuleM (Option Expr) := do
  match e with
  | Expr.forallE _ t b _ =>
    if b == mkConst ``False && (← inferType t).isProp then return some (mkApp (mkConst ``Not) t)
    else return none
  | _ => return none

/-- s → True ↦ True (we generalize this to (∀ _ : α, True) ↦ True) -/
def applyRule19 (e : Expr) : Option Expr := do
  match e with
  | Expr.forallE _ _ b _ =>
    if b == mkConst ``True then some (mkConst ``True)
    else none
  | _ => none

/-- s → ¬s ↦ ¬s -/
def applyRule20 (e : Expr) : Option Expr := do
  match e with
  | Expr.forallE _ t b _ =>
    if b == Expr.app (Expr.const ``Not []) t then some b
    else none
  | _ => none

/-- ¬s → s ↦ s -/
def applyRule21 (e : Expr) : Option Expr := do
  match e with
  | Expr.forallE _ t b _ =>
    if t == Expr.app (Expr.const ``Not []) b then some b
    else none
  | _ => none

/-- s → s ↦ True -/
def applyRule22 (e : Expr) : RuleM (Option Expr) := do
  match e with
  | Expr.forallE _ t b _ =>
    if t == b && (← inferType t).isProp then return some (mkConst ``True)
    else return none
  | _ => return none

/-- ∀ p : Prop, f(p) ↦ f(True) ∧ f(False) -/
def applyRule23 (e : Expr) : RuleM (Option Expr) := do
  match e with
  | Expr.forallE _ t b _ =>
    if t.isProp && (← inferType e).isProp then
      let bTrue := b.instantiate1 (mkConst ``True)
      let bFalse := b.instantiate1 (mkConst ``False)
      mkAppM ``And #[bTrue, bFalse]
    else return none
  | _ => return none

/-- ∀ b : Bool, f(b) ↦ f true ∧ f false (assuming `f : Bool → Prop`) -/
def applyRule23b (e : Expr) : RuleM (Option Expr) := do
  match e with
  | Expr.forallE _ t b _ =>
    if t == (mkConst ``Bool) && (← inferType e).isProp then
      let btrue := b.instantiate1 (mkConst ``true)
      let bfalse := b.instantiate1 (mkConst ``false)
      mkAppM ``And #[btrue, bfalse]
    else return none
  | _ => return none

/-- ∃ p : Prop, f(p) ↦ f True ∨ f False -/
def applyRule24 (e : Expr) : RuleM (Option Expr) := do
  match e with
  | Expr.app (Expr.app (Expr.const ``Exists _) t) b =>
    if t.isProp then
      let bTrue ← whnf $ mkApp b (mkConst ``True)
      let bFalse ← whnf $ mkApp b (mkConst ``False)
      mkAppM ``Or #[bTrue, bFalse]
    else return none
  | _ => return none

/-- ∃ b : Bool, f(b) ↦ f true ∨ f false (assuming `f : Bool → Prop`) -/
def applyRule24b (e : Expr) : RuleM (Option Expr) := do
  match e with
  | Expr.app (Expr.app (Expr.const ``Exists _) t) b =>
    if t == (mkConst ``Bool) then
      let btrue ← whnf $ mkApp b (mkConst ``true)
      let bfalse ← whnf $ mkApp b (mkConst ``false)
      mkAppM ``Or #[btrue, bfalse]
    else return none
  | _ => return none

partial def applyRule25Helper (e : Expr) (hyps : Array Expr) : RuleM (Option (Nat × Nat)) := do
  match e.consumeMData with
  | Expr.forallE _ t b _ =>
    let findNegation (h : Expr) : Bool := -- h = ¬t or t = ¬h
      h == Expr.app (Expr.const ``Not []) t || t == Expr.app (Expr.const ``Not []) h
    match hyps.findIdx? findNegation with
    | some hIdx =>
      let tIdx := hyps.size
      if t == Expr.app (Expr.const ``Not []) hyps[hIdx]! then return some (tIdx, hIdx)
      else return some (hIdx, tIdx)
    | none => applyRule25Helper b (hyps.push t)
  | _ => return none

/-- (s1 → s2 → ... → sn → v) ↦ True if there exists i and j such that si = ¬sj
    Since this rule will require a more involved proof reconstruction, rather than returning the
    resulting expression as in previous applyRule functions, we return the two indices of the hypotheses
    that directly contradict each other. Specifically, if si = ¬sj, then we return some (i, j). -/
def applyRule25 (e : Expr) : RuleM (Option (Nat × Nat)) := applyRule25Helper e #[]

partial def applyRule26Helper (e : Expr) (hyps : Array Expr) : RuleM (Option (Nat × Nat)) := do
  match e.consumeMData with
  | e@(Expr.forallE ..) => Meta.forallTelescope e fun xs b => do
    let tys ← (xs.mapM Meta.inferType : MetaM (Array Expr))
    applyRule26Helper b (hyps.append tys)
  | _ =>
    if !(← inferType e).isProp then return none -- Prevents applying rule26 to expressions like Nat → Nat
    let goals := getDisjunctiveGoals e #[]
    let mut goalIdx := 0
    for goal in goals do
      match hyps.findIdx? (fun hyp => hyp == goal) with
      | some hypIdx => return some (hypIdx, goalIdx)
      | none => goalIdx := goalIdx + 1
    return none

/-- (s1 → s2 → ... → sn → v1 ∨ ... ∨ vm) ↦ True if there exists i and j such that si = vj
    Since this rule will require a more involved proof reconstruction, rather than returning the
    resulting expression as in previous applyRule functions, we return the index of the hypothesis si and
    the index of the conclusion vj. Specifically, if si = vj, then we return some (i, j) -/
def applyRule26 (e : Expr) : RuleM (Option (Nat × Nat)) := applyRule26Helper e #[]

/-- (s1 ∧ s2 ∧ ... ∧ sn → v1 ∨ ... ∨ vm) ↦ True if there exists i and j such that si = vj
    Since this rule will require a more involved proof reconstruction, rather than returning the
    resulting expression as in previous applyRule functions, we return the index of the hypothesis si
    and the inddex of the conclusion vj. Specifically, if si = vj, then we return some (i, j) -/
partial def applyRule27 (e : Expr) : RuleM (Option (Nat × Nat)) := do
  match e.consumeMData with
  | e@(Expr.forallE ..) => Meta.forallBoundedTelescope e (some 1) fun xs b => do
    if !(← inferType b).isProp then return none -- Prevents applying rule27 to expressions like Nat → Nat
    let t ← inferType xs[0]!
    let hyps := getConjunctiveHypothesesHelper t
    let goals := getDisjunctiveGoals b #[]
    let mut goalIdx := 0
    for goal in goals do
      match hyps.findIdx? (fun hyp => hyp == goal) with
      | some hypIdx => return some (hypIdx, goalIdx)
      | none => goalIdx := goalIdx + 1
    return none
  | _ => return none

/-- s1 ↔ s2 ↦ s1 = s2 -/
def applyRule28 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Iff _) e1) e2 => some $ mkApp3 (mkConst ``Eq [levelOne]) (mkSort levelZero) e1 e2
  | _ => none

/-- Returns the rule theorem corresponding to boolSimpRule with the first argument applied.

    Note that this function assumes that `boolSimpRule` has already been shown to be applicable to `originalExp` so
    this is not rechecked (e.g. for rule1, this function does not check that the two propositions in the disjunction
    are actually equal, it assumes that this is the case from the fact that rule1 was applied) -/
def getBoolSimpRuleTheorem (boolSimpRule : BoolSimpRule) (originalExp : Expr) (ijOpt : Option (Nat × Nat)) : MetaM Expr :=
  match boolSimpRule with
  | rule1 => -- s ∨ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule1Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule1"
  | rule1b => -- s || s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) e1) _ => return mkApp (mkConst ``rule1bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule1b"
  | rule2 => -- ¬s ∨ s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 => return mkApp (mkConst ``rule2Theorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule2"
  | rule2b => -- !s || s ↦ true
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) _) e2 => return mkApp (mkConst ``rule2bTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule2b"
  | rule2Sym => -- s ∨ ¬s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule2SymTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule2Sym"
  | rule2bSym => -- s || !s ↦ true
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) e1) _ => return mkApp (mkConst ``rule2bSymTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule2bSym"
  | rule3 => -- s ∨ True ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule3Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule3"
  | rule3b => -- s || true ↦ true
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) e1) _ => return mkApp (mkConst ``rule3bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule3b"
  | rule3Sym => -- True ∨ s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 => return mkApp (mkConst ``rule3SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule3Sym"
  | rule3bSym => -- true || s ↦ true
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) _) e2 => return mkApp (mkConst ``rule3bSymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule3bSym"
  | rule4 => -- s ∨ False ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule4Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule4"
  | rule4b => -- s || false ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) e1) _ => return mkApp (mkConst ``rule4bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule4b"
  | rule4Sym => -- False ∨ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 => return mkApp (mkConst ``rule4SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule4Sym"
  | rule4bSym => -- false || s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``or _) _) e2 => return mkApp (mkConst ``rule4bSymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule4bSym"
  | rule5 => -- s = s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) _ => Meta.mkAppM ``rule5Theorem #[e1]
    | _ => throwError "Invalid originalExp {originalExp} for rule5"
  | rule5b => -- s == s ↦ true
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) _ => Meta.mkAppM ``rule5bTheorem #[e1]
    | _ => throwError "Invalid originalExp {originalExp} for rule5b"
  | rule6 => -- s = True ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) _ => return mkApp (mkConst ``rule6Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule6"
  | rule6b => -- s == true ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) _ => return mkApp (mkConst ``rule6bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule6b"
  | rule6Sym => -- True = s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _) e2 => return mkApp (mkConst ``rule6SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule6Sym"
  | rule6bSym => -- true == s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) _) e2 => return mkApp (mkConst ``rule6bSymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule6bSym"
  | rule7 => -- Not False ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``Not _) (Expr.const ``False _) => return mkConst ``rule7Theorem
    | _ => throwError "Invalid originalExp {originalExp} for rule7"
  | rule7b => -- !false ↦ true
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``not _) (Expr.const ``false _) => return mkConst ``rule7bTheorem
    | _ => throwError "Invalid originalExp {originalExp} for rule7b"
  | rule8 => -- s ∧ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule8Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule8"
  | rule8b => -- s && s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) e1) _ => return mkApp (mkConst ``rule8bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule8b"
  | rule9 => -- ¬s ∧ s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) _) e2 => return mkApp (mkConst ``rule9Theorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule9"
  | rule9b => -- !s && s ↦ false
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) _) e2 => return mkApp (mkConst ``rule9bTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule9b"
  | rule9Sym => -- s ∧ ¬s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule9SymTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule9Sym"
  | rule9bSym => -- s && !s ↦ false
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) e1) _ => return mkApp (mkConst ``rule9bSymTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule9bSym"
  | rule10 => -- s ∧ True ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule10Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule10"
  | rule10b => -- s && true ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) e1) _ => return mkApp (mkConst ``rule10bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule10b"
  | rule10Sym => -- True ∧ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) _) e2 => return mkApp (mkConst ``rule10SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule10Sym"
  | rule10bSym => -- true && s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) _) e2 => return mkApp (mkConst ``rule10bSymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule10bSym"
  | rule11 => -- s ∧ False ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule11Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule11"
  | rule11b => -- s && false ↦ false
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) e1) _ => return mkApp (mkConst ``rule11bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule11b"
  | rule11Sym => -- False ∧ s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) _) e2 => return mkApp (mkConst ``rule11SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule11Sym"
  | rule11bSym => -- false && s ↦ false
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``and _) _) e2 => return mkApp (mkConst ``rule11bSymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule11bSym"
  | rule12 => -- s ≠ s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _) e1) _ => Meta.mkAppM ``rule12Theorem #[e1]
    | _ => throwError "Invalid originalExp {originalExp} for rule12"
  | rule12b => -- s != s ↦ false
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``bne _) _) _) e1) _ => Meta.mkAppM ``rule12bTheorem #[e1]
    | _ => throwError "Invalid originalExp {originalExp} for rule12b"
  | rule13 => -- s = False ↦ ¬s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) _ => return mkApp (mkConst ``rule13Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule13"
  | rule13b => -- s == false ↦ !s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) e1) _ => return mkApp (mkConst ``rule13bTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule13b"
  | rule13Sym => -- False = s ↦ ¬s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _) e2 => return mkApp (mkConst ``rule13SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule13Sym"
  | rule13bSym => -- false == s ↦ !s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const ``BEq.beq _) _) _) _) e2 => return mkApp (mkConst ``rule13bSymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule13bSym"
  | rule14 => -- Not True ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``Not _) (Expr.const ``True _) => return mkConst ``rule14Theorem
    | _ => throwError "Invalid originalExp {originalExp} for rule14"
  | rule14b => -- !true ↦ false
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``not _) (Expr.const ``true _) => return mkConst ``rule14bTheorem
    | _ => throwError "Invalid originalExp {originalExp} for rule14b"
  | rule15 => -- ¬¬s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``Not _) (Expr.app (Expr.const ``Not _) e') => return mkApp (mkConst ``rule15Theorem) e'
    | _ => throwError "Invalid originalExp {originalExp} for rule15"
  | rule15b => -- !!s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``not _) (Expr.app (Expr.const ``not _) e') => return mkApp (mkConst ``rule15bTheorem) e'
    | _ => throwError "Invalid originalExp {originalExp} for rule15b"
  | rule16 => -- True → s ↦ s
    match originalExp.consumeMData with
    | Expr.forallE _ _ b _ => return mkApp (mkConst ``rule16Theorem) b
    | _ => throwError "Invalid originalExp {originalExp} for rule16"
  | rule17 => -- False → s ↦ True
    match originalExp.consumeMData with
    | Expr.forallE _ _ b _ => return mkApp (mkConst ``rule17Theorem) b
    | _ => throwError "Invalid originalExp {originalExp} for rule17"
  | rule18 => -- s → False ↦ ¬s
    match originalExp.consumeMData with
    | Expr.forallE _ t _ _ => return mkApp (mkConst ``rule18Theorem) t
    | _ => throwError "Invalid originalExp {originalExp} for rule18"
  | rule19 => -- s → True ↦ True (we generalize this to (∀ _ : α, True) ↦ True)
    match originalExp.consumeMData with
    | Expr.forallE _ t _ _ => Meta.mkAppM ``rule19Theorem #[t]
    | _ => throwError "Invalid originalExp {originalExp} for rule19"
  | rule20 => -- s → ¬s ↦ ¬s
    match originalExp.consumeMData with
    | Expr.forallE _ t _ _ => return mkApp (mkConst ``rule20Theorem) t
    | _ => throwError "Invalid originalExp {originalExp} for rule20"
  | rule21 => -- ¬s → s ↦ s
    match originalExp.consumeMData with
    | Expr.forallE _ _ b _ => return mkApp (mkConst ``rule21Theorem) b
    | _ => throwError "Invalid originalExp {originalExp} for rule21"
  | rule22 => -- s → s ↦ True
    match originalExp.consumeMData with
    | Expr.forallE _ _ b _ => return mkApp (mkConst ``rule22Theorem) b
    | _ => throwError "Invalid originalExp {originalExp} for rule22"
  | rule23 => -- ∀ p : Prop, f(p) ↦ f(True) ∧ f(False)
    match originalExp.consumeMData with
    | Expr.forallE n _ b _ => do
      let bFunction := Expr.lam n (mkSort levelZero) b BinderInfo.default
      return mkApp (mkConst ``rule23Theorem) bFunction
    | _ => throwError "Invalid originalExp {originalExp} for rule23"
  | rule23b => -- ∀ b : Bool, f(b) ↦ f true ∧ f false (assuming `f : Bool → Prop`)
    match originalExp.consumeMData with
    | Expr.forallE n _ b _ => do
      let bFunction := Expr.lam n (mkConst ``Bool) b BinderInfo.default
      return mkApp (mkConst ``rule23bTheorem) bFunction
    | _ => throwError "Invalid originalExp {originalExp} for rule23b"
  | rule24 => -- ∃ p : Prop, f(p) ↦ f True ∨ f False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Exists _) t) b => return mkApp (mkConst ``rule24Theorem) b
    | _ => throwError "Invalid originalExp {originalExp} for rule24"
  | rule24b => -- ∃ b : Bool, f(b) ↦ f true ∨ f false (assuming `f : Bool → Prop`)
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Exists _) t) b => return mkApp (mkConst ``rule24bTheorem) b
    | _ => throwError "Invalid originalExp {originalExp} for rule24b"
  | rule25 => -- (s1 → s2 → ... → sn → v) ↦ True if there exists i and j such that si = ¬sj
    match ijOpt with
    | some (i, j) => do Meta.mkAppM ``eq_true #[← mkRule25Theorem originalExp 0 i j]
    | none => throwError "rule25 requires indices that were not passed into getBoolSimpRuleTheorem"
  | rule26 => -- (s1 → s2 → ... → sn → v1 ∨ ... ∨ vm) ↦ True if there exists i and j such that si = vj
    match ijOpt with
    | some (i, j) => do Meta.mkAppM ``eq_true #[← mkRule26Theorem originalExp 0 i j]
    | none => throwError "rule26 requires indices that were not passed into getBoolSimpRuleTheorem"
  | rule27 => -- (s1 ∧ s2 ∧ ... ∧ sn → v1 ∨ ... ∨ vm) ↦ True if there exists i and j such that si = vj
    match ijOpt with
    | some (i, j) => do Meta.mkAppM ``eq_true #[← mkRule27Theorem originalExp i j]
    | none => throwError "rule27 requires indices that were not passed into getBoolSimpRuleTheorem"
  | rule28 => -- s1 ↔ s2 ↦ s1 = s2
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Iff _) e1) e2 => return mkApp2 (mkConst ``rule28Theorem) e1 e2
    | _ => throwError "Invalid originalExpr {originalExp} for rule28"

/-- Some boolSimpRules (those with `b` suffixes) operates on `Bool` rather than `Prop`. `mkBoolSimpProp` needs to know whether
    `boolSimpRule` is one such rule in order to pass the correct type into `congrArg` -/
def boolSimpRuleOperatesOnBool (boolSimpRule : BoolSimpRule) : Bool :=
  match boolSimpRule with
  | rule1b | rule2b | rule2bSym | rule3b | rule3bSym | rule4b | rule4bSym | rule5b | rule6b | rule6bSym | rule7b | rule8b
  | rule9b | rule9bSym | rule10b | rule10bSym | rule11b | rule11bSym | rule12b | rule13b | rule13bSym | rule14b | rule15b => true
  | _ => false -- `rule23b` and `rule24b` yield false because technically they take `Prop`s as input

def mkBoolSimpProof (substPos : ClausePos) (boolSimpRule : BoolSimpRule) (ijOpt : Option (Nat × Nat)) (premises : List Expr)
  (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
        if(i == substPos.lit) then
          let substLitPos : LitPos := ⟨substPos.side, substPos.pos⟩
          let boolSimpRuleThm ← getBoolSimpRuleTheorem boolSimpRule (← parentLits[substPos.lit]!.getAtPos! substLitPos) ijOpt

          let abstrLit ← (lit.abstractAtPos! substLitPos)
          let abstrExp := abstrLit.toExpr
          let abstrLam :=
            if boolSimpRuleOperatesOnBool boolSimpRule then mkLambda `x BinderInfo.default (mkConst ``Bool) abstrExp
            else mkLambda `x BinderInfo.default (mkSort levelZero) abstrExp
          let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, boolSimpRuleThm], h]
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i $ rwproof
        else
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
      proofCases := proofCases.push pr
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- The list of rules that do not require the RuleM monad -/
def applyRulesList1 : List ((Expr → (Option Expr)) × BoolSimpRule) := [
  (applyRule1, rule1),
  (applyRule1b, rule1b),
  (applyRule2, rule2),
  (applyRule2b, rule2b),
  (applyRule2Sym, rule2Sym),
  (applyRule2bSym, rule2bSym),
  (applyRule3, rule3),
  (applyRule3b, rule3b),
  (applyRule3Sym, rule3Sym),
  (applyRule3bSym, rule3bSym),
  (applyRule4, rule4),
  (applyRule4b, rule4b),
  (applyRule4Sym, rule4Sym),
  (applyRule4bSym, rule4bSym),
  (applyRule5, rule5),
  (applyRule5b, rule5b),
  (applyRule6, rule6),
  (applyRule6b, rule6b),
  (applyRule6Sym, rule6Sym),
  (applyRule6bSym, rule6bSym),
  (applyRule7, rule7),
  (applyRule7b, rule7b),
  (applyRule8, rule8),
  (applyRule8b, rule8b),
  (applyRule9, rule9),
  (applyRule9b, rule9b),
  (applyRule9Sym, rule9Sym),
  (applyRule9bSym, rule9bSym),
  (applyRule10, rule10),
  (applyRule10b, rule10b),
  (applyRule10Sym, rule10Sym),
  (applyRule10bSym, rule10bSym),
  (applyRule11, rule11),
  (applyRule11b, rule11b),
  (applyRule11Sym, rule11Sym),
  (applyRule11bSym, rule11bSym),
  (applyRule12, rule12),
  (applyRule12b, rule12b),
  (applyRule13, rule13),
  (applyRule13b, rule13b),
  (applyRule13Sym, rule13Sym),
  (applyRule13bSym, rule13bSym),
  (applyRule14, rule14),
  (applyRule14b, rule14b),
  (applyRule15, rule15),
  (applyRule15b, rule15b),
  (applyRule16, rule16),
  (applyRule17, rule17),
  (applyRule19, rule19),
  (applyRule20, rule20),
  (applyRule21, rule21),
  (applyRule28, rule28)
]

/-- The list of rules that do require the RuleM monad -/
def applyRulesList2 : List ((Expr → RuleM (Option Expr)) × BoolSimpRule) := [
  (applyRule18, rule18),
  (applyRule22, rule22),
  (applyRule23, rule23),
  (applyRule23b, rule23b),
  (applyRule24, rule24),
  (applyRule24b, rule24b)
]

/-- The list of rules for which indices must be returned -/
def applyRulesList3 : List ((Expr → RuleM (Option (Nat × Nat))) × BoolSimpRule) := [
  (applyRule25, rule25),
  (applyRule26, rule26),
  (applyRule27, rule27)
]

def applyBoolSimpRules (e : Expr) : RuleM (Option (Expr × BoolSimpRule)) := do
  for (applyRuleFn, rule) in applyRulesList1 do
    match applyRuleFn e with
    | some e' => return some (e', rule)
    | none => continue
  for (applyRuleFn, rule) in applyRulesList2 do
    match ← applyRuleFn e with
    | some e' => return some (e', rule)
    | none => continue
  return none

def applyBoolSimpRulesWithIndices (e : Expr) : RuleM (Option ((Nat × Nat) × BoolSimpRule)) := do
  for (applyRuleFn, rule) in applyRulesList3 do
    match ← applyRuleFn e with
    | some ij => return some (ij, rule)
    | none => continue
  return none

/-- Implements various Prop-related simplifications as described in "Superposition with First-Class Booleans and Inprocessing
    Clausification" and "Extensional Paramodulation for Higher-Order Logic and its Effective Implementation Leo-III" -/
def boolSimp : MSimpRule := fun c => do
  let c ← loadClause c
  trace[duper.rule.boolSimp] "Running boolSimp on {c.lits}"
  let fold_fn := fun acc e pos => do
    match acc.2 with
    | some _ => return acc -- If boolSimp ever succeeds, just return on first success
    | none =>
      let e := e.consumeMData -- We apply consumeMData before passing e into all of the rules so we don't need to constantly reapply it
      /-
        Try to apply each of the rules to e. If any of them succeed, perform the appropriate substitution and return
        the new clause along with a proof that the new clause can be obtained from the old one. If all of the rules fail,
        then return the original clause and none (which is simply the same acc we started with)
      -/
      match ← applyBoolSimpRules e with
      | some (e', boolSimpRule) =>
        if let some replacedMClause ← c.replaceAtPosUpdateType? pos e' then
          trace[duper.rule.boolSimp] "Replaced {e} with {e'} in {c.lits} to produce {replacedMClause.lits} via {boolSimpRule}"
          return (replacedMClause, mkBoolSimpProof pos boolSimpRule none)
        else
          return acc
      | none => -- If none of the first 24 rules worked, attempt rules 25, 26, and 27
        match ← applyBoolSimpRulesWithIndices e with
        | some (ij, boolSimpRule) =>
          if let some replacedMClause ← c.replaceAtPosUpdateType? pos (mkConst ``True) then
            trace[duper.rule.boolSimp] "Replaced {e} with True in {c.lits} to produce {replacedMClause.lits} via {boolSimpRule}"
            return (replacedMClause, mkBoolSimpProof pos boolSimpRule (some ij))
          else
            return acc
        | none => return acc -- If no bool simp rule can be applied, then return the original clause unchanged
  let (c', proofOpt) ← c.foldGreenM fold_fn (c, none)
  match proofOpt with
  | none => return none -- No substitutions were performed, so we don't need to yield any clause and we can return false
  | some proof =>
    let cp ← yieldClause c' "bool simp" $ some proof
    return some #[cp]
