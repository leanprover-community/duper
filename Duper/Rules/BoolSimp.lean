import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open Lean.Meta
open RuleM
open SimpResult
open Comparison

initialize Lean.registerTraceClass `Rule.boolSimp

-- Rules 1 through 15 are from Leo-III. Remaining rules are from "Superposition with First-Class
-- Booleans and Inprocessing Clausification"
inductive BoolSimpRule
  | rule1 -- s ∨ s ↦ s
  | rule2 -- ¬s ∨ s ↦ True
  | rule2Sym -- s ∨ ¬s ↦ True
  | rule3 -- s ∨ True ↦ True
  | rule3Sym -- True ∨ s ↦ True
  | rule4 -- s ∨ False ↦ s
  | rule4Sym -- False ∨ s ↦ s
  | rule5 -- s = s ↦ True
  | rule6 -- s = True ↦ s
  | rule6Sym -- True = s ↦ s
  | rule7 -- Not False ↦ True
  | rule8 -- s ∧ s ↦ s
  | rule9 -- ¬s ∧ s ↦ False
  | rule9Sym -- s ∧ ¬s ↦ False
  | rule10 -- s ∧ True ↦ s
  | rule10Sym -- True ∧ s ↦ s
  | rule11 -- s ∧ False ↦ False
  | rule11Sym -- False ∧ s ↦ False
  | rule12 -- s ≠ s ↦ False
  | rule13 -- s = False ↦ ¬s
  | rule13Sym -- False = s ↦ ¬s
  | rule14 -- Not True ↦ False
  | rule15 -- ¬¬s ↦ s
  -- TODO: Implement rules from "Superposition with First-Class Booleans and Inprocessing Clausification"

open BoolSimpRule

def BoolSimpRule.format (boolSimpRule : BoolSimpRule) : MessageData :=
  match boolSimpRule with
  | rule1 => m!"rule1"
  | rule2 => m!"rule2"
  | rule2Sym => m!"rule2Sym"
  | rule3 => m!"rule3"
  | rule3Sym => m!"rule3Sym"
  | rule4 => m!"rule4"
  | rule4Sym => m!"rule4Sym"
  | rule5 => m!"rule5"
  | rule6 => m!"rule6"
  | rule6Sym => m!"rule6Sym"
  | rule7 => m!"rule7"
  | rule8 => m!"rule8"
  | rule9 => m!"rule9"
  | rule9Sym => m!"rule9Sym"
  | rule10 => m!"rule10"
  | rule10Sym => m!"rule10Sym"
  | rule11 => m!"rule11"
  | rule11Sym => m!"rule11Sym"
  | rule12 => m!"rule12"
  | rule13 => m!"rule13"
  | rule13Sym => m!"rule13Sym"
  | rule14 => m!"rule14"
  | rule15 => m!"rule15"

instance : ToMessageData BoolSimpRule := ⟨BoolSimpRule.format⟩

theorem rule1Theorem (p : Prop) : (p ∨ p) = p := by simp
theorem rule2Theorem (p : Prop) : (¬p ∨ p) = True := by
  apply @Classical.byCases p
  . intro hp
    apply eq_true
    exact Or.intro_right _ hp
  . intro hnp
    apply eq_true
    exact Or.intro_left _ hnp
theorem rule2SymTheorem (p : Prop) : (p ∨ ¬p) = True := by
  apply @Classical.byCases p
  . intro hnp
    apply eq_true
    exact Or.intro_left _ hnp
  . intro hp
    apply eq_true
    exact Or.intro_right _ hp
theorem rule3Theorem (p : Prop) : (p ∨ True) = True := by simp
theorem rule3SymTheorem (p : Prop) : (True ∨ p) = True := by simp
theorem rule4Theorem (p : Prop) : (p ∨ False) = p := by simp
theorem rule4SymTheorem (p : Prop) : (False ∨ p) = p := by simp
theorem rule5Theorem (p : α) : (p = p) = True := by simp
theorem rule6Theorem (p : Prop) : (p = True) = p := by simp
theorem rule6SymTheorem (p : Prop) : (True = p) = p := by simp
theorem rule7Theorem : Not False = True := by simp
theorem rule8Theorem (p : Prop) : (p ∧ p) = p := by simp
theorem rule9Theorem (p : Prop) : (¬p ∧ p) = False := by simp
theorem rule9SymTheorem (p : Prop) : (p ∧ ¬p) = False := by simp
theorem rule10Theorem (p : Prop) : (p ∧ True) = p := by simp
theorem rule10SymTheorem (p : Prop) : (True ∧ p) = p := by simp
theorem rule11Theorem (p : Prop) : (p ∧ False) = False := by simp
theorem rule11SymTheorem (p : Prop) : (False ∧ p) = False := by simp
theorem rule12Theorem (p : α) : (p ≠ p) = False := by simp
theorem rule13Theorem (p : Prop) : (p = False) = ¬p := by simp
theorem rule13SymTheorem (p : Prop) : (False = p) = ¬p := by simp
theorem rule14Theorem : Not True = False := by simp
theorem rule15Theorem (p : Prop) : (¬¬p) = p := by rw [Classical.not_not]

/-- s ∨ s ↦ s -/
def applyRule1 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
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

/-- s ∨ ¬s ↦ True -/
def applyRule2Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``Not []) e1 then some (mkConst ``True)
    else none
  | _ => none

/-- s ∨ True ↦ True -/
def applyRule3 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) _) e2 =>
    if e2 == mkConst ``True then some (mkConst ``True)
    else none
  | _ => none

/-- True ∨ s ↦ True -/
def applyRule3Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) _ =>
    if e1 == mkConst ``True then some (mkConst ``True)
    else none
  | _ => none

/-- s ∨ False ↦ s -/
def applyRule4 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e2 == mkConst ``False then some e1
    else none
  | _ => none

/-- False ∨ s ↦ s -/
def applyRule4Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e1 == mkConst ``False then some e2
    else none
  | _ => none

/-- s = s ↦ True -/
def applyRule5 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e1 == e2 then some (mkConst ``True)
    else none
  | _ => none

/-- s = True ↦ s -/
def applyRule6 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e2 == mkConst ``True then some e1
    else none
  | _ => none

/-- True = s ↦ s -/
def applyRule6Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e1 == mkConst ``True then some e2
    else none
  | _ => none

/-- Not False ↦ True -/
def applyRule7 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) (Expr.const ``False _) => some (mkConst ``True)
  | _ => none

/-- s ∧ s ↦ s -/
def applyRule8 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
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

/-- s ∧ ¬s ↦ False -/
def applyRule9Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``Not []) e1 then some (mkConst ``False)
    else none
  | _ => none

/-- s ∧ True ↦ s -/
def applyRule10 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e2 == mkConst ``True then some e1
    else none
  | _ => none

/-- True ∧ s ↦ s -/
def applyRule10Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) e2 =>
    if e1 == mkConst ``True then some e2
    else none
  | _ => none

/-- s ∧ False ↦ False -/
def applyRule11 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) _) e2 =>
    if e2 == mkConst ``False then some (mkConst ``False)
    else none
  | _ => none

/-- False ∧ s ↦ False -/
def applyRule11Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) e1) _ =>
    if e1 == mkConst ``False then some (mkConst ``False)
    else none
  | _ => none

/-- s ≠ s ↦ False -/
def applyRule12 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _) e1) e2 =>
    if e1 == e2 then some (mkConst ``False)
    else none
  | _ => none

/-- s = False ↦ ¬s -/
def applyRule13 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e2 == mkConst ``False then some (mkApp (mkConst ``Not) e1)
    else none
  | _ => none

/-- False = s ↦ ¬s -/
def applyRule13Sym (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) e2 =>
    if e1 == mkConst ``False then some (mkApp (mkConst ``Not) e2)
    else none
  | _ => none

/-- Not True ↦ False -/
def applyRule14 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) (Expr.const ``True _) => some (mkConst ``False)
  | _ => none

/-- ¬¬s ↦ s -/
def applyRule15 (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.const ``Not _) e') => some e'
  | _ => none

/-- Returns the rule theorem corresponding to boolSimpRule with the first argument applied.

    Note that this function assumes that `boolSimpRule` has already been shown to be applicable to `originalExp` so
    this is not rechecked (e.g. for rule1, this function does not check that the two propositions in the disjunction
    are actually equal, it assumes that this is the case from the fact that rule1 was applied) -/
def getBoolSimpRuleTheorem (boolSimpRule : BoolSimpRule) (originalExp : Expr) : MetaM Expr :=
  match boolSimpRule with
  | rule1 => -- s ∨ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule1Theorem) e1
    | _ => throwError "Invalid orignalExp {originalExp} for rule1"
  | rule2 => -- ¬s ∨ s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 => return mkApp (mkConst ``rule2Theorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule2"
  | rule2Sym => -- s ∨ ¬s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule2SymTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule2Sym"
  | rule3 => -- s ∨ True ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule3Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule3"
  | rule3Sym => -- True ∨ s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 => return mkApp (mkConst ``rule3SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule3Sym"
  | rule4 => -- s ∨ False ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ => return mkApp (mkConst ``rule4Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule4"
  | rule4Sym => -- False ∨ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 => return mkApp (mkConst ``rule4SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule4Sym"
  | rule5 => -- s = s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) _ => Meta.mkAppM ``rule5Theorem #[e1]
    | _ => throwError "Invalid originalExp {originalExp} for rule5"
  | rule6 => -- s = True ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) _ => return mkApp (mkConst ``rule6Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule6"
  | rule6Sym => -- True = s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _) e2 => return mkApp (mkConst ``rule6SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule6Sym"
  | rule7 => -- Not False ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``Not _) (Expr.const ``False _) => return mkConst ``rule7Theorem
    | _ => throwError "Invalid originalExp {originalExp} for rule7"
  | rule8 => -- s ∧ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule8Theorem) e1
    | _ => throwError "Invalid orignalExp {originalExp} for rule8"
  | rule9 => -- ¬s ∧ s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) _) e2 => return mkApp (mkConst ``rule9Theorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule9"
  | rule9Sym => -- s ∧ ¬s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule9SymTheorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule9Sym"
  | rule10 => -- s ∧ True ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule10Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule10"
  | rule10Sym => -- True ∧ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) _) e2 => return mkApp (mkConst ``rule10SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule10Sym"
  | rule11 => -- s ∧ False ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) e1) _ => return mkApp (mkConst ``rule11Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule11"
  | rule11Sym => -- False ∧ s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``And _) _) e2 => return mkApp (mkConst ``rule11SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule11Sym"
  | rule12 => -- s ≠ s ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _) e1) _ => Meta.mkAppM ``rule12Theorem #[e1]
    | _ => throwError "Invalid originalExp {originalExp} for rule12"
  | rule13 => -- s = False ↦ ¬s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) e1) _ => return mkApp (mkConst ``rule13Theorem) e1
    | _ => throwError "Invalid originalExp {originalExp} for rule13"
  | rule13Sym => -- False = s ↦ ¬s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _) e2 => return mkApp (mkConst ``rule13SymTheorem) e2
    | _ => throwError "Invalid originalExp {originalExp} for rule13Sym"
  | rule14 => -- Not True ↦ False
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``Not _) (Expr.const ``True _) => return mkConst ``rule14Theorem
    | _ => throwError "Invalid originalExp {originalExp} for rule14"
  | rule15 => -- ¬¬s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.const ``Not _) (Expr.app (Expr.const ``Not _) e') => return mkApp (mkConst ``rule15Theorem) e'
    | _ => throwError "Invalid originalExp {originalExp} for rule15"

def mkBoolSimpProof (substPos : ClausePos) (boolSimpRule : BoolSimpRule) (premises : List Expr) (parents : List ProofParent)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
        if(i == substPos.lit) then
          let substLitPos : LitPos := ⟨substPos.side, substPos.pos⟩
          let boolSimpRuleThm ← getBoolSimpRuleTheorem boolSimpRule (parentLits[substPos.lit]!.getAtPos! substLitPos)

          let litPos : LitPos := {side := substPos.side, pos := substPos.pos}
          let abstrLit ← (lit.abstractAtPos! litPos)
          let abstrExp := abstrLit.toExpr
          let abstrLam := mkLambda `x BinderInfo.default (mkSort levelZero) abstrExp
          let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, boolSimpRuleThm], h]
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i $ rwproof
        else
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
      proofCases := proofCases.push pr
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

def applyRulesList : List ((Expr → (Option Expr)) × BoolSimpRule) := [
  (applyRule1, rule1),
  (applyRule2, rule2),
  (applyRule2Sym, rule2Sym),
  (applyRule3, rule3),
  (applyRule3Sym, rule3Sym),
  (applyRule4, rule4),
  (applyRule4Sym, rule4Sym),
  (applyRule5, rule5),
  (applyRule6, rule6),
  (applyRule6Sym, rule6Sym),
  (applyRule7, rule7),
  (applyRule8, rule8),
  (applyRule9, rule9),
  (applyRule9Sym, rule9Sym),
  (applyRule10, rule10),
  (applyRule10Sym, rule10Sym),
  (applyRule11, rule11),
  (applyRule11Sym, rule11Sym),
  (applyRule12, rule12),
  (applyRule13, rule13),
  (applyRule13Sym, rule13Sym),
  (applyRule14, rule14),
  (applyRule15, rule15)
]

def applyBoolSimpRules (e : Expr) : RuleM (Option (Expr × BoolSimpRule)) := do
  for (applyRuleFn, rule) in applyRulesList do
    match applyRuleFn e with
    | some e' => return some (e', rule)
    | none => continue
  return none

/-- Implements various Prop-related simplifications as described in "Superposition with First-Class Booleans and Inprocessing
    Clausification" and "Extensional Paramodulation for Higher-Order Logic and its Effective Implementation Leo-III" -/
def boolSimp : MSimpRule := fun c => do
  let c ← loadClause c
  trace[Rule.boolSimp] "Running boolSimp on {c.lits}"
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
        trace[Rule.boolSimp] "Replaced {e} with {e'} in {c.lits} to produce {(← c.replaceAtPos! pos e').lits} via {boolSimpRule}"
        return (← c.replaceAtPos! pos e', mkBoolSimpProof pos boolSimpRule)
      | none => return acc -- If no bool simp rule can be applied, then return the original clause unchanged
  let (c', proofOpt) ← c.foldGreenM fold_fn (c, none)
  match proofOpt with
  | none => return false -- No substitutions were performed, so we don't need to yield any clause and we can return false
  | some proof =>
    yieldClause c' "bool simp" $ some proof
    return true