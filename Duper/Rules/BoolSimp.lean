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
  -- TODO: Implement remaining rules (note: skip ∀ and ∃ Leo-III rules because they're not valid with empty types)

open BoolSimpRule

def BoolSimpRule.format (boolSimpRule : BoolSimpRule) : MessageData :=
  match boolSimpRule with
  | rule1 => m!"rule1"
  | rule2 => m!"rule2"
  | rule2Sym => m!"rule2Sym"
  | rule3 => m!"rule3"
  | rule3Sym => m!"rule3Sym"

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

/-- s ∨ s ↦ s -/
def applyRule1 (e : Expr) : RuleM (Option Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e1 == e2 then return some e1
    else return none
  | _ => return none

/-- ¬s ∨ s ↦ True -/
def applyRule2 (e : Expr) : RuleM (Option Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e1 == Expr.app (Expr.const ``Not []) e2 then return some (mkConst ``True)
    else return none
  | _ => return none

/-- s ∨ ¬s ↦ True -/
def applyRule2Sym (e : Expr) : RuleM (Option Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) e2 =>
    if e2 == Expr.app (Expr.const ``Not []) e1 then return some (mkConst ``True)
    else return none
  | _ => return none

/-- s ∨ True ↦ True -/
def applyRule3 (e : Expr) : RuleM (Option Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) _) e2 =>
    if e2 == mkConst ``True then return some (mkConst ``True)
    else return none
  | _ => return none

/-- True ∨ s ↦ True -/
def applyRule3Sym (e : Expr) : RuleM (Option Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Or _) e1) _ =>
    if e1 == mkConst ``True then return some (mkConst ``True)
    else return none
  | _ => return none

/-- Returns a Lit defining the equality indicated by `boolSimpRule` and `originalExp` along with the appropriate theorem
    with the first argument applied. Note that this function assumes that `boolSimpRule` has already been shown to be
    applicable to `originalExp` so this is not rechecked (e.g. for rule1, this function does not check that the two propositions
    in the disjunction are actually equal, it assumes that this is the case from the fact that rule1 was applied) -/
def getLitAndTheoremFromBoolSimpRule (boolSimpRule : BoolSimpRule) (originalExp : Expr) : MetaM (Lit × Expr) :=
  -- Every field of eqLit will be as written here except for rhs which will be overwritten by each case
  let eqLit := Lit.mk
    (sign := true)
    (lvl := levelOne)
    (ty := mkSort levelZero) -- e1 and e2 have to be of type Prop for them to be connected via ``Or
    (lhs := originalExp.consumeMData)
    (rhs := originalExp.consumeMData)
  match boolSimpRule with
  | rule1 => -- s ∨ s ↦ s
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ =>
      let eqLit := {eqLit with rhs := e1}
      let boolSimpRuleTheorem := mkApp (mkConst ``rule1Theorem) e1 
      return (eqLit, boolSimpRuleTheorem)
    | _ => throwError "Invalid orignalExp {originalExp} for rule1"
  | rule2 => -- ¬s ∨ s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 =>
      let eqLit := {eqLit with rhs := mkConst ``True}
      let boolSimpRuleTheorem := mkApp (mkConst ``rule2Theorem) e2
      return (eqLit, boolSimpRuleTheorem)
    | _ => throwError "Invalid originalExp {originalExp} for rule2"
  | rule2Sym => -- s ∨ ¬s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ =>
      let eqLit := {eqLit with rhs := mkConst ``True}
      let boolSimpRuleTheorem := mkApp (mkConst ``rule2SymTheorem) e1
      return (eqLit, boolSimpRuleTheorem)
    | _ => throwError "Invalid originalExp {originalExp} for rule2Sym"
  | rule3 => -- s ∨ True ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) e1) _ =>
      let eqLit := {eqLit with rhs := mkConst ``True}
      let boolSimpRuleTheorem := mkApp (mkConst ``rule3Theorem) e1
      return (eqLit, boolSimpRuleTheorem)
    | _ => throwError "Invalid originalExp {originalExp} for rule3"
  | rule3Sym => -- True ∨ s ↦ True
    match originalExp.consumeMData with
    | Expr.app (Expr.app (Expr.const ``Or _) _) e2 =>
      let eqLit := {eqLit with rhs := mkConst ``True}
      let boolSimpRuleTheorem := mkApp (mkConst ``rule3SymTheorem) e2
      return (eqLit, boolSimpRuleTheorem)
    | _ => throwError "Invalid originalExp {originalExp} for rule3Sym"

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
          let (eqLit, boolSimpRuleThm) ← getLitAndTheoremFromBoolSimpRule boolSimpRule (parentLits[substPos.lit]!.getAtPos! substLitPos)

          let litPos : LitPos := {side := substPos.side, pos := substPos.pos}
          let abstrLit ← (lit.abstractAtPos! litPos)
          let abstrExp := abstrLit.toExpr
          let abstrLam := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstrExp
          let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, boolSimpRuleThm], h]
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i $ rwproof
        else
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
      proofCases := proofCases.push pr
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

def applyRulesList : List ((Expr → RuleM (Option Expr)) × BoolSimpRule) := [
  (applyRule1, rule1),
  (applyRule2, rule2),
  (applyRule2Sym, rule2Sym),
  (applyRule3, rule3),
  (applyRule3Sym, rule3Sym)
]

def applyBoolSimpRules (e : Expr) : RuleM (Option (Expr × BoolSimpRule)) := do
  for (applyRuleFn, rule) in applyRulesList do
    match ← applyRuleFn e with
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