import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open SimpResult
open Lean

/-- Determines whether a literal has exactly the form `false = true` or `true = false`-/
def isFalseBoolLiteral (lit : Lit) : MetaM Bool := do
  if lit.ty.consumeMData == (mkConst ``Bool) then
    return lit.sign &&
      ((lit.lhs == mkConst ``true && lit.rhs == mkConst ``false) ||
      (lit.lhs == mkConst ``false && lit.rhs == mkConst ``true))
  else return false

theorem bool_false_ne_true (h : false = true) : False := ne_false_of_eq_true h (by rfl)

theorem bool_true_ne_false (h : true = false) : False := ne_true_of_eq_false h (by rfl)

def mkIdentBoolFalseElimProof (refs : List (Option Nat)) (premises : List Expr) (parents: List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if (← isFalseBoolLiteral lit) then -- lit has the form `false = true` or `true = false`
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if (lit.lhs == mkConst ``false) then
            let proofCase := mkApp (mkConst ``bool_false_ne_true) h
            let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
            Meta.mkLambdaFVars #[h] proofCase
          else if(lit.lhs == mkConst ``true) then
            let proofCase := mkApp (mkConst ``bool_true_ne_false) h
            let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
            Meta.mkLambdaFVars #[h] proofCase
          else
            throwError "mkIdentBoolFalseElimProof failed to match {lit.lhs} to an expected expression"
        proofCases := proofCases.push proofCase
      else -- refs[i] should have the value (some j) where parentLits[i] == c[j]
        match refs[i]! with
        | none => throwError "Refs invariant is not satisfied in identBoolFalseElim"
        | some j =>
          let proofCase ← Meta.withLocalDeclD `h parentLits[i]!.toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Eliminate literals that are exactly of the form `false = true` or `true = false`. 
    This is a special case of the boolFalseElim inference rule in which σ is the identity. 
    This rule is included as a means of giving Bools special attention. -/
def identBoolFalseElim : MSimpRule := fun c => do
  let c ← loadClause c
  /-
    Spec for newLits and refs
    If c.lits[i] is `false = true` or `true = false`, then refs[i] = none
    If c.lits[i] isn't `false = true` or `true = false`,then refs[i] = some j where newLits[j] = c.lits[i]
  -/
  let mut newLits : List Lit := []
  let mut refs : List (Option Nat) := []
  for lit in c.lits do
    if (← runMetaAsRuleM (isFalseBoolLiteral lit)) then
      refs := none :: refs
    else
      refs := (some newLits.length) :: refs
      newLits := lit :: newLits
  -- To achieve the desired spec for newLits and refs, I must reverse them
  newLits := newLits.reverse
  refs := refs.reverse
  if (newLits.length = c.lits.size) then
    return none
  else
    let resultClause ← yieldClause (MClause.mk newLits.toArray c.mvars) "identity boolean false elimination"
      (some (mkIdentBoolFalseElimProof refs))
    return some #[resultClause]

end Duper