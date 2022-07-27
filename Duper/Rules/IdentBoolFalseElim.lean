import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open SimpResult
open Lean

#check Meta.isDefEq

/-- Determines whether a literal has exactly the form `false = true` or `true = false`-/
def isFalseLiteral (lit : Lit) : MetaM Bool := do
  if ← Meta.isDefEq lit.ty (mkConst ``Bool) then
    return lit.sign &&
      ((lit.lhs == mkConst ``true && lit.rhs == mkConst ``false) ||
      (lit.lhs == mkConst ``false && lit.rhs == mkConst ``true))
  else return false

theorem bool_false_ne_true (h : false = true) : False := ne_false_of_eq_true h (by rfl)

theorem bool_true_ne_false (h : true = false) : False := ne_true_of_eq_false h (by rfl)

def mkIdentBoolFalseElimProof (refs : Array (Option Nat)) (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]
    let appliedPremise := appliedPremises[0]

    let mut proofCases : Array Expr := #[]
    for i in [:parentLits.size] do
      let lit := parentLits[i]
      if (← isFalseLiteral lit) then -- lit has the form `false = true` or `true = false`
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
        match refs[i] with
        | none => throwError "Refs invariant is not satisfied in identFalseElim"
        | some j =>
          let proofCase ← Meta.withLocalDeclD `h parentLits[i].toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Eliminate literals that are exactly of the form `false = true` or `true = false`. 
    This is a special case of the falseElim inference rule in which σ is the identity. 
    This rule is included as a means of giving Bools special attention. -/
def identBoolFalseElim : MSimpRule := fun c => do
  let mut newLits : Array Lit := #[]
  -- If c.lits[i] is `false = true` or `true = false`, then refs[i] = none
  -- If c.lits[i] isn't `false = true` or `true = false`,then refs[i] = some j where newLits[j] = c.lits[i]
  let mut refs : Array (Option Nat) := #[]
  for lit in c.lits do
    if (← runMetaAsRuleM (isFalseLiteral lit)) then
      refs := refs.push none
    else
      refs := refs.push (some newLits.size)
      newLits := newLits.push lit
  if (newLits.size = c.lits.size) then
    return Unapplicable
  else
    return Applied [(MClause.mk newLits, some (mkIdentBoolFalseElimProof refs))]

end Duper