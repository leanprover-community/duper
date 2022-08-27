import Duper.Simp
import Duper.Util.ProofReconstruction
import Lean.Meta.Basic

namespace Duper
open RuleM
open SimpResult
open Lean

/-- Determines whether a literal has exactly the form `False = True` or `True = False`-/
def isFalsePropLiteral (lit : Lit) : MetaM Bool := do
  match lit.ty with
  | Expr.sort lvl =>
    if Level.isEquiv (← Lean.instantiateLevelMVars lvl) levelZero then
      return lit.sign &&
        ((lit.lhs == mkConst ``True && lit.rhs == mkConst ``False) ||
        (lit.lhs == mkConst ``False && lit.rhs == mkConst ``True))
    else return false
  | _ => return false

theorem prop_false_ne_true (h : False = True) : False := by rw [h]; exact ⟨⟩

theorem prop_true_ne_false (h : True = False) : False := by rw [← h]; exact ⟨⟩

def mkIdentPropFalseElimProof (refs : Array (Option Nat)) (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := #[]
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if (← isFalsePropLiteral lit) then -- lit has the form `False = True` or `True = False`
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if (lit.lhs == mkConst ``False) then
            let proofCase := mkApp (mkConst ``prop_false_ne_true) h
            let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
            Meta.mkLambdaFVars #[h] proofCase
          else if(lit.lhs == mkConst ``True) then
            let proofCase := mkApp (mkConst ``prop_true_ne_false) h
            let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
            Meta.mkLambdaFVars #[h] proofCase
          else
            throwError "mkIdentPropFalseElimProof failed to match {lit.lhs} to an expected expression"
        proofCases := proofCases.push proofCase
      else -- refs[i] should have the value (some j) where parentLits[i] == c[j]
        match refs[i]! with
        | none => throwError "Refs invariant is not satisfied in identPropFalseElim"
        | some j =>
          let proofCase ← Meta.withLocalDeclD `h parentLits[i]!.toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Eliminate literals that are exactly of the form `False = True` or `True = False`. 
    This is a special case of the propFalseElim inference rule in which σ is the identity. -/
def identPropFalseElim : MSimpRule := fun c => do
  let c ← loadClause c
  let mut newLits : Array Lit := #[]
  -- If c.lits[i] is `False = True` or `True = False`, then refs[i] = none
  -- If c.lits[i] isn't `False = True` or `True = False`,then refs[i] = some j where newLits[j] = c.lits[i]
  let mut refs : Array (Option Nat) := #[]
  for lit in c.lits do
    if (← runMetaAsRuleM (isFalsePropLiteral lit)) then
      refs := refs.push none
    else
      refs := refs.push (some newLits.size)
      newLits := newLits.push lit
  if (newLits.size = c.lits.size) then
    trace[Simp.identPropFalseElim] "Returning Unapplicable on {c.lits}"
    return Unapplicable
  else
    trace[Simp.identPropFalseElim] "Succeeded on {c.lits}, yielding {newLits}"
    return Applied [(MClause.mk newLits, some (mkIdentPropFalseElimProof refs))]

end Duper