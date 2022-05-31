import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Std
open RuleM
open SimpResult
open Lean

def mkElimResolvedLitProof (refs : Array (Option Nat)) (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]
    let appliedPremise := appliedPremises[0]

    let mut proofCases : Array Expr := #[]
    for i in [:parentLits.size] do {
      let lit := parentLits[i]
      if ((not lit.sign) && lit.lhs == lit.rhs) then
        -- lit has the form t ≠ t
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let proofCase := mkApp2 (mkConst ``rfl [lit.lvl]) lit.ty lit.lhs
          let proofCase := mkApp h proofCase
          let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
          Meta.mkLambdaFVars #[h] proofCase
        proofCases := proofCases.push proofCase
      else
        -- lit does not have the form t ≠ t, so refs[i] should have the value (some j) where parentLits[i] == c[j]
        match refs[i] with
        | none =>
          panic! "There is a bug in ElimResolvedLit.lean (The refs invariant is not satisfied)"
        | some j => 
          let proofCase ← Meta.withLocalDeclD `h parentLits[i].toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    }
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

-- Eliminate resolved literals (i.e. literals of the form t ≠ t) (Deletion of Resolved Literals: (DR))
def elimResolvedLit : MSimpRule := fun c => do
  --trace[Simp.debug] "Calling elimResolvedLit on clause {c.lits}"
  let mut newLits : Array Lit := #[]
  -- If c.lits[i] is resolved (i.e. of the form t ≠ t), then refs[i] = none
  -- If c.lits[i] isn't resolved, then refs[i] = some j where newLits[j] = c.lits[i]
  let mut refs : Array (Option Nat) := #[]
  for lit in c.lits do {
    if ((not lit.sign) && lit.lhs == lit.rhs) then
      refs := refs.push none -- c.lits[i] is a resolved literal
    else
      refs := refs.push (some newLits.size)
      newLits := newLits.push lit -- Only add the literal if it does not have the form t ≠ t
  }
  if (newLits.size = c.lits.size) then
    return Unapplicable
  else
    trace[Simp.debug] "elimResolvedLit returning Applied with the newLits: {newLits}"
    return Applied [(MClause.mk newLits, some (mkElimResolvedLitProof refs))]

end Duper