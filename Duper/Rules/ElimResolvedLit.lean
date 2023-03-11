import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta

initialize Lean.registerTraceClass `Rule.elimResolvedLit

def mkElimResolvedLitProof (refs : List (Option Nat)) (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do {
      let lit := parentLits[i]!
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
        match refs[i]! with
        | none =>
          panic! "There is a bug in ElimResolvedLit.lean (The refs invariant is not satisfied)"
        | some j => 
          let proofCase ← Meta.withLocalDeclD `h parentLits[i]!.toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    }
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Eliminate resolved literals (i.e. literals of the form t ≠ t) (Deletion of Resolved Literals: (DR)) -/
def elimResolvedLit : MSimpRule := fun c => do
  let c ← loadClause c
  /-
    Spec for newLits and refs:
    If c.lits[i] is resolved (i.e. of the form t ≠ t), then refs[i] = none
    If c.lits[i] isn't resolved, then refs[i] = some j where newLits[j] = c.lits[i]
  -/
  let mut newLits : List Lit := []
  let mut refs : List (Option Nat) := []
  for lit in c.lits do {
    if ((not lit.sign) && lit.lhs == lit.rhs) then
      refs := none :: refs -- c.lits[i] is a resolved literal
    else
      refs := (some newLits.length) :: refs
      newLits := lit :: newLits -- Only add the literal if it does not have the form t ≠ t
  }
  -- To achieve the desired spec for newLits and refs, I must reverse them
  newLits := newLits.reverse
  refs := refs.reverse
  if (newLits.length = c.lits.size) then
    return none
  else
    trace[Rule.elimResolvedLit] "elimResolvedLit applied with the newLits: {newLits}"
    let yc ← yieldClause (MClause.mk newLits.toArray) "eliminate resolved literals" (some (mkElimResolvedLitProof refs))
    return some #[yc]

end Duper