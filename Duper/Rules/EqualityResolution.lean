import Duper.RuleM
import Duper.MClause
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean

def mkEqualityResolutionProof (i : Nat) (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        -- lit has the form t ≠ t
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let pr := mkApp2 (mkConst ``rfl [lit.lvl]) lit.ty lit.lhs
          let pr := mkApp h pr
          let pr := mkApp2 (mkConst ``False.elim [levelZero]) body pr
          Meta.mkLambdaFVars #[h] pr
        caseProofs := caseProofs.push pr
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        -- caseProofs := caseProofs.push $ ← Lean.Meta.mkSorry (← Meta.mkArrow lit.toExpr body) (synthetic := true)
        caseProofs := caseProofs.push pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def equalityResolutionAtLit (given : Clause) (c : MClause) (i : Nat) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]!
    let eligibility ← eligibilityPreUnificationCheck c i
    if eligibility == Eligibility.notEligible then return #[]
    let loaded ← getLoadedClauses
    let ug ← unifierGenerator #[(lit.lhs, lit.rhs)]
    let yC := do
      setLoadedClauses loaded
      if (← eligibilityPostUnificationCheck c i eligibility) then
        return none
      let c := c.eraseLit i
      some <$> yieldClause c "equality resolution" 
        (mkProof := mkEqualityResolutionProof i)
    return #[ClauseStream.mk ug given yC]
      
def equalityResolution (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[Prover.debug] "EqRes inferences with {c.lits}"
  let mut streams := #[]
  for i in [:c.lits.size] do
    if c.lits[i]!.sign = false then
      streams := streams.append (← equalityResolutionAtLit given c i)
  return streams

end Duper
