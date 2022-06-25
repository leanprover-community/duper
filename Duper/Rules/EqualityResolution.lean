import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean

def mkEqualityResolutionProof (i : Nat) (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]
    let appliedPremise := appliedPremises[0]

    let mut caseProofs := #[]
    for j in [:parentLits.size] do
      let lit := parentLits[j]
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
        caseProofs := caseProofs.push $ pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def equalityResolutionAtLit (c : MClause) (i : Nat) : RuleM Unit :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]
    let able_to_unify ← unify #[(lit.lhs, lit.rhs)]
    if able_to_unify && (← eligibleForResolution c i) then -- Need to check eligibility for resolution after unification
      let c := c.eraseLit i
      yieldClause c "equality resolution" 
        (mkProof := mkEqualityResolutionProof i)

def equalityResolution (c : MClause) : RuleM Unit := do
  for i in [:c.lits.size] do
    if c.lits[i].sign = false then
      equalityResolutionAtLit c i

open ProverM

def performEqualityResolution (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "EqRes inferences with {givenClause}"
  performInference equalityResolution givenClause

end Duper
