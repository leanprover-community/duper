import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean

theorem foo (f g : Nat → Nat → Nat) (h : f = g) (a b : Nat) : f a b = g a b :=
  congrFun (congrFun h a) b

def mkArgumentCongruenceProof (i : Nat) (mVarTys : Array Expr)
  (premises : List Expr) (parents : List ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        let newMVars ← (mVarTys.map some).mapM Meta.mkFreshExprMVar
        let newFVars ← newMVars.mapM Lean.instantiateMVars
        let cj := cLits[j]!
        let pj := lit
        let cjl := cj.lhs
        let pjl ← Meta.mkAppM' pj.lhs newMVars
        let able_to_unify ← Meta.unify #[(cjl, pjl)]
        if able_to_unify then
          let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
            let mut pr := h
            for x in newFVars do
              pr ← Meta.mkAppM `congrFun #[pr, x]
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j pr
          caseProofs := caseProofs.push pr
        else
          throwError s!"mkArgumentCongruenceProof:: " ++
                     s!"Unable to unify lhs of conclusion: {cjl} with " ++
                     s!"lhs of parent: {pjl}"
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
        caseProofs := caseProofs.push pr
    
    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def argCongAtLit (c : MClause) (i : Nat) : RuleM Unit :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]!
    let able_to_unify ← unify #[(lit.lhs, lit.rhs)]
    if able_to_unify && (← strictlyEligible c i) then -- TODO: Eligibility
      let ty ← inferType lit.lhs
      let (es, _, _) ← forallMetaTelescope ty
      let lhs := lit.lhs; let rhs := lit.rhs;
      let mut newMVars := #[]; let mut mVarTys := #[]
      for e in es do
        newMVars := newMVars.push (← mkFreshExprMVar e)
        mVarTys := mVarTys.push e
        let newlhs ← mkAppM' lhs newMVars
        let newrhs ← mkAppM' rhs newMVars
        let newlit := { lit with lhs := newlhs,
                                 rhs := newrhs,
                                 ty  := ← inferType lhs}
        let c' := c.replaceLit! i newlit
        yieldClause c' "argument congruence"
          (mkProof := mkArgumentCongruenceProof i mVarTys)


def argCong (c : MClause) : RuleM Unit := do
  for i in [:c.lits.size] do
    if c.lits[i]!.sign = true then
      argCongAtLit c i

open ProverM

def performArgCong (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "ArgCong inferences with {givenClause}"
  performInference argCong givenClause

end Duper