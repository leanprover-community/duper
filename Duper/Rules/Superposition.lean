import Duper.ProverM
import Duper.RuleM
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean

-- TODO: Pass in the clauses later?
def mkSuperpositionProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (givenIsMain : Bool) 
    (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    
    let mainParentLits := if givenIsMain then parentsLits[0] else parentsLits[1]
    let sideParentLits := if givenIsMain then parentsLits[1] else parentsLits[0]
    let appliedMainPremise := if givenIsMain then appliedPremises[0] else appliedPremises[1]
    let appliedSidePremise := if givenIsMain then appliedPremises[1] else appliedPremises[0]

    let mut caseProofsSide := #[]
    for j in [:sideParentLits.size] do
      if j == sidePremiseLitIdx then
        let eqLit := sideParentLits[j]
        let pr ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
          let eq := if sidePremiseLitSide == LitSide.rhs 
                      then ← Meta.mkAppM ``Eq.symm #[heq] 
                      else heq
          let mut caseProofsMain : Array Expr := #[]
          for i in [:mainParentLits.size] do
            let lit := mainParentLits[i]
            let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
              let idx := sideParentLits.size - 1 + i
              let abstr ← Meta.kabstract lit.toExpr $ eqLit.getSide sidePremiseLitSide
              let abstr := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstr
              let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstr,eq], h]
              Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx $ rwproof
            caseProofsMain := caseProofsMain.push $ pr
          let r ← orCases (mainParentLits.map Lit.toExpr) caseProofsMain
          Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
        caseProofsSide := caseProofsSide.push $ pr
      else
        let lit := sideParentLits[j]
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ sidePremiseLitIdx then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofsSide := caseProofsSide.push $ pr

    let r ← orCases (sideParentLits.map Lit.toExpr) caseProofsSide
    let proof ← Meta.mkLambdaFVars xs $ mkApp r appliedSidePremise
    -- Meta.mkLambdaFVars xs $ ← Lean.Meta.mkSorry body (synthetic := true)
    return proof

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) 
    (sidePremise : MClause) (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide) (givenIsMain : Bool): RuleM Unit := do
  Core.checkMaxHeartbeats "superposition"
  withoutModifyingMCtx $ do
    let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx].makeLhs sidePremiseSide
    let restOfSidePremise := sidePremise.eraseIdx sidePremiseLitIdx
    if mainPremiseSubterm.isMVar then
      return ()
    if not $ ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)] then
      return ()
    let lhs ← instantiateMVars sidePremiseLit.lhs
    let rhs ← instantiateMVars sidePremiseLit.rhs
    if (← compare lhs rhs) == Comparison.LessThan then
      return ()

    let sidePremise ← sidePremise.mapM fun e => instantiateMVars e
    if not $ ← runMetaAsRuleM $ sidePremise.isMaximalLit (← getOrder) sidePremiseLitIdx then
      return ()
    -- TODO: make exception for selected lits

    -- TODO: also check maximality for main premise

    let mainPremiseReplaced ← 
      mainPremise.mapM fun e => do
        replace (← instantiateMVars e) lhs rhs --TODO: Replace only green subterms

    -- if mainPremiseReplaced.isTrivial then
    --   trace[Prover.debug] "trivial: {mainPremiseReplaced.lits}"
      -- return ()
      
    let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
    let res := MClause.append restOfSidePremise mainPremiseReplaced 
    yieldClause res "superposition" 
      (mkProof := mkSuperpositionProof sidePremiseLitIdx sidePremiseSide givenIsMain)

def superpositionAtLit (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
      (sidePremise : MClause) (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide) : 
    RuleM Unit := do
  let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx].makeLhs sidePremiseSide
  trace[Rule.debug] "Superposition inferences at literal {sidePremiseLit}"
  let potentialPartners ← mainPremiseIdx.getUnify sidePremiseLit.lhs
  -- trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      superpositionAtLitWithPartner c (c.getAtPos! partnerPos)
          sidePremise sidePremiseLitIdx sidePremiseSide (givenIsMain := false)

def superpositionAtExpr (e : Expr) (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos)
    (mainPremise : MClause) : RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at expression {e}"
  let potentialPartners ← sidePremiseIdx.getUnify e
  -- trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      superpositionAtLitWithPartner mainPremise e
          c partnerPos.lit partnerPos.side (givenIsMain := true)
          

def superposition 
    (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (givenMClause : MClause) : RuleM Unit := do
  -- With given clause as side premise:
  -- trace[Rule.debug] "Superposition inferences with {givenClause} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true && litSelectedOrNothingSelected givenMClause i
    then 
      let restOfGivenClause := givenMClause.eraseIdx i
      for side in #[LitSide.lhs, LitSide.rhs] do
        let flippedLit := givenMClause.lits[i].makeLhs side
        if (← RuleM.compare flippedLit.lhs flippedLit.rhs) == Comparison.LessThan then
          continue
        let cs ← superpositionAtLit mainPremiseIdx givenMClause i side
  -- With given clause as main premise
  -- trace[Rule.debug] "Superposition inferences with {givenClause} as main premise"
  givenMClause.foldGreenM fun acc e pos => do
      superpositionAtExpr e sidePremiseIdx givenMClause
    ()
  -- TODO: What about inference with itself?
      
open ProverM

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause}"
  let mainPremiseIdx ← getSupMainPremiseIdx
  let sidePremiseIdx ← getSupSidePremiseIdx
  performInference (superposition mainPremiseIdx sidePremiseIdx) givenClause


end Duper
