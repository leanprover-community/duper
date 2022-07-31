import Duper.ProverM
import Duper.RuleM
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean

inductive Eligibility 
  | eligible 
  | potentially_eligible 
  | not_eligible
deriving Inhabited, BEq, Repr

def mkSuperpositionProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (mainPremisePos : ClausePos)
  (givenIsMain : Bool) (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr := do
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
          let eq :=
            if sidePremiseLitSide == LitSide.rhs then ← Meta.mkAppM ``Eq.symm #[heq]
            else heq
          let mut caseProofsMain : Array Expr := #[]
          for i in [:mainParentLits.size] do
            let lit := mainParentLits[i]
            let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
              let idx := sideParentLits.size - 1 + i
              if(i == mainPremisePos.lit) then
                let litPos : LitPos := {side := mainPremisePos.side, pos := mainPremisePos.pos}
                let abstrLit ← (lit.abstractAtPos! litPos)
                let abstrExp := abstrLit.toExpr
                let abstrLam := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstrExp
                let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, eq], h]
                Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx $ rwproof
              else
                Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
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
    return proof

/-- The side premise must be strictly eligible in order to proceed for superposition. This means that either:
  1. sidePremise.lits[sidePremiseLitIdx] is a selected literal in sidePremise
  2. There are no selected literals in sidePremise and sidePremise.lits[sidePremiseLitIdx] is strictly maximal in sidePremise

  Checking whether sidePremise.lits[sidePremiseLitIdx] is a selected literal and whether there are no selected literals in sidePremise
  must occur before unification. Checking whether sidePremise.lits[sidePremiseLitIdx] is strictly maximal in sidePremise must occur after,
  but we can do a partial check before to see whether it's even possible for sidePremise.lits[sidePremiseLitIdx] to be strictly maximal.
  The benefit of this is that if we can already see that sidePremise.lits[sidePremiseLitIdx] can never be strictly maximal under any
  substituttion, then we can exit superpositionAtLitWithPartner prior to performing the expensive unification operation.
-/
def sidePremiseEligiblePreUnificationCheck (sidePremise : MClause) (sidePremiseLitIdx : Nat) : RuleM Eligibility :=
  let sel := getSelections sidePremise
  if(sel.contains sidePremiseLitIdx) then
    return Eligibility.eligible -- sidePremiseLitIdx is eligible for superposition and the post unification check is not necessary
  else if(sel == []) then do
    if (← runMetaAsRuleM $ sidePremise.canNeverBeMaximal (← getOrder) sidePremiseLitIdx) then
      return Eligibility.not_eligible
    else
      return Eligibility.potentially_eligible -- sidePremiseLitIdx may be eligible but the post unification check is needed to confirm maximality
  else
    return Eligibility.not_eligible

/-- If sidePremiseEligiblePostUnificationCheck is being called, then there are no selected literals in the pre-unification sidePremise, and
    to determine the eligibility of sidePremise.lits[sidePremiseLitIdx], we have to determine whether sidePremise.lits[sidePremiseLitIdx]
    is strictly maximal in sidePremise. sidePremise.lits[sidePremiseLitIdx] is eligible for superposition if it is strictly maximal in
    sidePremise, and is not eligible otherwise.
-/
def sidePremiseEligiblePostUnificationCheck (sidePremise : MClause) (sidePremiseLitIdx : Nat) : RuleM Bool := do
  runMetaAsRuleM $ sidePremise.isMaximalLit (← getOrder) sidePremiseLitIdx (strict := true)

/-- The main premise must be eligible if negative and strictly eligible if positive in order to proceed for superposition. 
    This means that either:
  1. mainPremisePos.lit is a selected literal in mainPremise
  2. There are no selected literals in mainPremise and either:
      - mainPremisePos.lit is negative and nonstrictly maximal in mainPremise
      - mainPremisePos.lit is positive and strictly maximal in mainPremise

  Checking whether mainPremisePos.lit is a selected literal and whether there are no selected literals in mainPremise must occur before
  unification. Checking whether mainPremisePos.lit is (strictly or nonstrictly) maximal in mainPremise must occur after, but we can do
  a partial check before to see whether it's even possible for mainPremisePos.lit to be (strictly or nonstrictly) maximal. The benefit
  of this is that if we can already see that mainPremisePos.lit can never be (strictly or nonstrictly) maximal under any substitution,
  then we can exit superpositionAtLitWithPartner prior to performing the expensive unification operation.
-/
def mainPremiseEligiblePreUnificationCheck (mainPremise : MClause) (mainPremisePos : ClausePos) : RuleM Eligibility :=
  let sel := getSelections mainPremise
  if(sel.contains mainPremisePos.lit) then
    return Eligibility.eligible -- mainPremisePos.lit is eligible for superposition and the post unificaiton check is not necessary
  else if(sel == []) then do
    if (← runMetaAsRuleM $ mainPremise.canNeverBeMaximal (← getOrder) mainPremisePos.lit) then
      return Eligibility.not_eligible
    else
      return Eligibility.potentially_eligible -- mainPremisePos.lit may be eligibile but the post unification check is needed to confirm maximality
  else
    return Eligibility.not_eligible

/-- If mainPremiseEligiblePostUnificationCheck is being called, then there are no selected literals in the pre-unification mainPremise,
    and to determine the eligibility of mainPremisePos.lit, we have to determine whether:
    - mainPremisePos.lit is negative and nonstrictly maximal in mainPremise
    - mainPremisePos.lit is positive and strictly maximal in mainPremise
    If either of the above two cases hold, then mainPremisePos.lit is eligible for superposition. Otherwise, it is not.
-/
def mainPremiseEligiblePostUnificationCheck (mainPremise : MClause) (mainPremisePos : ClausePos) : RuleM Bool := do
  let strictness := mainPremise.lits[mainPremisePos.lit].sign -- strictness is true iff mainPremisePos.lit is positive
  runMetaAsRuleM $ mainPremise.isMaximalLit (← getOrder) mainPremisePos.lit strictness

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) (mainPremisePos : ClausePos)
    (sidePremise : MClause) (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide) (givenIsMain : Bool): RuleM Unit := do
  Core.checkMaxHeartbeats "superposition"
  withoutModifyingMCtx $ do
    let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx].makeLhs sidePremiseSide
    let restOfSidePremise := sidePremise.eraseIdx sidePremiseLitIdx
    if mainPremiseSubterm.isMVar then
      return () 
    
    let sidePremiseEligibility ← sidePremiseEligiblePreUnificationCheck sidePremise sidePremiseLitIdx
    let mainPremiseEligibility ← mainPremiseEligiblePreUnificationCheck mainPremise mainPremisePos

    if sidePremiseEligibility == Eligibility.not_eligible || mainPremiseEligibility == Eligibility.not_eligible then
      return () -- Preunification checks determined ineligibility, so we don't need to bother with unificaiton
    if not $ ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)] then
      return () -- Unification failed, so superposition cannot occur
    if sidePremiseEligibility == Eligibility.potentially_eligible then
      -- Only need to run the post unificaiton check if the side premise is potentially eligible (as opposed to eligible)
      let sidePremiseFinalEligibility ← sidePremiseEligiblePostUnificationCheck sidePremise sidePremiseLitIdx
      if not sidePremiseFinalEligibility then return ()
    if mainPremiseEligibility == Eligibility.potentially_eligible then
      -- Only need to run the post unificaiton check if the main premise is potentially eligible (as opposed to eligible)
      let mainPremiseFinalEligibility ← mainPremiseEligiblePostUnificationCheck mainPremise mainPremisePos
      if not mainPremiseFinalEligibility then return ()
    
    let lhs ← instantiateMVars sidePremiseLit.lhs
    let rhs ← instantiateMVars sidePremiseLit.rhs
    if (← compare lhs rhs) == Comparison.LessThan then
      return ()

    let mainPremiseReplaced ← mainPremise.replaceAtPos! mainPremisePos rhs

    if mainPremiseReplaced.isTrivial then
      trace[Prover.debug] "trivial: {mainPremiseReplaced.lits}"
      return ()
      
    let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
    let res := MClause.append restOfSidePremise mainPremiseReplaced
    yieldClause res "superposition" 
      (mkProof := mkSuperpositionProof sidePremiseLitIdx sidePremiseSide mainPremisePos givenIsMain)

def superpositionAtLit (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
      (sidePremise : MClause) (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide) : 
    RuleM Unit := do
  let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx].makeLhs sidePremiseSide
  trace[Rule.debug] "Superposition inferences at literal {sidePremiseLit}"
  let potentialPartners ← mainPremiseIdx.getUnify sidePremiseLit.lhs
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      superpositionAtLitWithPartner c (c.getAtPos! partnerPos) partnerPos
          sidePremise sidePremiseLitIdx sidePremiseSide (givenIsMain := false)

def superpositionAtExpr (e : Expr) (pos : ClausePos) (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos)
    (mainPremise : MClause) : RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at expression {e}"
  let potentialPartners ← sidePremiseIdx.getUnify e
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      superpositionAtLitWithPartner mainPremise e pos
          c partnerPos.lit partnerPos.side (givenIsMain := true)

def superposition
    (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (givenMClause : MClause) : RuleM Unit := do
  -- With given clause as side premise:
  --trace[Rule.debug] "Superposition inferences with {givenMClause.lits} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true && litSelectedOrNothingSelected givenMClause i
    then
      for side in #[LitSide.lhs, LitSide.rhs] do
        let flippedLit := givenMClause.lits[i].makeLhs side
        if (← RuleM.compare flippedLit.lhs flippedLit.rhs) == Comparison.LessThan then
          continue
        let cs ← superpositionAtLit mainPremiseIdx givenMClause i side
  -- With given clause as main premise
  --trace[Rule.debug] "Superposition inferences with {givenMClause.lits} as main premise"
  givenMClause.foldGreenM fun acc e pos => do
      superpositionAtExpr e pos sidePremiseIdx givenMClause
    ()
  -- TODO: What about inference with itself?
      
open ProverM

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause}"
  let mainPremiseIdx ← getMainPremiseIdx
  let sidePremiseIdx ← getSupSidePremiseIdx
  performInference (superposition mainPremiseIdx sidePremiseIdx) givenClause


end Duper
