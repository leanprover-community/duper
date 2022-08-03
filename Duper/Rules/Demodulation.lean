import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.demodulation

def mkForwardDemodulationProof (sidePremiseLhs : LitSide) (mainPremisePos : ClausePos)
  (premises : Array Expr) (parents: Array ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs

    let mainParentLits := parentsLits[0]
    let sideParentLits := parentsLits[1]
    let appliedMainPremise := appliedPremises[0]
    let appliedSidePremise := appliedPremises[1]

    let eqLit := sideParentLits[0]

    let proof ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
      let mut caseProofs : Array Expr := #[]
      let eq :=
        if sidePremiseLhs == LitSide.rhs then ← Meta.mkAppM ``Eq.symm #[heq]
        else heq
      for i in [:mainParentLits.size] do
        let lit := mainParentLits[i]
        let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if(i == mainPremisePos.lit) then
            let litPos : LitPos := {side := mainPremisePos.side, pos := mainPremisePos.pos}
            let abstrLit ← (lit.abstractAtPos! litPos)
            let abstrExp := abstrLit.toExpr
            let abstrLam := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstrExp
            let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, eq], h]
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i $ rwproof
          else
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
        caseProofs := caseProofs.push $ pr
      let r ← orCases (mainParentLits.map Lit.toExpr) caseProofs
      Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
    let proof ← Meta.mkLambdaFVars xs $ mkApp proof appliedSidePremise
    return proof

/- Note: I am implementing Schulz's side conditions for RP and RN, except for the condition that RP is allowed if p ≠ λ or σ 
   is a variable renaming. The reason for this is that I suspect I will just have to change the side conditions later to match
   "Superposition for Full Higher-Order Logic", so there's little point in being super precise about implementing Schulz's more
   annoying side conditions.

   So the side conditions I'm implementing are:
   - If mainPremise.lits[mainPremisePos.lit].sign is true (i.e. we are in the RP case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
      3. mainPremise.lits[mainPremisePos.lit] must not be eligible for paramodulation (in Schulz's paper, we could instead have
         p ≠ λ or σ not be a variable renaming, but these are the conditions I'm not implementing right now)
   - If mainPremise.lits[mainPremisePos.lit].sign is false (i.e. we are in the RN case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
-/
def forwardDemodulationWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) (mainPremisePos : ClausePos)
  (sidePremise : MClause) (sidePremiseLhs : LitSide) (givenClauseIsMainPremise : Bool) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  Core.checkMaxHeartbeats "forward demodulation"
  let sidePremiseLit := sidePremise.lits[0].makeLhs sidePremiseLhs
  if (mainPremise.lits[mainPremisePos.lit].sign && (← eligibleForParamodulation mainPremise mainPremisePos.lit)) then
    return Unapplicable -- Cannot perform demodulation because Schulz's side conditions are not met
  if not (← performMatch #[(mainPremiseSubterm, sidePremiseLit.lhs)]) then
    return Unapplicable -- Cannot perform demodulation because we could not match sidePremiseLit.lhs to mainPremiseSubterm
  if (← compare sidePremiseLit.lhs sidePremiseLit.rhs) != Comparison.GreaterThan then
    return Unapplicable -- Cannot perform demodulation because side condition 2 listed above is not met
  let mainPremiseReplaced ← mainPremise.replaceAtPos! mainPremisePos $ ← instantiateMVars sidePremiseLit.rhs
  return Applied [(mainPremiseReplaced, (some $ mkForwardDemodulationProof sidePremiseLhs mainPremisePos))]

def forwardDemodulationAtExpr (e : Expr) (pos : ClausePos) (sideIdx : ProverM.ClauseDiscrTree ClausePos) (givenMainClause : MClause) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  let potentialPartners ← sideIdx.getMatch e
  for (partnerClause, partnerPos) in potentialPartners do
    let (mclause, cToLoad) ← prepLoadClause partnerClause
    match ← forwardDemodulationWithPartner givenMainClause e pos mclause partnerPos.side true with
    | Unapplicable => continue
    | Applied res =>
      -- forwardDemodulationWithPartner succeeded so we need to add cToLoad to loadedClauses in the state
      setLoadedClauses ((← getLoadedClauses).push cToLoad)
      trace[Rule.demodulation] "Main clause: {givenMainClause.lits} at lit: {pos.lit} at expression: {e}"
      trace[Rule.demodulation] "Side clause: {partnerClause} at lit: {partnerPos.lit}"
      trace[Rule.demodulation] "Result: {(List.get! res 0).1.lits}"
      return Applied res
    | Removed => throwError "Invalid demodulation result"
  return Unapplicable

/-- Performs rewriting of positive and negative literals (demodulation) with the given clause c as the main clause. We only attempt
    to use c as the main clause (rather than attempt to use it as a side clause as well) because if we used c as a side clause, we
    would remove the wrong clause from the active set (we would remove c rather than the main clause that c is paired with). c will 
    considered as a side clause in the backward simplificaiton loop (i.e. in backwardDemodulation) -/
def forwardDemodulation (sideIdx : ProverM.ClauseDiscrTree ClausePos) : MSimpRule := fun c => do
  let fold_fn := fun acc e pos => do
    match acc with
    | Unapplicable => forwardDemodulationAtExpr e pos sideIdx c
    | Applied res => return Applied res -- If forwardDemodulationAtExpr ever succeeds, just return the first success
    | Removed => throwError "Invalid demodulation result"
  c.foldM fold_fn Unapplicable