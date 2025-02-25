import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

set_option linter.unusedVariables false

namespace Duper

open Lean
open Meta
open RuleM
open SimpResult
open Comparison

initialize Lean.registerTraceClass `duper.rule.demodulation

def mkDemodulationProof (sidePremiseLhs : LitSide) (mainPremisePos : ClausePos) (isForward : Bool)
  (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs

    let mainParentLits := if isForward then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if isForward then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if isForward then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if isForward then appliedPremises[0]! else appliedPremises[1]!

    let eqLit := sideParentLits[0]!

    let proof ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
      let mut caseProofs : Array Expr := Array.mkEmpty mainParentLits.size
      let eq ←
        if sidePremiseLhs == LitSide.rhs then Meta.mkAppM ``Eq.symm #[heq]
        else pure heq
      for i in [:mainParentLits.size] do
        let lit := mainParentLits[i]!
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

/- Note: I am implementing Schulz's side conditions for RP and RN, but only approximately.
   The side conditions are:
   - If mainPremise.lits[mainPremisePos.lit].sign is true (i.e. we are in the RP case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
      3. At least one of the following must be false:
        - mainPremise.lits[mainPremisePos.lit] is eligible for paramodulation (note, we replace this by the literal being maximal)
        - mainPremise.lits[mainPremisePos.lit].side > mainPremise.lits[mainPremisePos.lit].otherside
        - mainPremiseSubterm = λ
        - σ is a variable renaming (note, we do not check this because it's unclear if this is actually complete)
   - If mainPremise.lits[mainPremisePos.lit].sign is false (i.e. we are in the RN case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
-/
def forwardDemodulationWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId) (mainPremiseSubterm : Expr)
  (mainPremisePos : ClausePos) (sidePremise : MClause) (sidePremiseLhs : LitSide) :
  RuleM (Option (MClause × Option ProofReconstructor)) := do
  Core.checkMaxHeartbeats "forward demodulation"
  let sidePremiseLit := sidePremise.lits[0]!.makeLhs sidePremiseLhs
  if (mainPremise.lits[mainPremisePos.lit]!.sign) then
    let isMaximalLit ← mainPremise.isMaximalLit (← getOrder) true mainPremisePos.lit
    let mainPremiseSideComparison ← compare
      (mainPremise.lits[mainPremisePos.lit]!.getSide mainPremisePos.side)
      (mainPremise.lits[mainPremisePos.lit]!.getOtherSide mainPremisePos.side)
      true -- alreadyReduced is true because we have not modified the main premise yet (we have not called performMatch yet)
    let atTopPos := Array.isEmpty mainPremisePos.pos
    if isMaximalLit && (mainPremiseSideComparison == Comparison.GreaterThan) && atTopPos then
      return none -- Cannot perform demodulation because Schulz's side conditions are not met
  if not (← performMatch #[(mainPremiseSubterm, sidePremiseLit.lhs)] mainPremiseMVarIds) then
    return none -- Cannot perform demodulation because we could not match sidePremiseLit.lhs to mainPremiseSubterm
  if (← compare sidePremiseLit.lhs sidePremiseLit.rhs false) != Comparison.GreaterThan then
    return none -- Cannot perform demodulation because side condition 2 listed above is not met
  let some mainPremiseReplaced ← mainPremise.replaceAtPosUpdateType? mainPremisePos sidePremiseLit.rhs
    | return none -- If `mainPremise` cannot be safely changed at `mainPremisePos`, then don't apply demodulation
  return some (mainPremiseReplaced, (some $ mkDemodulationProof sidePremiseLhs mainPremisePos true))

def forwardDemodulationAtExpr (e : Expr) (pos : ClausePos) (sideIdx : RootCFPTrie) (givenMainClause : MClause)
  (mainClauseMVarIds : Array MVarId) : RuleM (Option (Array (Clause × Proof))) := do
  let potentialPartners ← sideIdx.getMatchFromPartners e
  for (partnerClauseNum, partnerClause, partnerPos, _) in potentialPartners do
    let (mclause, cToLoad) ← prepLoadClause partnerClause
    match ← forwardDemodulationWithPartner givenMainClause mainClauseMVarIds e pos mclause partnerPos.side with
    | none => continue
    | some res =>
      -- forwardDemodulationWithPartner succeeded so we need to add cToLoad to loadedClauses in the state
      setLoadedClauses ((← getLoadedClauses).push cToLoad)
      let cp ← yieldClause res.1 "forward demodulation" res.2
      trace[duper.rule.demodulation] "Main clause: {givenMainClause.lits} at lit: {pos.lit} at expression: {e}"
      trace[duper.rule.demodulation] "Side clause: {partnerClause} at lit: {partnerPos.lit}"
      trace[duper.rule.demodulation] "Result: {res.1.lits}"
      return some #[cp]
  return none

/-- Performs rewriting of positive and negative literals (demodulation) with the given clause c as the main clause. We only attempt
    to use c as the main clause (rather than attempt to use it as a side clause as well) because if we used c as a side clause, we
    would remove the wrong clause from the active set (we would remove c rather than the main clause that c is paired with). c will
    considered as a side clause in the backward simplificaiton loop (i.e. in backwardDemodulation) -/
def forwardDemodulation (sideIdx : RootCFPTrie) : MSimpRule := fun c => do
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc e pos => do
    match acc with
    | some cp => return some cp -- If forwardDemodulationAtExpr ever succeeds, just return on first success
    | none => forwardDemodulationAtExpr e pos sideIdx c cMVarIds
  c.foldGreenM fold_fn none

/- Attempts to perform backward demodulation with the given mainPremise and sidePremise. Returns true iff successful.
   Note: I am implementing Schulz's side conditions for RP and RN, but only approximately.
   The side conditions are:
   - If mainPremise.lits[mainPremisePos.lit].sign is true (i.e. we are in the RP case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
      3. At least one of the following must be false:
        - mainPremise.lits[mainPremisePos.lit] is eligible for paramodulation (note, we replace this by the literal being maximal)
        - mainPremise.lits[mainPremisePos.lit].side > mainPremise.lits[mainPremisePos.lit].otherside
        - mainPremiseSubterm = λ (note, we do not check this, so we may miss some opportunities for demodulation, but I don't believe
          we ever perform demodulation when it should not be allowed)
        - σ is a variable renaming (note, we do not check this, so we may miss some opportunities for demodulation, but I don't
          believe we ever perform demodulation when it should not be allowed)
   - If mainPremise.lits[mainPremisePos.lit].sign is false (i.e. we are in the RN case), then all of the following must hold:
      1. sidePremise.sidePremiseLhs must match mainPremiseSubterm
      2. sidePremise.sidePremiseLhs must be greater than sidePremise.getOtherSide sidePremiseLhs after matching is performed
-/
def backwardDemodulationWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId) (mainPremiseSubterm : Expr)
  (mainPremisePos : ClausePos) (sidePremise : MClause) (sidePremiseLhs : LitSide) : RuleM (Option (Clause × Proof)) := do
  Core.checkMaxHeartbeats "backward demodulation"
  let sidePremiseLit := sidePremise.lits[0]!.makeLhs sidePremiseLhs
  if (mainPremise.lits[mainPremisePos.lit]!.sign) then
    let isMaximalLit ← mainPremise.isMaximalLit (← getOrder) true mainPremisePos.lit
    let mainPremiseSideComparison ← compare
      (mainPremise.lits[mainPremisePos.lit]!.getSide mainPremisePos.side)
      (mainPremise.lits[mainPremisePos.lit]!.getOtherSide mainPremisePos.side)
      true -- alreadyReduced is true because we have not modified the main premise yet (we have not called performMatch yet)
    let atTopPos := Array.isEmpty mainPremisePos.pos
    if isMaximalLit && (mainPremiseSideComparison == Comparison.GreaterThan) && atTopPos then
      return none -- Cannot perform demodulation because Schulz's side conditions are not met
  if not (← performMatch #[(mainPremiseSubterm, sidePremiseLit.lhs)] mainPremiseMVarIds) then
    return none -- Cannot perform demodulation because we could not match sidePremiseLit.lhs to mainPremiseSubterm
  if (← compare sidePremiseLit.lhs sidePremiseLit.rhs false) != Comparison.GreaterThan then
    return none -- Cannot perform demodulation because side condition 2 listed above is not met
  let some mainPremiseReplaced ← mainPremise.replaceAtPosUpdateType? mainPremisePos sidePremiseLit.rhs
    | return none -- If `mainPremise` cannot be safely changed at `mainPremisePos`, then don't apply demodulation
  trace[duper.rule.demodulation] "(Backward) Main mclause (after matching): {mainPremise.lits}"
  trace[duper.rule.demodulation] "(Backward) Side clause (after matching): {sidePremise.lits}"
  trace[duper.rule.demodulation] "(Backward) Result: {mainPremiseReplaced.lits}"
  some <$> yieldClause mainPremiseReplaced "backward demodulation" (some $ mkDemodulationProof sidePremiseLhs mainPremisePos false)

/-- Performs rewriting of positive and negative literals (demodulation) with the given clause as the side clause. Returns the list of
    original clauses that are to be removed by backward simplification. -/
def backwardDemodulation (mainIdx : RootCFPTrie) : BackwardMSimpRule := fun givenSideClause => do
  let givenSideClause ← loadClause givenSideClause
  if givenSideClause.lits.size != 1 || not givenSideClause.lits[0]!.sign then return #[]
  let l := givenSideClause.lits[0]!
  let c ← compare l.lhs l.rhs true -- alreadyReduced is true because we have not modified l.lhs or l.rhs yet
  if (c == Incomparable || c == Equal) then return #[]

  let givenSideClauseLhs := -- givenSideClause.getSide givenSideClauseLhs is will function as the lhs of the side clause
    if c == GreaterThan then LitSide.lhs
    else LitSide.rhs
  let potentialPartners ← mainIdx.getMatchOntoPartners (Lit.getSide l givenSideClauseLhs)
  let mut result := #[]
  let mut clausesToRemove := #[]

  for (partnerClauseNum, partnerClause, partnerPos, _) in potentialPartners do
    -- Since demodulation is a simplification rule, we shouldn't perform multiple demodulation calls with the same partner clause
    if clausesToRemove.contains partnerClause then continue
    let backwardDemodulationRes ←
      withoutModifyingLoadedClauses do
        withoutModifyingMCtx do
          let (mclauseMVarIds, mclause) ← loadClauseCore partnerClause
          let mclauseMVarIds := mclauseMVarIds.map Expr.mvarId!
          backwardDemodulationWithPartner mclause mclauseMVarIds (← mclause.getAtPos! partnerPos) partnerPos givenSideClause givenSideClauseLhs
    if let some cp := backwardDemodulationRes then
      result := result.push (partnerClause, some cp)
      clausesToRemove := clausesToRemove.push partnerClause

  return result
