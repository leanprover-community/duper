import Duper.RuleM
import Duper.Selection
import Duper.Util.Misc
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean
open Meta

initialize registerTraceClass `Rule.fluidSup

def mkFluidSupProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (mainPremisePos : ClausePos)
  (givenIsMain : Bool) (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    sorry

def fluidSupWithPartner (mainPremise : MClause) (mainPremiseNum : Nat) (mainPremiseSubterm : Expr)
  (mainPremisePos : ClausePos) (mainPremiseEligibility : Eligibility) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) (sidePremiseEligibility : Eligibility) (given : Clause) (givenIsMain : Bool) : RuleM (Array ClauseStream) := do
  Core.checkMaxHeartbeats "fluidSup"
  withoutModifyingMCtx $ do
    let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
    let restOfSidePremise := sidePremise.eraseIdx sidePremiseLitIdx

    let freshFunctionVarInputType := sidePremiseLit.ty
    let freshFunctionVarOutputType ← inferType mainPremiseSubterm
    let freshFunctionVar ← mkFreshExprMVar $ Expr.forallE .anonymous freshFunctionVarInputType freshFunctionVarOutputType default
    let freshFunctionVarWithLhs := .app freshFunctionVar sidePremiseLit.lhs
    let freshFunctionVarWithRhs := .app freshFunctionVar sidePremiseLit.rhs

    /-
      To efficiently approximate condition 7 in https://matryoshka-project.github.io/pubs/hosup_report.pdf, if the main
      premise literal is positive and the main premise subterm is directly below the equality, then we require that the
      main premise's clause id is less than or equal to the side premise's clause id (as an arbitrary tiebreaker).
    -/
    if mainPremise.lits[mainPremisePos.lit]!.sign && mainPremisePos.pos == #[] && mainPremiseNum > sidePremiseNum then
      return #[]

    let loaded ← getLoadedClauses
    let ug ← unifierGenerator #[(mainPremiseSubterm, freshFunctionVarWithLhs)]
    let yC := do
      setLoadedClauses loaded
      let sidePremiseFinalEligibility ←
        eligibilityPostUnificationCheck sidePremise false sidePremiseLitIdx sidePremiseEligibility (strict := true)
      if not sidePremiseFinalEligibility then return none
      let mainPremiseFinalEligibility ←
        eligibilityPostUnificationCheck mainPremise false mainPremisePos.lit mainPremiseEligibility
          (strict := mainPremise.lits[mainPremisePos.lit]!.sign)
      if not mainPremiseFinalEligibility then return none

      -- Even though we did preliminary comparison checks before unification, we still need to do comparison checks after unification
      let sidePremiseLhs ← instantiateMVars sidePremiseLit.lhs
      let sidePremiseRhs ← instantiateMVars sidePremiseLit.rhs
      let sidePremiseComparison ← compare sidePremiseLhs sidePremiseRhs false
      if sidePremiseComparison == Comparison.LessThan || sidePremiseComparison == Comparison.Equal then
        return none

      let mainPremiseLhs := mainPremise.lits[mainPremisePos.lit]!.getSide mainPremisePos.side
      let mainPremiseRhs := mainPremise.lits[mainPremisePos.lit]!.getOtherSide mainPremisePos.side
      let mainPremiseComparison ← compare mainPremiseLhs mainPremiseRhs false
      if mainPremiseComparison == Comparison.LessThan || mainPremiseComparison == Comparison.Equal then
        return none

      -- Checking Sup condition 9 in https://matryoshka-project.github.io/pubs/hosup_report.pdf
      if sidePremiseLhs.isFullyAppliedLogicalSymbol then return none

      -- Checking Sup condition 10 in https://matryoshka-project.github.io/pubs/hosup_report.pdf
      if sidePremiseRhs == mkConst ``False && (!mainPremise.lits[mainPremisePos.lit]!.sign || mainPremisePos.pos != #[]) then return none

      -- Checking fluidSup condition 4
      let freshFunctionVarWithLhs ← Core.betaReduce freshFunctionVarWithLhs
      let freshFunctionVarWithRhs ← Core.betaReduce freshFunctionVarWithRhs
      if (freshFunctionVarWithLhs == freshFunctionVarWithRhs) then return none

      let mainPremiseReplaced ← mainPremise.replaceAtPos! mainPremisePos freshFunctionVarWithRhs
      if mainPremiseReplaced.isTrivial then
        trace[Rule.fluidSup] "trivial: {mainPremiseReplaced.lits}"
        return none

      let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
      let res := MClause.append restOfSidePremise mainPremiseReplaced
      let mkProof := mkFluidSupProof sidePremiseLitIdx sidePremiseSide mainPremisePos givenIsMain
      trace[Rule.fluidSup]
        m!"FluidSup successfully yielded {res.lits} from mainPremise: {mainPremise.lits} (lit : {mainPremisePos.lit}) " ++
        m!"and sidePremise: {sidePremise.lits} (lit : {sidePremiseLitIdx})."
      some <$> yieldClause res "fluidSup" none
    return #[ClauseStream.mk ug given yC "fluidSup"]

def fluidSupWithGivenAsSide (given : Clause) (mainPremiseIdx : RootCFPTrie) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) (sidePremiseEligibility : Eligibility) : RuleM (Array ClauseStream) := do
  let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
  let potentialPartners ← mainPremiseIdx.getUnificationPartners sidePremiseLit.lhs
  let mut streams := #[]
  for (mainClauseNum, mainClause, mainPos, mainClauseEligibilityOpt) in potentialPartners do
    let mainClauseEligibility ←
      match mainClauseEligibilityOpt with
      | some eligibility => pure eligibility
      | none => throwError "Eligibility not correctly stored in fluidSupMainPremiseIdx"
    let newStreams ← withoutModifyingLoadedClauses $ do
      let c ← loadClause mainClause
      fluidSupWithPartner c mainClauseNum (← c.getAtPos! mainPos) mainPos mainClauseEligibility sidePremise sidePremiseNum sidePremiseLitIdx
        sidePremiseSide sidePremiseEligibility given (givenIsMain := false)
    streams := streams.append newStreams
  return streams

def fluidSupWithGivenAsMain (given : Clause) (e : Expr) (pos : ClausePos) (sidePremiseIdx : RootCFPTrie)
  (mainPremise : MClause) (mainPremiseNum : Nat) (mainPremiseEligibility : Eligibility) : RuleM (Array ClauseStream) := do
  let potentialPartners ← sidePremiseIdx.getUnificationPartners e
  let mut streams := #[]
  for (sideClauseNum, sideClause, sidePos, sideClauseEligibilityOpt) in potentialPartners do
    let sideClauseEligibility ←
      match sideClauseEligibilityOpt with
      | some eligibility => pure eligibility
      | none => throwError "Eligibility not correctly stored in supSidePremiseIdx"
    let newStreams ← withoutModifyingLoadedClauses $ do
      let c ← loadClause sideClause
      fluidSupWithPartner mainPremise mainPremiseNum e pos mainPremiseEligibility c sideClauseNum sidePos.lit sidePos.side sideClauseEligibility given (givenIsMain := true)
    streams := streams.append newStreams
  return streams

def fluidSup (mainPremiseIdx : RootCFPTrie) (sidePremiseIdx : RootCFPTrie) (given : Clause) (givenClause : MClause)
  (givenClauseNum : Nat) : RuleM (Array ClauseStream) := do
  let mut streams := #[]
  -- With given clause as side premise:
  for i in [:givenClause.lits.size] do
    let litEligibility ← eligibilityPreUnificationCheck givenClause true i
    if givenClause.lits[i]!.sign = true && (litEligibility == Eligibility.eligible || litEligibility == Eligibility.potentiallyEligible) then
      for side in #[LitSide.lhs, LitSide.rhs] do
        let flippedLit := givenClause.lits[i]!.makeLhs side
        if (← RuleM.compare flippedLit.lhs flippedLit.rhs true) == Comparison.LessThan then
          continue
        let cs ← fluidSupWithGivenAsSide given mainPremiseIdx givenClause givenClauseNum i side litEligibility
        streams := streams.append cs
  -- With given clause as main premise
  let cs ← givenClause.foldGreenM fun acc e pos => do
      let givenClauseLit := givenClause.lits[pos.lit]!.makeLhs pos.side
      let litEligibility ← eligibilityPreUnificationCheck givenClause true pos.lit
      let sideComparison ← RuleM.compare givenClauseLit.lhs givenClauseLit.rhs true
      if (not (isFluidOrDeep givenClause e)) || litEligibility == Eligibility.notEligible || sideComparison == Comparison.LessThan then
        return acc
      else
        let cs ← fluidSupWithGivenAsMain given e pos sidePremiseIdx givenClause givenClauseNum litEligibility
        return acc.append cs
    #[]
  return streams.append cs