import Duper.RuleM
import Duper.Selection
import Duper.Util.Misc
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean
open Meta

initialize registerTraceClass `Rule.fluidSup

def fluidSupWithPartner (mainPremise : MClause) (mainPremiseNum : Nat) (mainPremiseSubterm : Expr)
  (mainPremisePos : ClausePos) (mainPremiseEligibility : Eligibility) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) (sidePremiseEligibility : Eligibility) (given : Clause) (givenIsMain : Bool) : RuleM (Array ClauseStream) := do
  sorry

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