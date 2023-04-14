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
  (mainPremisePos : ClausePos) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide)
  (given : Clause) (givenIsMain : Bool) : RuleM (Array ClauseStream) := do
  sorry

def fluidSupWithGivenAsSide (given : Clause) (mainPremiseIdx : RootCFPTrie) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) : RuleM (Array ClauseStream) := do
  let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
  let potentialPartners ← mainPremiseIdx.getUnificationPartners sidePremiseLit.lhs
  let mut streams := #[]
  for (mainClauseNum, mainClause, mainPos) in potentialPartners do
    let newStreams ← withoutModifyingLoadedClauses $ do
      let c ← loadClause mainClause
      let mainLit := c.lits[mainPos.lit]!.makeLhs mainPos.side
      -- TODO: I think that if I index positions correctly, this comparison check should be unnecessary
      if (← RuleM.compare mainLit.lhs mainLit.rhs true) != Comparison.LessThan then
        fluidSupWithPartner c mainClauseNum (← c.getAtPos! mainPos) mainPos sidePremise sidePremiseNum sidePremiseLitIdx sidePremiseSide
          given (givenIsMain := false)
      else
        return #[]
    streams := streams.append newStreams
  return streams

def fluidSupWithGivenAsMain (given : Clause) (e : Expr) (pos : ClausePos) (sidePremiseIdx : RootCFPTrie)
  (mainPremise : MClause) (mainPremiseNum : Nat) : RuleM (Array ClauseStream) := do
  let potentialPartners ← sidePremiseIdx.getUnificationPartners e
  let mut streams := #[]
  for (sideClauseNum, sideClause, sidePos) in potentialPartners do
    let newStreams ← withoutModifyingLoadedClauses $ do
      let c ← loadClause sideClause
      let sideLit := c.lits[sidePos.lit]!.makeLhs sidePos.side
      -- TODO: I think that if I index positions correctly, this comparison check should be unnecessary
      if (← RuleM.compare sideLit.lhs sideLit.rhs true) != Comparison.LessThan then
        fluidSupWithPartner mainPremise mainPremiseNum e pos c sideClauseNum sidePos.lit sidePos.side given (givenIsMain := true)
      else
        return #[]
    streams := streams.append newStreams
  return streams

def fluidSup (mainPremiseIdx : RootCFPTrie) (sidePremiseIdx : RootCFPTrie) (given : Clause) (givenClause : MClause)
  (givenClauseNum : Nat) : RuleM (Array ClauseStream) := do
  let mut streams := #[]
  -- With given clause as side premise:
  for i in [:givenClause.lits.size] do
    if givenClause.lits[i]!.sign = true && litSelectedOrNothingSelected givenClause i then
      for side in #[LitSide.lhs, LitSide.rhs] do
        let flippedLit := givenClause.lits[i]!.makeLhs side
        if (← RuleM.compare flippedLit.lhs flippedLit.rhs true) == Comparison.LessThan then
          continue
        let cs ← fluidSupWithGivenAsSide given mainPremiseIdx givenClause givenClauseNum i side
        streams := streams.append cs
  -- With given clause as main premise
  let cs ← givenClause.foldGreenM fun acc e pos => do
      let givenClauseLit := givenClause.lits[pos.lit]!.makeLhs pos.side
      if (not (isFluidOrDeep givenClause e)) || (← RuleM.compare givenClauseLit.lhs givenClauseLit.rhs true) == Comparison.LessThan then
        return acc
      else
        let cs ← fluidSupWithGivenAsMain given e pos sidePremiseIdx givenClause givenClauseNum
        return acc.append cs
    #[]
  return streams.append cs