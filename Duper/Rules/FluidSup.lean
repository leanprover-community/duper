import Duper.RuleM
import Duper.Selection
import Duper.Util.Misc
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean
open Meta

initialize registerTraceClass `Rule.fluidSup

def fluidSupWithGivenAsSide (given : Clause) (mainPremiseIdx : RootCFPTrie) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) : RuleM (Array ClauseStream) := do
  sorry

def fluidSupWithGivenAsMain (given : Clause) (e : Expr) (pos : ClausePos) (sidePremiseIdx : RootCFPTrie)
  (mainPremise : MClause) (mainPremiseNum : Nat) : RuleM (Array ClauseStream) := do
  sorry

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