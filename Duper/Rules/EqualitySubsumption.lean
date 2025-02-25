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
initialize Lean.registerTraceClass `duper.rule.equalitySubsumption

/-- Checks that (getAtPos mainPremise[pos.lit].lhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseLhs and that
    (getAtPos mainPremise[pos.lit].rhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseRhs. Importantly, this function
    does NOT check mainPremise[pos.lit].sign or that mainPremise[pos.lit].lhs and mainPremise[pos.lit].rhs agree outside of the given pos. -/
def equalitySubsumptionWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId)
  (mainPremisePos : ClausePos) (sidePremise : MClause) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  withoutModifyingMCtx do
    -- Try to match sidePremise side to mainPremiseSubterm. If it succeeds, check if other side of side premise
    -- can match with main premise lit's other side at the same ExprPos
    let sidePremiseLit := sidePremise.lits[0]!
    let mainPremiseLit := mainPremise.lits[mainPremisePos.lit]!.makeLhs mainPremisePos.side
    if (← performMatch #[((← mainPremiseLit.lhs.getAtPos! mainPremisePos.pos), sidePremiseLit.lhs)] mainPremiseMVarIds) then
      if (← performMatch #[((← mainPremiseLit.rhs.getAtPos! mainPremisePos.pos), sidePremiseLit.rhs)] mainPremiseMVarIds) then
        return Removed
      else return Unapplicable
    else return Unapplicable

def forwardEqualitySubsumptionAtExpr (mainPremise : MClause) (pos : ClausePos)
  (potentialSubsumingClauses : Array Clause) (mainMVarIds : Array MVarId) :
  RuleM Bool := withoutModifyingMCtx do
    for potentialSubsumingClause in potentialSubsumingClauses do
      let (sideMClause, cToLoad) ← prepLoadClause potentialSubsumingClause
      match ← equalitySubsumptionWithPartner mainPremise mainMVarIds pos sideMClause with
      | Unapplicable => continue
      | Removed =>
        trace[duper.rule.equalitySubsumption] "Main clause: {mainPremise.lits} removed by side clause {potentialSubsumingClause.lits}"
        return true
      | Applied _ => throwError "Invalid equality subsumption result"
    return false

/-- Returns Removed if there exists a clause that subsumes c, and returns Unapplicable otherwise -/
def forwardEqualitySubsumption (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let potentialSubsumingClauses ← subsumptionTrie.getPotentialSubsumingClauses c
  let potentialSubsumingClauses := -- Only consider side clauses consisting of exactly one positive literal
    potentialSubsumingClauses.filter (fun clause => clause.lits.size = 1 && clause.lits[0]!.sign)

  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc _ pos => do
    match acc with
    | false =>
      /-
        The lit c[pos.lit] can be expressed as u[p ← σ(s)] = u[p ← σ(t)] if and only if the following holds:
        1. c[pos.lit].sign is true
        2. c[pos.lit].lhs and c[pos.lit].rhs are identical everywhere except at p
        3. s (the lhs of the potential subsuming clause) can be matched onto position p of c[pos.lit].lhs
        4. t (the rhs of the potential subsuming clause) can be matched onto position p of c[pos.lit].rhs

        Conditions 1 and 2 are checked here, conditions 3 and 4 are checked in forwardEqualitySubsumptionAtExpr.
      -/
      let sidesAgree ← Expr.expressionsAgreeExceptAtPos c.lits[pos.lit]!.lhs c.lits[pos.lit]!.rhs pos.pos
      if(c.lits[pos.lit]!.sign && sidesAgree) then
        forwardEqualitySubsumptionAtExpr c pos potentialSubsumingClauses cMVarIds
      else return false
    | true => return true -- If forwardEqualitySubsumptionAtExpr ever succeeds, then we need not check further
  -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
  -- rather than just green ones
  let subsumed ← c.foldGreenM fold_fn false
  if subsumed then
    return some #[]
  else
    return none

/-- Returns the list of clauses that givenSubsumingClause subsumes -/
def backwardEqualitySubsumption (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSubsumingClause => do
  -- Return Unapplicable if givenSubsumingClause is anything other than a clause with exactly one positive literal
  if (!givenSubsumingClause.lits[0]!.sign) then return #[]
  if (givenSubsumingClause.lits.size != 1) then return #[]

  let potentialSubsumedClauses ← subsumptionTrie.getPotentialSubsumedClauses givenSubsumingClause
  let givenSubsumingClause ← loadClause givenSubsumingClause
  let fold_fn := fun acc nextClause =>
    conditionallyModifyingLoadedClauses do
      let (nextClauseMVars, nextClauseM) ← loadClauseCore nextClause
      let nextClauseMVarIds := nextClauseMVars.map Expr.mvarId!
      let inner_fold_fn := fun acc _ pos => do
        match acc with
        | false =>
          let sidesAgree ← Expr.expressionsAgreeExceptAtPos nextClause.lits[pos.lit]!.lhs nextClause.lits[pos.lit]!.rhs pos.pos
          if(nextClause.lits[pos.lit]!.sign && sidesAgree) then
            match ← equalitySubsumptionWithPartner nextClauseM nextClauseMVarIds pos givenSubsumingClause with
            | SimpResult.Removed => return true
            | _ => return false
          else return false
        | true => return true -- If it has been determined that nextClause can be removed, no need to check further
      let nextClauseCanBeRemoved ← nextClauseM.foldGreenM inner_fold_fn false
      if nextClauseCanBeRemoved then
        trace[duper.rule.equalitySubsumption] "Main clause {nextClause.lits} subsumed by {givenSubsumingClause.lits} (backward equality subsumption)"
        return (true, acc.push nextClause)
      else return (false, acc)
  let subsumed ← potentialSubsumedClauses.foldlM fold_fn #[]
  return subsumed.map (fun x => (x, none))
