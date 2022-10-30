import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open Lean.Meta
open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.equalitySubsumption

/-- Checks that (getAtPos mainPremise[pos.lit].lhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseLhs and that 
    (getAtPos mainPremise[pos.lit].rhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseRhs. Importantly, this function
    does NOT check mainPremise[pos.lit].sign or that mainPremise[pos.lit].lhs and mainPremise[pos.lit].rhs agree outside of the given pos. -/
def equalitySubsumptionWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId)
  (mainPremisePos : ClausePos) (sidePremise : MClause) (sidePremiseLhs : LitSide) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  withoutModifyingMCtx do
    -- Try to match sidePremise side to mainPremiseSubterm. If it succeeds, check if other side of side premise
    -- can match with main premise lit's other side at the same ExprPos
    let sidePremiseLit := sidePremise.lits[0]!.makeLhs sidePremiseLhs
    let mainPremiseLit := mainPremise.lits[mainPremisePos.lit]!.makeLhs mainPremisePos.side
    if (← RuleM.performMatch #[(mainPremiseLit.lhs.getAtPos! mainPremisePos.pos, sidePremiseLit.lhs)] mainPremiseMVarIds) then
      if (← RuleM.performMatch #[(mainPremiseLit.rhs.getAtPos! mainPremisePos.pos, sidePremiseLit.rhs)] mainPremiseMVarIds) then
        return Removed
      else return Unapplicable
    else return Unapplicable

def forwardEqualitySubsumptionAtExpr (mainPremise : MClause) (pos : ClausePos)
  (potentialSubsumingClauses : Array Clause) (mainMVarIds : Array MVarId) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  withoutModifyingMCtx do
    let clausePosLhs : ClausePos := ⟨0, LitSide.lhs, ExprPos.empty⟩
    let clausePosRhs : ClausePos := ⟨0, LitSide.rhs, ExprPos.empty⟩
    let potentialSubsumingClauses := potentialSubsumingClauses.zip #[clausePosLhs, clausePosRhs]
    for (potentialSubsumingClause, subsumingPos) in potentialSubsumingClauses do
      let (sideMClause, cToLoad) ← prepLoadClause potentialSubsumingClause
      match ← equalitySubsumptionWithPartner mainPremise mainMVarIds pos sideMClause subsumingPos.side with
      | Unapplicable => continue
      | Removed =>
        trace[Rule.equalitySubsumption] "Main clause: {mainPremise.lits} removed by side clause {potentialSubsumingClause.lits}"
        return Removed
      | Applied _ => throwError "Invalid equality subsumption result"
    return Unapplicable

/-- Returns true iff e1 and e2 are identical except potentially at position p. Returns false if p is not a valid position
    for either e1 or e2. -/
def sidesAgreeExceptAtPos (e1 : Expr) (e2 : Expr) (p : ExprPos) : Bool :=
  -- e1 and e2 are identical except potentially at p iff e1 is identical with (replaceAtPos e2 pos (getAtPos e1 pos))
  match e1.getAtPos? p with
  | none => false
  | some e1Subterm =>
    match e2.replaceAtPos? p e1Subterm with
    | none => false
    | some e2Replaced => e1 == e2Replaced

/-- Returns Removed if there exists a clause that subsumes c, and returns Unapplicable otherwise -/
def forwardEqualitySubsumption (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let potentialSubsumingClauses ← subsumptionTrie.getPotentialSubsumingClauses c
  let potentialSubsumingClauses := -- Only consider side clauses consisting of exactly one positive literal
    potentialSubsumingClauses.filter (fun clause => clause.lits.size = 1 && clause.lits[0]!.sign)

  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc _ pos => do
    match acc with
    | Unapplicable =>
      /-
        The lit c[pos.lit] can be expressed as u[p ← σ(s)] = u[p ← σ(t)] if and only if the following holds:
        1. c[pos.lit].sign is true
        2. c[pos.lit].lhs and c[pos.lit].rhs are identical everywhere except at p
        3. s can be matched onto position p of c[pos.lit].lhs
        4. t can be matched onto position p of c[pos.lit].rhs

        Conditions 1 and 2 are checked here, conditions 3 and 4 are checked in forwardEqualitySubsumptionAtExpr.
        Additionally, we enforce that pos.side is LitSide.lhs since forwardEqualitySubsumptionAtExpr will check both
        conditions 3 and 4 (so it would be redundant to perform the same call with the only difference being pos.side)
      -/
      let sidesAgree := sidesAgreeExceptAtPos c.lits[pos.lit]!.lhs c.lits[pos.lit]!.rhs pos.pos
      if(pos.side == LitSide.lhs && c.lits[pos.lit]!.sign && sidesAgree) then
        forwardEqualitySubsumptionAtExpr c pos potentialSubsumingClauses cMVarIds
      else return Unapplicable
    | Removed => return Removed -- If forwardEqualitySubsumptionAtExpr ever succeeds, then we need not check further
    | Applied _ => throwError "Invalid equality subsumption result"
  -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
  -- rather than just green ones
  c.foldGreenM fold_fn Unapplicable

open BackwardSimpResult

/-- Returns Removed l where l is a list of clauses that givenSubsumingClause subsumes -/
def backwardEqualitySubsumption (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSubsumingClause => do
  -- Return Unapplicable if givenSubsumingClause is anything other than a clause with exactly one positive literal
  if (givenSubsumingClause.lits.size != 1) then return Unapplicable
  if (!givenSubsumingClause.lits[0]!.sign) then return Unapplicable

  let potentialSubsumedClauses ← subsumptionTrie.getPotentialSubsumedClauses givenSubsumingClause
  let givenSubsumingClause ← loadClause givenSubsumingClause
  let fold_fn := fun acc nextClause =>
    conditionallyModifyingLoadedClauses do
      let (nextClauseMVars, nextClause) ← loadClauseCore nextClause
      let nextClauseMVarIds := nextClauseMVars.map Expr.mvarId!
      let inner_fold_fn := fun acc _ pos => do
        match acc with
        | false =>
          let sidesAgree := sidesAgreeExceptAtPos nextClause.lits[pos.lit]!.lhs nextClause.lits[pos.lit]!.rhs pos.pos
          if(nextClause.lits[pos.lit]!.sign && sidesAgree) then
            -- Note that we can let sidePremiseLhs be LitSide.lhs because we do not require that pos.side == lhs
            match ← equalitySubsumptionWithPartner nextClause nextClauseMVarIds pos givenSubsumingClause LitSide.lhs with
            | SimpResult.Removed => return true
            | _ => return false
          else return false
        | true => return true -- If it has been determined that nextClause can be removed, no need to check further
      let nextClauseCanBeRemoved ← nextClause.foldGreenM inner_fold_fn false
      if nextClauseCanBeRemoved then
        trace[Rule.equalitySubsumption] "Main clause {nextClause.lits} subsumed by {givenSubsumingClause.lits} (backward equality subsumption)"
        return (true, nextClause :: acc)
      else return (false, acc)
  return Removed (← potentialSubsumedClauses.foldlM fold_fn [])