import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open Lean.Meta
open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.simplifyReflect

/-- Checks that (getAtPos mainPremise[pos.lit].lhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseLhs and that 
    (getAtPos mainPremise[pos.lit].rhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseRhs. Importantly, this function
    does NOT check mainPremise[pos.lit].sign or that mainPremise[pos.lit].lhs and mainPremise[pos.lit].rhs agree outside of the given pos. -/
def positiveSimplifyReflectWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId)
  (mainPremisePos : ClausePos) (sidePremise : MClause) (sidePremiseLhs : LitSide) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  withoutModifyingMCtx do
    -- Try to match sidePremise side to mainPremiseSubterm. If it succeeds, check if other side of side premise
    -- can match with main premise lit's other side at the same ExprPos
    let sidePremiseLit := sidePremise.lits[0]!.makeLhs sidePremiseLhs
    let mainPremiseLit := mainPremise.lits[mainPremisePos.lit]!.makeLhs mainPremisePos.side
    if (← RuleM.performMatch #[(mainPremiseLit.lhs.getAtPos! mainPremisePos.pos, sidePremiseLit.lhs)] mainPremiseMVarIds) then
      if (← RuleM.performMatch #[(mainPremiseLit.rhs.getAtPos! mainPremisePos.pos, sidePremiseLit.rhs)] mainPremiseMVarIds) then
        let mut mainPremiseLitsExceptSimplifiedLit : List Lit := []
        for i in [:mainPremise.lits.size] do
          if i = mainPremisePos.lit then continue
          else mainPremiseLitsExceptSimplifiedLit := mainPremise.lits[i]! :: mainPremiseLitsExceptSimplifiedLit
        return Applied [(MClause.mk mainPremiseLitsExceptSimplifiedLit.toArray, none)]
      else return Unapplicable
    else return Unapplicable

def forwardPositiveSimplifyReflectAtExpr (mainPremise : MClause) (pos : ClausePos)
  (potentialSideClauses : Array Clause) (mainMVarIds : Array MVarId) :
  RuleM (SimpResult (List (MClause × Option ProofReconstructor))) := do
  withoutModifyingMCtx do
    let potentialSideClauses := potentialSideClauses.zip #[LitSide.lhs, LitSide.rhs]
    for (potentialSideClause, sideClauseSide) in potentialSideClauses do
      let (sideMClause, cToLoad) ← prepLoadClause potentialSideClause
      match ← positiveSimplifyReflectWithPartner mainPremise mainMVarIds pos sideMClause sideClauseSide with
      | Unapplicable => continue
      | Applied res =>
        -- positiveSimplifyReflectWithPartner succeeded so we need to add cToLoad to loadedClauses in the state
        setLoadedClauses (cToLoad :: (← getLoadedClauses))
        trace[Rule.simplifyReflect] "(forward positive): Main clause: {mainPremise.lits}, side clause: {sideMClause.lits}, res: {res[0]!.1.lits}"
        return Applied res
      | Removed => throwError "Invalid simplify reflect result"
    return Unapplicable

/-- Performs positive simplifyReflect with the given clause c as the main clause -/
def forwardPositiveSimplifyReflect (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc _ pos => do
    match acc with
    | Unapplicable =>
      let curLitButPositive := {c.lits[pos.lit]! with sign := true}
      -- To find potential side clauses for the current literal, we search for clauses that subsume curLitButPositive
      let potentialSideClauses ← subsumptionTrie.getPotentialSubsumingClauses ⟨#[], #[curLitButPositive]⟩
      /-
        The lit c[pos.lit] can be expressed as u[p ← σ(s)] ≠ u[p ← σ(t)] if and only if the following holds:
        1. c[pos.lit].sign is false
        2. c[pos.lit].lhs and c[pos.lit].rhs are identical everywhere except at p
        3. s can be matched onto position p of c[pos.lit].lhs
        4. t can be matched onto position p of c[pos.lit].rhs

        Conditions 1 and 2 are checked here, conditions 3 and 4 are checked in forwardPositiveSimplifyReflectAtExpr.
        Additionally, we enforce that pos.side is LitSide.lhs since forwardPositiveSimplifyReflectAtExpr will check both
        conditions 3 and 4 (so it would be redundant to perform the same call with the only difference being pos.side)
      -/
      let sidesAgree := Expr.expressionsAgreeExceptAtPos c.lits[pos.lit]!.lhs c.lits[pos.lit]!.rhs pos.pos
      if(pos.side == LitSide.lhs && !c.lits[pos.lit]!.sign && sidesAgree) then
        forwardPositiveSimplifyReflectAtExpr c pos potentialSideClauses cMVarIds
      else return Unapplicable
    | Applied res => return Applied res
    | Removed => throwError "Invalid simplify reflect result"
  -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
  -- rather than just green ones
  c.foldGreenM fold_fn Unapplicable

/-- Performs negative simplifyReflect with the given clause c as the main clause -/
-- Note: Although it might be somewhat counterintuitive, I think it should be possible to use subsumptionTrie rather
-- than a fingerprint trie. My idea is, if we are considering the lit e1 = e2 in clause c, we can search for all clauses
-- in subsumptionTrie that are subsumed by the full clause "e1 ≠ e2".
def forwardNegativeSimplifyReflect (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  sorry