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

def mkPositiveSimplifyReflectProof (mainPremisePos : ClausePos) (isForward : Bool) (premises : List Expr) (parents : List ProofParent)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs

    let mainParentLits := if isForward then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if isForward then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if isForward then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if isForward then appliedPremises[0]! else appliedPremises[1]!

    let eqLit := sideParentLits[0]! 

    let proof ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
      let mut caseProofs : Array Expr := Array.mkEmpty mainParentLits.size
      for i in [:mainParentLits.size] do
        let lit := mainParentLits[i]!
        let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if(i == mainPremisePos.lit) then
            if (mainPremisePos.side == LitSide.lhs) then -- lhs of side premise is matched onto lhs of main premise, so no Eq.symm needed
              Meta.mkLambdaFVars #[h] $ mkApp2 (mkConst ``False.elim [levelZero]) body $ mkApp h appliedSidePremise
            else -- lhs of side premise is matched onto rhs of main premise, so we do need an Eq.symm
              Meta.mkLambdaFVars #[h] $ mkApp2 (mkConst ``False.elim [levelZero]) body $ mkApp h $ ← Meta.mkAppM ``Eq.symm #[appliedSidePremise]
          else if (i < mainPremisePos.lit) then
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
          else -- i > mainPremisePos.lit, so we have to adjust for the off-by-one error by giving orIntro `i - 1` rather than `i`
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) (i - 1) h
        caseProofs := caseProofs.push $ pr
      let r ← orCases (mainParentLits.map Lit.toExpr) caseProofs
      Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
    let proof ← Meta.mkLambdaFVars xs $ mkApp proof appliedSidePremise
    return proof

/-- Checks that (getAtPos mainPremise[pos.lit].lhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseLhs and that 
    (getAtPos mainPremise[pos.lit].rhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseRhs. Importantly, this function
    does NOT check mainPremise[pos.lit].sign or that mainPremise[pos.lit].lhs and mainPremise[pos.lit].rhs agree outside of the given pos. -/
def forwardPositiveSimplifyReflectWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId)
  (mainPremisePos : ClausePos) (sidePremise : MClause) (cToLoad : Clause × Array MVarId): RuleM Bool := do
  let sidePremiseLit := sidePremise.lits[0]!
  let mainPremiseLit := mainPremise.lits[mainPremisePos.lit]!.makeLhs mainPremisePos.side
  let matchSuccess ← -- Try to match lhs of sidePremise to mainPremisePos.side of mainPremise and rhs of sidePremise to other side of main premise
    RuleM.performMatch #[(mainPremiseLit.lhs.getAtPos! mainPremisePos.pos, sidePremiseLit.lhs),
                         (mainPremiseLit.rhs.getAtPos! mainPremisePos.pos, sidePremiseLit.rhs)] mainPremiseMVarIds
  if matchSuccess then
    let mut mainPremiseLitsExceptSimplifiedLit : List Lit := []
    for i in [:mainPremise.lits.size] do
      if i = mainPremisePos.lit then continue
      else mainPremiseLitsExceptSimplifiedLit := mainPremise.lits[i]! :: mainPremiseLitsExceptSimplifiedLit
    -- forwardPositiveSimplifyReflectWithPartner succeeded so we need to add cToLoad to loadedClauses in the state
    setLoadedClauses (cToLoad :: (← getLoadedClauses))
    let res := MClause.mk mainPremiseLitsExceptSimplifiedLit.toArray
    yieldClause res
      "forward positive simplify reflect"
      (some $ mkPositiveSimplifyReflectProof mainPremisePos true)
    trace[Rule.simplifyReflect] "(forward positive): Main clause: {mainPremise.lits}, side clause: {sidePremise.lits}, res: {res.lits}"
    return true 
  else return false

def forwardPositiveSimplifyReflectAtExpr (mainPremise : MClause) (pos : ClausePos)
  (potentialSideClauses : Array Clause) (mainMVarIds : Array MVarId) :
  RuleM Bool := do
  for potentialSideClause in potentialSideClauses do
    let (sideMClause, cToLoad) ← prepLoadClause potentialSideClause
    match ← forwardPositiveSimplifyReflectWithPartner mainPremise mainMVarIds pos sideMClause cToLoad with
    | false => continue
    | true =>
      return true
  return false

/-- Performs positive simplifyReflect with the given clause c as the main clause -/
def forwardPositiveSimplifyReflect (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc _ pos => do
    match acc with
    | false =>
      -- To find potential side clauses for the current literal, we search for clauses that subsume curLitButPositive
      let curLitButPositive := {c.lits[pos.lit]! with sign := true}
      let potentialSideClauses ← subsumptionTrie.getPotentialSubsumingClauses ⟨#[], #[curLitButPositive]⟩
      /-
        The lit c[pos.lit] can be expressed as u[p ← σ(s)] ≠ u[p ← σ(t)] if and only if the following holds:
        1. c[pos.lit].sign is false
        2. c[pos.lit].lhs and c[pos.lit].rhs are identical everywhere except at p
        3. s (the lhs of the side clause) can be matched onto position p of c[pos.lit].lhs
        4. t (the rhs of the side clause) can be matched onto position p of c[pos.lit].rhs
        Conditions 1 and 2 are checked here, conditions 3 and 4 are checked in forwardPositiveSimplifyReflectAtExpr.
      -/
      let sidesAgree := Expr.expressionsAgreeExceptAtPos c.lits[pos.lit]!.lhs c.lits[pos.lit]!.rhs pos.pos
      if(!c.lits[pos.lit]!.sign && sidesAgree) then
        forwardPositiveSimplifyReflectAtExpr c pos potentialSideClauses cMVarIds
      else return false
    | true => return true
  -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
  -- rather than just green ones
  c.foldGreenM fold_fn false

/-- Performs negative simplifyReflect with the given clause c as the main clause -/
-- Note: Although it might be somewhat counterintuitive, I think it should be possible to use subsumptionTrie rather
-- than a fingerprint trie. My idea is, if we are considering the lit e1 = e2 in clause c, we can search for all clauses
-- in subsumptionTrie that are subsumed by the full clause "e1 ≠ e2".
def forwardNegativeSimplifyReflect (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  sorry

open BackwardSimpResult

/-- Performs positive simplifyReflect with the given clause as the side clause -/
def backwardPositiveSimplifyReflect (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSideClause => do
  -- Return Unapplicable if givenSideClause is anything other than a clause with exactly one positive literal
  if (givenSideClause.lits.size != 1 || !givenSideClause.lits[0]!.sign) then return Unapplicable
  -- To find potential main clauses for the given side clause, we search for clauses that would be subsumed by sideClauseButNegative
  let sideClauseButNegative := ⟨#[], #[{givenSideClause.lits[0]! with sign := false}]⟩
  let potentialMainClauses ← subsumptionTrie.getPotentialSubsumedClauses sideClauseButNegative
  let givenSideClause ← loadClause givenSideClause
  for mainClause in potentialMainClauses do
    let (mainClause, (originalMainClause, mclauseMVarIds)) ← prepLoadClause mainClause
    let cToLoad := (originalMainClause, mclauseMVarIds)
    let fold_fn := fun acc _ pos => do
      match acc with
      | BackwardSimpResult.Unapplicable =>
        /-
          The lit mainClause[pos.lit] can be expressed as u[p ← σ(s)] ≠ u[p ← σ(t)] if and only if the following holds:
          1. mainClause[pos.lit].sign is false
          2. mainClause[pos.lit].lhs and mainClause[pos.lit].rhs are identical everywhere except at p
          3. s (the lhs of the side clause) can be matched onto position p of mainClause[pos.lit].lhs
          4. t (the rhs of the side clause) can be matched onto position p of mainClause[pos.lit].rhs
        -/
        let sidesAgree := Expr.expressionsAgreeExceptAtPos mainClause.lits[pos.lit]!.lhs mainClause.lits[pos.lit]!.rhs pos.pos
        if(!mainClause.lits[pos.lit]!.sign && sidesAgree) then
          let sideClauseLit := givenSideClause.lits[0]!
          let mainClauseLit := mainClause.lits[pos.lit]!.makeLhs pos.side
          let matchSuccess ← -- Try to match lhs of sidePremise to pos.side of mclause and rhs of sidePremise to other side of mclause
            RuleM.performMatch #[(mainClauseLit.lhs.getAtPos! pos.pos, sideClauseLit.lhs),
                                (mainClauseLit.rhs.getAtPos! pos.pos, sideClauseLit.rhs)] mclauseMVarIds
          if matchSuccess then
            let mut mainClauseLitsExceptSimplifiedLit : List Lit := []
            for i in [:mainClause.lits.size] do
              if i = pos.lit then continue
              else mainClauseLitsExceptSimplifiedLit := mainClause.lits[i]! :: mainClauseLitsExceptSimplifiedLit
            return Applied [(mainClause, (MClause.mk mainClauseLitsExceptSimplifiedLit.toArray, some $ mkPositiveSimplifyReflectProof pos false))]
          else return Unapplicable
        else return Unapplicable
      | BackwardSimpResult.Applied _ => return acc
      | BackwardSimpResult.Removed _ => throwError "Invalid simplify reflect result"
    match ← mainClause.foldGreenM fold_fn BackwardSimpResult.Unapplicable with
    | BackwardSimpResult.Unapplicable => continue
    | BackwardSimpResult.Applied transformedClauses =>
      -- backwardPositiveSimplifyReflect succeeded so we need to add cToLoad to loadedClauses in the state
      setLoadedClauses (cToLoad :: (← getLoadedClauses))
      trace[Rule.simplifyReflect] "Backward positive simplify reflect with givenSideClause: {givenSideClause.lits} and main clause: {mainClause.lits}"
      trace[Rule.simplifyReflect] "transformedClauses.1: {(transformedClauses.get! 0).1.lits}"
      trace[Rule.simplifyReflect] "transformedClauses.2: {(transformedClauses.get! 0).2.1.lits}"
      return BackwardSimpResult.Applied transformedClauses
    | BackwardSimpResult.Removed _ => throwError "Invalid simplify reflect result"
  return Unapplicable