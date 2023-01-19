import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open Lean.Meta
open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.contextualLiteralCutting

def mkContextualLiteralCuttingProof (negatedLitMainIdx : Nat) (assignment : List (Nat × Bool)) (isForward : Bool) (premises : List Expr)
  (parents : List ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs

    let mainParentLits := if isForward then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if isForward then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if isForward then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if isForward then appliedPremises[0]! else appliedPremises[1]!

    let mut caseProofsSide := Array.mkEmpty sideParentLits.size
    for curSideLitIdx in [:sideParentLits.size] do
      let curSideLit := sideParentLits[curSideLitIdx]!
      let (curSideLitAssignment, curSideLitIsFlipped) := assignment.get! curSideLitIdx
      let curSideLitAssignmentWithOffset :=
        if curSideLitAssignment ≤ negatedLitMainIdx then curSideLitAssignment
        else curSideLitAssignment - 1
      if curSideLitAssignment == negatedLitMainIdx then
        let pr ← Meta.withLocalDeclD `hSide curSideLit.toExpr fun hSide => do
          let mut caseProofsMain : Array Expr := Array.mkEmpty mainParentLits.size
          for curMainLitIdx in [:mainParentLits.size] do
            let curMainLit := mainParentLits[curMainLitIdx]!
            if curMainLitIdx == negatedLitMainIdx then
              let pr ← Meta.withLocalDeclD `hMain curMainLit.toExpr fun hMain => do
                let contraProof ←
                  if curMainLit.sign then
                    if curSideLitIsFlipped then
                      let hMainFlipped ← Meta.mkAppM ``Eq.symm #[hMain]
                      Meta.mkAppM' hSide #[hMainFlipped]
                    else Meta.mkAppM' hSide #[hMain]
                  else
                    if curSideLitIsFlipped then
                      let hSideFlipped ← Meta.mkAppM ``Eq.symm #[hSide]
                      Meta.mkAppM' hMain #[hSideFlipped]
                    else Meta.mkAppM' hMain #[hSide]
                Meta.mkLambdaFVars #[hMain] $ mkApp2 (mkConst ``False.elim [levelZero]) body contraProof
              caseProofsMain := caseProofsMain.push pr
            else
              let pr ← Meta.withLocalDeclD `hMain curMainLit.toExpr fun hMain => do
                let curMainLitIdxWithOffset :=
                  if curMainLitIdx ≤ negatedLitMainIdx then curMainLitIdx
                  else curMainLitIdx - 1
                Meta.mkLambdaFVars #[hMain] $ ← orIntro (cLits.map Lit.toExpr) curMainLitIdxWithOffset hMain
              caseProofsMain := caseProofsMain.push pr
          let r ← orCases (mainParentLits.map Lit.toExpr) caseProofsMain
          Meta.mkLambdaFVars #[hSide] $ mkApp r appliedMainPremise
        caseProofsSide := caseProofsSide.push $ pr
      else
        let pr ← Meta.withLocalDeclD `h curSideLit.toExpr fun h => do
          if curSideLitIsFlipped then -- Need to use Eq.symm or Ne.symm depending on the sign of the current literal
            if curSideLit.sign then Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) curSideLitAssignmentWithOffset (← Meta.mkAppM ``Eq.symm #[h])
            else Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) curSideLitAssignmentWithOffset (← Meta.mkAppM ``Ne.symm #[h])
          else Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) curSideLitAssignmentWithOffset h
        caseProofsSide := caseProofsSide.push pr

    let r ← orCases (sideParentLits.map Lit.toExpr) caseProofsSide
    Meta.mkLambdaFVars xs $ mkApp r appliedSidePremise

/-- Returns an mclause identical to `c` except that the lit indicated by litIndex is negated -/
def negateMClauseLit (c : MClause) (litIndex : Nat) : RuleM MClause := do
  let l := c.lits[litIndex]!
  let lNeg := {l with sign := not l.sign}
  match c.replaceLit? litIndex lNeg with
  | some c => return c
  | none => throwError "Invalid litIndex {litIndex}"

def forwardContextualLiteralCuttingWithPartner (mainClauseWithNegatedLit : MClause) (mainClauseMVarIds : Array MVarId)
  (sideClause : Clause) (negatedLitIdx : Nat) : RuleM Bool :=
  withoutModifyingLoadedClauses do
    let sideClause ← loadClause sideClause
    match ← subsumptionCheck' sideClause mainClauseWithNegatedLit mainClauseMVarIds with
    | some assignment => 
      let mainClauseWithNegatedLitRemoved := mainClauseWithNegatedLit.eraseLit negatedLitIdx
      trace[Rule.contextualLiteralCutting] "Forward CLC: Produced {mainClauseWithNegatedLitRemoved.lits} from {mainClauseWithNegatedLit.lits} and {sideClause.lits}"
      yieldClause mainClauseWithNegatedLitRemoved
        "forward contextual literal cutting" $ some (mkContextualLiteralCuttingProof negatedLitIdx assignment true)
      return true
    | none => return false

/-- Performs contextual literal cutting with c as the main clause -/
def forwardContextualLiteralCutting (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  for negatedLitIdx in [:c.lits.size] do
    let cWithNegatedLit ← negateMClauseLit c negatedLitIdx
    let potentialSideClauses ← subsumptionTrie.getPotentialSubsumingClauses' cWithNegatedLit
    for sideClause in potentialSideClauses do
      if ← forwardContextualLiteralCuttingWithPartner cWithNegatedLit cMVarIds sideClause negatedLitIdx then
        return true
  return false

def backwardContextualLiteralCuttingWithPartner (sideClauseWithNegatedLit : MClause) (mainClause : Clause) (negatedLitIdx : Nat) : RuleM Bool :=
  withoutModifyingLoadedClauses do
    withoutModifyingMCtx do
      let (mainClauseMVars, mainClause) ← loadClauseCore mainClause
      let mainClauseMVarIds := mainClauseMVars.map Expr.mvarId!
      match ← subsumptionCheck' sideClauseWithNegatedLit mainClause mainClauseMVarIds with
      | some assignment =>
        let negatedLitMainIdx := assignment[negatedLitIdx]!.1
        let mainClauseWithNegatedLitRemoved := mainClause.eraseLit negatedLitMainIdx
        trace[Rule.contextualLiteralCutting] "Backward CLC: Produced {mainClauseWithNegatedLitRemoved.lits} from {mainClause.lits} and {sideClauseWithNegatedLit.lits}"
        yieldClause mainClauseWithNegatedLitRemoved
          "backward contextual literal cutting" $ some (mkContextualLiteralCuttingProof negatedLitMainIdx assignment false)
        return true
      | none => return false

/-- Performs contextual literal cutting with the given clause as the side clause -/
def backwardContextualLiteralCutting (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSideClause => do
  let givenSideClause ← loadClause givenSideClause
  let mut clausesToRemove := []
  for negatedLitIdx in [:givenSideClause.lits.size] do
    let givenSideClauseWithNegatedLit ← negateMClauseLit givenSideClause negatedLitIdx
    let potentialMainClauses ← subsumptionTrie.getPotentialSubsumedClauses' givenSideClauseWithNegatedLit
    for mainClause in potentialMainClauses do
      if ← backwardContextualLiteralCuttingWithPartner givenSideClauseWithNegatedLit mainClause negatedLitIdx then 
        clausesToRemove := mainClause :: clausesToRemove
  return clausesToRemove