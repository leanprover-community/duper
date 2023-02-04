import Duper.RuleM
import Duper.Selection
import Duper.Util.Misc
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean

initialize registerTraceClass `Superposition.debug

def mkSuperpositionProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (mainPremisePos : ClausePos)
  (givenIsMain : Bool) (premises : List Expr) (parents: List ProofParent) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    
    let mainParentLits := if givenIsMain then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if givenIsMain then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if givenIsMain then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if givenIsMain then appliedPremises[0]! else appliedPremises[1]!

    let mut caseProofsSide := Array.mkEmpty sideParentLits.size
    for j in [:sideParentLits.size] do
      if j == sidePremiseLitIdx then
        let eqLit := sideParentLits[j]!
        let pr ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
          let eq :=
            if sidePremiseLitSide == LitSide.rhs then ← Meta.mkAppM ``Eq.symm #[heq]
            else heq
          let mut caseProofsMain : Array Expr := Array.mkEmpty mainParentLits.size
          for i in [:mainParentLits.size] do
            let lit := mainParentLits[i]!
            let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
              let idx := sideParentLits.size - 1 + i
              if(i == mainPremisePos.lit) then
                let litPos : LitPos := {side := mainPremisePos.side, pos := mainPremisePos.pos}
                let abstrLit ← (lit.abstractAtPos! litPos)
                let abstrExp := abstrLit.toExpr
                let abstrLam := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstrExp
                let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstrLam, eq], h]
                Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx $ rwproof
              else
                Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
            caseProofsMain := caseProofsMain.push $ pr
          let r ← orCases (mainParentLits.map Lit.toExpr) caseProofsMain
          Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
        caseProofsSide := caseProofsSide.push $ pr
      else
        let lit := sideParentLits[j]!
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ sidePremiseLitIdx then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofsSide := caseProofsSide.push $ pr

    let r ← orCases (sideParentLits.map Lit.toExpr) caseProofsSide
    let proof ← Meta.mkLambdaFVars xs $ mkApp r appliedSidePremise
    return proof

def mkSimultaneousSuperpositionProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (givenIsMain : Bool)
  (premises : List Expr) (parents: List ProofParent) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs

    let mainParentLits := if givenIsMain then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if givenIsMain then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if givenIsMain then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if givenIsMain then appliedPremises[0]! else appliedPremises[1]!

    let mut caseProofsSide := Array.mkEmpty sideParentLits.size
    for j in [:sideParentLits.size] do
      if j == sidePremiseLitIdx then
        let eqLit := sideParentLits[j]!
        let pr ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
          let eq := if sidePremiseLitSide == LitSide.rhs
                      then ← Meta.mkAppM ``Eq.symm #[heq]
                      else heq
          let mut caseProofsMain : Array Expr := Array.mkEmpty mainParentLits.size
          for i in [:mainParentLits.size] do
            let lit := mainParentLits[i]!
            let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
              let idx := sideParentLits.size - 1 + i
              let abstr ← Lean.Meta.abstractAtExpr lit.toExpr $ eqLit.getSide sidePremiseLitSide
              let abstr := mkLambda `x BinderInfo.default (← Meta.inferType eqLit.lhs) abstr
              let rwproof ← Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[abstr,eq], h]
              Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx $ rwproof
            caseProofsMain := caseProofsMain.push $ pr
          let r ← orCases (mainParentLits.map Lit.toExpr) caseProofsMain
          Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
        caseProofsSide := caseProofsSide.push $ pr
      else
        let lit := sideParentLits[j]!
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ sidePremiseLitIdx then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofsSide := caseProofsSide.push $ pr

    let r ← orCases (sideParentLits.map Lit.toExpr) caseProofsSide
    let proof ← Meta.mkLambdaFVars xs $ mkApp r appliedSidePremise
    return proof

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseNum : Nat) (mainPremiseSubterm : Expr)
  (mainPremisePos : ClausePos) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide)
  (givenIsMain : Bool) (simultaneousSuperposition : Bool) : RuleM Unit := do
  Core.checkMaxHeartbeats "superposition"
  withoutModifyingMCtx $ do
    let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
    let restOfSidePremise := sidePremise.eraseIdx sidePremiseLitIdx
    if mainPremiseSubterm.isMVar then
      return () -- No superposition into variables
    
    /-
      To efficiently approximate condition 7 in https://matryoshka-project.github.io/pubs/hosup_report.pdf, if the main
      premise literal is positive and the main premise subterm is directly below the equality, then we require that the
      main premise's clause id is less than or equal to the side premise's clause id (as an arbitrary tiebreaker).
    -/
    if mainPremise.lits[mainPremisePos.lit]!.sign && mainPremisePos.pos == #[] && mainPremiseNum > sidePremiseNum then
      return ()

    let sidePremiseEligibility ← eligibilityPreUnificationCheck sidePremise sidePremiseLitIdx
    let mainPremiseEligibility ← eligibilityPreUnificationCheck mainPremise mainPremisePos.lit

    if sidePremiseEligibility == Eligibility.notEligible || mainPremiseEligibility == Eligibility.notEligible then
      return () -- Preunification checks determined ineligibility, so we don't need to bother with unificaiton
    if not $ ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)] then
      return () -- Unification failed, so superposition cannot occur
    let sidePremiseFinalEligibility ←
      eligibilityPostUnificationCheck sidePremise sidePremiseLitIdx sidePremiseEligibility (strict := true)
    if not sidePremiseFinalEligibility then return ()
    let mainPremiseFinalEligibility ←
      eligibilityPostUnificationCheck mainPremise mainPremisePos.lit mainPremiseEligibility
        (strict := mainPremise.lits[mainPremisePos.lit]!.sign)
    if not mainPremiseFinalEligibility then return ()

    -- Even though we did preliminary comparison checks before unification, we still need to do comparison checks after unification
    let lhs ← RuleM.instantiateMVars sidePremiseLit.lhs
    let rhs ← RuleM.instantiateMVars sidePremiseLit.rhs
    if (← compare lhs rhs) == Comparison.LessThan then
      return ()

    let mainPremiseLhs := mainPremise.lits[mainPremisePos.lit]!.getSide mainPremisePos.side
    let mainPremiseRhs := mainPremise.lits[mainPremisePos.lit]!.getOtherSide mainPremisePos.side
    if (← compare mainPremiseLhs mainPremiseRhs) == Comparison.LessThan then
      return ()

    -- Checking Sup condition 10 in https://matryoshka-project.github.io/pubs/hosup_report.pdf
    if rhs == mkConst ``False && (!mainPremise.lits[mainPremisePos.lit]!.sign || mainPremisePos.pos != #[]) then
      return ()

    let mainPremiseReplaced ←
      if simultaneousSuperposition then mainPremise.mapM fun e => do replace e lhs rhs --TODO: Replace only green subterms
      else mainPremise.replaceAtPos! mainPremisePos rhs

    if mainPremiseReplaced.isTrivial then
      trace[Prover.debug] "trivial: {mainPremiseReplaced.lits}"
      return ()
      
    let restOfSidePremise ← restOfSidePremise.mapM fun e => RuleM.instantiateMVars e
    let res := MClause.append restOfSidePremise mainPremiseReplaced
    let mkProof :=
      if simultaneousSuperposition then mkSimultaneousSuperpositionProof sidePremiseLitIdx sidePremiseSide givenIsMain
      else mkSuperpositionProof sidePremiseLitIdx sidePremiseSide mainPremisePos givenIsMain
    trace[Superposition.debug]
      m!"Superposition successfully yielded {res.lits} from mainPremise: {mainPremise.lits} (lit : {mainPremisePos.lit}) " ++
      m!"and sidePremise: {sidePremise.lits} (lit : {sidePremiseLitIdx})."
    yieldClause res "superposition" mkProof

def superpositionWithGivenAsSide (mainPremiseIdx : RootCFPTrie) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) (simultaneousSuperposition : Bool) : RuleM Unit := do
  let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
  let potentialPartners ← mainPremiseIdx.getUnificationPartners sidePremiseLit.lhs
  for (mainClauseNum, mainClause, mainPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      let c ← loadClause mainClause
      let mainLit := c.lits[mainPos.lit]!.makeLhs mainPos.side
      if (← RuleM.compare mainLit.lhs mainLit.rhs) != Comparison.LessThan then
        superpositionAtLitWithPartner c mainClauseNum (c.getAtPos! mainPos) mainPos sidePremise sidePremiseNum sidePremiseLitIdx sidePremiseSide
          (givenIsMain := false) simultaneousSuperposition

def superpositionWithGivenAsMain (e : Expr) (pos : ClausePos) (sidePremiseIdx : RootCFPTrie)
  (mainPremise : MClause) (mainPremiseNum : Nat) (simultaneousSuperposition : Bool) : RuleM Unit := do
  let potentialPartners ← sidePremiseIdx.getUnificationPartners e
  for (sideClauseNum, sideClause, sidePos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      let c ← loadClause sideClause
      let sideLit := c.lits[sidePos.lit]!.makeLhs sidePos.side
      if (← RuleM.compare sideLit.lhs sideLit.rhs) != Comparison.LessThan then
        superpositionAtLitWithPartner mainPremise mainPremiseNum e pos c sideClauseNum sidePos.lit sidePos.side
          (givenIsMain := true) simultaneousSuperposition

def superposition (mainPremiseIdx : RootCFPTrie) (sidePremiseIdx : RootCFPTrie) (givenClause : MClause)
  (givenClauseNum : Nat) : RuleM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause.lits}"
  let simultaneousSuperposition := true -- TODO: Make this an option that can be passed into duper
  -- With given clause as side premise:
  for i in [:givenClause.lits.size] do
    if givenClause.lits[i]!.sign = true && litSelectedOrNothingSelected givenClause i
    then
      for side in #[LitSide.lhs, LitSide.rhs] do
        let flippedLit := givenClause.lits[i]!.makeLhs side
        if (← RuleM.compare flippedLit.lhs flippedLit.rhs) == Comparison.LessThan then
          continue
        let cs ← superpositionWithGivenAsSide mainPremiseIdx givenClause givenClauseNum i side simultaneousSuperposition
  -- With given clause as main premise
  givenClause.foldGreenM fun acc e pos =>
    do
      let givenClauseLit := givenClause.lits[pos.lit]!.makeLhs pos.side
      if (← RuleM.compare givenClauseLit.lhs givenClauseLit.rhs) == Comparison.LessThan then
        return ()
      else
        superpositionWithGivenAsMain e pos sidePremiseIdx givenClause givenClauseNum simultaneousSuperposition
    ()

end Duper
