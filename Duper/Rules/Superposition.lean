import Duper.RuleM
import Duper.Selection
import Duper.Util.Misc
import Duper.Util.ProofReconstruction
import Duper.Expr

namespace Duper
open RuleM
open Lean
open Meta

initialize registerTraceClass `Rule.superposition

register_option simultaneousSuperposition : Bool := {
  defValue := true
  descr := "Whether we perform simultaneous superposition"
}

def getSimultaneousSuperposition (opts : Options) : Bool :=
  simultaneousSuperposition.get opts

def mkSuperpositionProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (mainPremisePos : ClausePos)
  (givenIsMain : Bool) (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    
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
              if i == mainPremisePos.lit then
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

def mkSimultaneousSuperpositionProof (sidePremiseLitIdx : Nat) (sidePremiseLitSide : LitSide) (givenIsMain : Bool) (poses : Array ClausePos)
  (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs

    let mainParentLits := if givenIsMain then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if givenIsMain then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if givenIsMain then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if givenIsMain then appliedPremises[0]! else appliedPremises[1]!

    -- processing `poses`
    let mut poseses : Array (Array LitPos) := (Array.mk <| List.range mainParentLits.size).map (fun _ => #[])
    for cpos in poses do
      let lit := cpos.lit
      poseses := poseses.set! lit (poseses[lit]!.push cpos.toLitPos)

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
              let abstr := (← lit.mapMByPos Expr.abstractAtPoses! poseses[i]!).toExpr
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
  (mainPremisePos : ClausePos) (mainPremiseEligibility : Eligibility) (sidePremise : MClause) (sidePremiseNum : Nat)
  (sidePremiseLitIdx : Nat) (sidePremiseSide : LitSide) (sidePremiseEligibility : Eligibility) (given : Clause) (givenIsMain : Bool)
  (simultaneousSuperposition : Bool) : RuleM (Array ClauseStream) := do
  Core.checkMaxHeartbeats "superposition"
  withoutModifyingMCtx $ do
    let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
    let restOfSidePremise := sidePremise.eraseIdx sidePremiseLitIdx

    /-
      To efficiently approximate condition 7 in https://matryoshka-project.github.io/pubs/hosup_report.pdf, if the main
      premise literal is positive and the main premise subterm is directly below the equality, then we require that the
      main premise's clause id is less than or equal to the side premise's clause id (as an arbitrary tiebreaker).
    -/
    if mainPremise.lits[mainPremisePos.lit]!.sign && mainPremisePos.pos == #[] && mainPremiseNum > sidePremiseNum then
      return #[]

    let loaded ← getLoadedClauses
    let ug ← unifierGenerator #[(mainPremiseSubterm, sidePremiseLit.lhs)]
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
  
      let mut mainPremiseReplaced : MClause := Inhabited.default
      let mut poses : Array ClausePos := #[]
      if simultaneousSuperposition then
        let mainPremise ← mainPremise.mapM instantiateMVars
        let sidePremiseLhs ← instantiateMVars sidePremiseLhs
        (mainPremiseReplaced, poses) ← mainPremise.mapMWithPos <|
          Expr.replaceGreenWithPos sidePremiseLhs sidePremiseRhs
      else
        mainPremiseReplaced ← mainPremise.replaceAtPos! mainPremisePos sidePremiseRhs
  
      if mainPremiseReplaced.isTrivial then
        trace[Rule.superposition] "trivial: {mainPremiseReplaced.lits}"
        return none
  
      let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
      let res := MClause.append restOfSidePremise mainPremiseReplaced
      let mkProof :=
        if simultaneousSuperposition then mkSimultaneousSuperpositionProof sidePremiseLitIdx sidePremiseSide givenIsMain poses
        else mkSuperpositionProof sidePremiseLitIdx sidePremiseSide mainPremisePos givenIsMain
      trace[Rule.superposition]
        m!"Superposition successfully yielded {res.lits} from mainPremise: {mainPremise.lits} (lit : {mainPremisePos.lit}) " ++
        m!"and sidePremise: {sidePremise.lits} (lit : {sidePremiseLitIdx})."
      some <$> yieldClause res "superposition" mkProof
    return #[ClauseStream.mk ug given yC "superposition"]

def superpositionWithGivenAsSide (given : Clause) (mainPremiseIdx : RootCFPTrie) (sidePremise : MClause) (sidePremiseNum : Nat) (sidePremiseLitIdx : Nat)
  (sidePremiseSide : LitSide) (sidePremiseEligibility : Eligibility) (simultaneousSuperposition : Bool) : RuleM (Array ClauseStream) := do
  let sidePremiseLit := sidePremise.lits[sidePremiseLitIdx]!.makeLhs sidePremiseSide
  let potentialPartners ← mainPremiseIdx.getUnificationPartners sidePremiseLit.lhs
  let mut streams := #[]
  for (mainClauseNum, mainClause, mainPos, mainClauseEligibilityOpt) in potentialPartners do
    let mainClauseEligibility ←
      match mainClauseEligibilityOpt with
      | some eligibility => pure eligibility
      | none => throwError "Eligibility not correctly stored in supMainPremiseIdx"
    let newStreams ← withoutModifyingLoadedClauses $ do
      let c ← loadClause mainClause
      superpositionAtLitWithPartner c mainClauseNum (← c.getAtPos! mainPos) mainPos mainClauseEligibility sidePremise sidePremiseNum sidePremiseLitIdx sidePremiseSide
        sidePremiseEligibility given (givenIsMain := false) simultaneousSuperposition
    streams := streams.append newStreams
  return streams

def superpositionWithGivenAsMain (given : Clause) (e : Expr) (pos : ClausePos) (sidePremiseIdx : RootCFPTrie)
  (mainPremise : MClause) (mainPremiseNum : Nat) (mainPremiseEligibility : Eligibility) (simultaneousSuperposition : Bool) : RuleM (Array ClauseStream) := do
  let potentialPartners ← sidePremiseIdx.getUnificationPartners e
  let mut streams := #[]
  for (sideClauseNum, sideClause, sidePos, sideClauseEligibilityOpt) in potentialPartners do
    let sideClauseEligibility ←
      match sideClauseEligibilityOpt with
      | some eligibility => pure eligibility
      | none => throwError "Eligibility not correctly stored in supSidePremiseIdx"
    let newStreams ← withoutModifyingLoadedClauses $ do
      let c ← loadClause sideClause
      superpositionAtLitWithPartner mainPremise mainPremiseNum e pos mainPremiseEligibility c sideClauseNum sidePos.lit sidePos.side
        sideClauseEligibility given (givenIsMain := true) simultaneousSuperposition
    streams := streams.append newStreams
  return streams

def superposition (mainPremiseIdx : RootCFPTrie) (sidePremiseIdx : RootCFPTrie) (given : Clause) (givenClause : MClause)
  (givenClauseNum : Nat) : RuleM (Array ClauseStream) := do
  trace[Rule.superposition] "Superposition inferences with {givenClause.lits}"
  let opts ← getOptions
  let simultaneousSuperposition := getSimultaneousSuperposition opts
  let mut streams := #[]
  -- With given clause as side premise:
  for i in [:givenClause.lits.size] do
    let litEligibility ← eligibilityPreUnificationCheck givenClause true i
    if givenClause.lits[i]!.sign = true && (litEligibility == Eligibility.eligible || litEligibility == Eligibility.potentiallyEligible) then
      for side in #[LitSide.lhs, LitSide.rhs] do
        let flippedLit := givenClause.lits[i]!.makeLhs side
        if (← RuleM.compare flippedLit.lhs flippedLit.rhs true) == Comparison.LessThan then
          continue
        let cs ← superpositionWithGivenAsSide given mainPremiseIdx givenClause givenClauseNum i side litEligibility simultaneousSuperposition
        streams := streams.append cs
  -- With given clause as main premise
  let cs ← givenClause.foldGreenM fun acc e pos => do
      let givenClauseLit := givenClause.lits[pos.lit]!.makeLhs pos.side
      let litEligibility ← eligibilityPreUnificationCheck givenClause true pos.lit
      let sideComparison ← RuleM.compare givenClauseLit.lhs givenClauseLit.rhs true
      if e.isMVar' || (Order.isFluid e) || litEligibility == Eligibility.notEligible || sideComparison == Comparison.LessThan then
        return acc
      else
        let cs ← superpositionWithGivenAsMain given e pos sidePremiseIdx givenClause givenClauseNum litEligibility simultaneousSuperposition
        return acc.append cs
    #[]
  return streams.append cs

end Duper
