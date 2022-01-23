import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

namespace Schroedinger
open RuleM
open Lean

-- TODO: Pass in the clauses later?
def mkEqualityResolutionProof (c : Clause) (i : Nat) (premises : Array Expr) (parents: Array ProofParent) : MetaM Expr := do
  let premise := premises[0]
  let parent := parents[0]
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let vanishingVarSkolems ← parent.vanishingVarTypes.mapM (fun ty => Lean.Meta.mkSorry ty (synthetic := true))
    let parentInstantiations := parent.instantiations.map (fun ins => ins.instantiate (xs ++ vanishingVarSkolems))
    let parentLits := parent.clause.lits.map (fun lit => lit.map (fun e => e.instantiateRev parentInstantiations))
    let mut ors := #[parentLits[parentLits.size - 1].toExpr]
    for l in [2:parentLits.size+1] do
      ors := ors.push (mkApp2 (mkConst ``Or) parentLits[parentLits.size - l].toExpr ors[ors.size-1])
    trace[Meta.debug] "Parent lits: {parentLits}"
    trace[Meta.debug] "Parent toExpr: {parent.clause.toExpr}"
    trace[Meta.debug] "instantiations: {parent.instantiations}"
    trace[Meta.debug] "instantiations: {parentInstantiations}"
    trace[Meta.debug] "Premise type: {← Meta.inferType premise}"
    trace[Meta.debug] "apppremise: {← Meta.inferType (mkAppN premise parentInstantiations)}"
      


    let mut r ← Lean.Meta.mkSorry (← Meta.mkArrow parentLits[parentLits.size - 1].toExpr body) (synthetic := true)
    for k in [2:parentLits.size+1] do
      let newOne ← Lean.Meta.mkSorry (← Meta.mkArrow parentLits[parentLits.size - k].toExpr body) (synthetic := true)
      r ← Meta.withLocalDeclD `h ors[k-1] fun h => do
        let p := mkApp6
          (mkConst ``Or.elim)
          parentLits[parentLits.size - k].toExpr
          ors[k-2]
          body
          h
          newOne
          r
        Meta.mkLambdaFVars #[h] p
      

    trace[Meta.debug] "r: {r}"
    trace[Meta.debug] "Type1: {← Meta.inferType r}"
    let appliedPremise := mkAppN premise parentInstantiations
    trace[Meta.debug] "Type2: {← Meta.inferType appliedPremise}"
    trace[Meta.debug] "{← Meta.inferType $ mkApp r appliedPremise}"
    Meta.check (mkApp r appliedPremise)
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def equalityResolutionAtLit (c : MClause) (i : Nat) : RuleM Unit :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]
    if ← unify #[(lit.lhs, lit.rhs)]
    then
      let c := c.eraseLit i
      yieldClause c "equality resolution" 
        (mkProof := mkEqualityResolutionProof (← neutralizeMClause c) i)

def equalityResolution (c : MClause) : RuleM Unit := do
  for i in [:c.lits.size] do
    if c.lits[i].sign = false then
      equalityResolutionAtLit c i

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : RuleM Unit := do
  Core.checkMaxHeartbeats "superposition"
  withoutModifyingMCtx $ do
    if mainPremiseSubterm.isMVar then
      return ()
    if not $ ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)] then
      return ()
    let lhs ← instantiateMVars sidePremiseLit.lhs
    let rhs ← instantiateMVars sidePremiseLit.rhs
    if (← compare lhs rhs) == Comparison.LessThan then
      return ()
    let mainPremiseReplaced ← 
      mainPremise.mapM fun e => do
        replace (← instantiateMVars e) lhs rhs
    let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
    yieldClause (MClause.append mainPremiseReplaced restOfSidePremise) "superposition"

def superpositionAtLit (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : 
    RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at literal {sidePremiseLit}"
  let potentialPartners ← mainPremiseIdx.getUnify sidePremiseLit.lhs
  -- trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      superpositionAtLitWithPartner c (c.getAtPos! partnerPos)
          sidePremiseLit restOfSidePremise

def superpositionAtExpr (e : Expr) (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos)
    (mainPremise : MClause) : RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at expression {e}"
  let potentialPartners ← sidePremiseIdx.getUnify e
  -- trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      let lit := match partnerPos.side with
      | LitSide.lhs => c.lits[partnerPos.lit]
      | LitSide.rhs => c.lits[partnerPos.lit].symm
      superpositionAtLitWithPartner mainPremise e
          lit
          (c.eraseIdx partnerPos.lit)

def superposition 
    (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (givenMClause : MClause) : RuleM Unit := do
  -- With given clause as side premise:
  -- trace[Rule.debug] "Superposition inferences with {givenClause} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true
    then 
      let restOfGivenClause ← givenMClause.eraseIdx i
      for lit in #[(givenMClause.lits[i]), (givenMClause.lits[i]).symm] do
        if (← RuleM.compare lit.lhs lit.rhs) == Comparison.LessThan then
          continue
        let cs ← superpositionAtLit mainPremiseIdx lit restOfGivenClause
  -- With given clause as main premise
  -- trace[Rule.debug] "Superposition inferences with {givenClause} as main premise"
  givenMClause.foldGreenM fun acc e pos => do
      superpositionAtExpr e sidePremiseIdx givenMClause
      ()
    ()
  -- TODO: What about inference with itself?
      
open ProverM

def performEqualityResolution (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "EqRes inferences with {givenClause}"
  performInference equalityResolution givenClause

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause}"
  let mainPremiseIdx ← getSupMainPremiseIdx
  let sidePremiseIdx ← getSupSidePremiseIdx
  performInference (superposition mainPremiseIdx sidePremiseIdx) givenClause


end Schroedinger