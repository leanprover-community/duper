import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

namespace Schroedinger
open RuleM
open Lean

def equalityResolutionAtLit (c : MClause) (i : Nat) : RuleM Unit :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]
    if ← unify #[(lit.lhs, lit.rhs)]
    then
      let c := c.eraseLit i
      yieldClause c "equality resolution"

def equalityResolution (c : Clause) : RuleM Unit := do
  let c ← loadClause c
  for i in [:c.lits.size] do
    if c.lits[i].sign = false then
      equalityResolutionAtLit c i

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : RuleM Unit := do
  withoutModifyingMCtx $ do
    if ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)]
    then do
      let mainPremiseReplaced ← 
        mainPremise.mapM fun e => do
          replace (← instantiateMVars e) 
            (← instantiateMVars sidePremiseLit.lhs) (← instantiateMVars sidePremiseLit.rhs)
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
      superpositionAtLitWithPartner mainPremise e
          c.lits[partnerPos.lit]
          (c.eraseIdx partnerPos.lit)

def superposition 
    (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (givenClause : Clause) : RuleM Unit := do
  let givenMClause ← loadClause givenClause
  -- With given clause as side premise:
  trace[Rule.debug] "Superposition inferences with {givenClause} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true
    then 
      let restOfGivenClause ← givenMClause.eraseIdx i
      for lit in #[(givenMClause.lits[i]), (givenMClause.lits[i]).symm] do
        let cs ← superpositionAtLit mainPremiseIdx lit restOfGivenClause
  -- With given clause as main premise
  trace[Rule.debug] "Superposition inferences with {givenClause} as main premise"
  givenMClause.foldGreenM fun acc e pos => do
      superpositionAtExpr e sidePremiseIdx givenMClause
      ()
    ()
  -- TODO: What about inference with itself?
      
open ProverM

def performEqualityResolution (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "EqRes inferences with {givenClause}"
  let cs ← runInferenceRule $ equalityResolution givenClause
  for (c, proof) in cs do
    addNewToPassive c proof

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause}"
  let mainPremiseIdx ← getSupMainPremiseIdx
  let sidePremiseIdx ← getSupSidePremiseIdx
  let cs ← runInferenceRule (superposition mainPremiseIdx sidePremiseIdx givenClause)
  for (c, proof) in cs do
    addNewToPassive c proof

end Schroedinger