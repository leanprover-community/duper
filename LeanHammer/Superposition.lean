import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

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

def superpositionAtLit (mainPremiseIdx : ProverM.ClauseDiscrTree) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : 
    RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at literal {sidePremiseLit}"
  let potentialPartners ← mainPremiseIdx.getUnify sidePremiseLit.lhs
  trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerTerm) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      superpositionAtLitWithPartner (← loadClause partnerClause) partnerTerm
          sidePremiseLit restOfSidePremise

def superposition (mainPremiseIdx : ProverM.ClauseDiscrTree) (givenClause : Clause) : RuleM Unit := do
  let givenMClause ← loadClause givenClause
  -- With given clause as side premise:
  trace[Rule.debug] "Superposition inferences with {givenClause} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true
    then 
      let restOfGivenClause ← givenMClause.eraseIdx i
      for lit in #[(givenMClause.lits[i]), (givenMClause.lits[i]).symm] do
        let cs ← superpositionAtLit mainPremiseIdx lit restOfGivenClause
  -- TODO: with given clause as main premise
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
  let cs ← runInferenceRule (superposition mainPremiseIdx givenClause)
  for (c, proof) in cs do
    addNewToPassive c proof