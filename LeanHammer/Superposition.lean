import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.Inference
import LeanHammer.MClause

open RuleM
open Lean

def equalityResolutionAtLit (c : MClause) (i : Nat) : RuleM (Option MClause) := do
  let lit := c.lits[i]
  if ← unify #[(lit.lhs, lit.rhs)]
  then
    c |>.eraseLit i
      |>.mapM instantiateMVars
  else return none

def equalityResolution (c : MClause) : RuleM (Array MClause) := do
  let mut res := #[]
  for i in [:c.lits.size] do
    if c.lits[i].sign = false then
      match ← withoutModifyingMCtx $ equalityResolutionAtLit c i with
      | some c => do 
        res := res.push c
      | none => ()
  return res

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : 
    RuleM (Option MClause) := do
  if ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)]
  then do
    let mainPremiseReplaced ← 
      mainPremise.mapM fun e => do
        replace (← instantiateMVars e) 
          (← instantiateMVars sidePremiseLit.lhs) (← instantiateMVars sidePremiseLit.rhs)
    let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
    return MClause.append mainPremiseReplaced restOfSidePremise
  else return none

def superpositionAtLit (mainPremiseIdx : ProverM.ClauseDiscrTree) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : 
    RuleM (Array MClause) := do
  trace[Rule.debug] "Superposition inferences at literal {sidePremiseLit}"
  let potentialPartners ← mainPremiseIdx.getUnify sidePremiseLit.lhs
  trace[Rule.debug] "Potential partners {potentialPartners}"
  let res ← potentialPartners.foldrM
    fun (partnerClause, partnerTerm) res => do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      withoutModifyingMCtx $ do
        match ← superpositionAtLitWithPartner (← MClause.fromClause partnerClause) partnerTerm
          sidePremiseLit restOfSidePremise with
        | some c => res.push c
        | none => res
    #[]
  return res

def superposition (mainPremiseIdx : ProverM.ClauseDiscrTree) (givenClause : Clause) : RuleM (Array Clause) := do
  let (mvars, givenMClause) ← MClause.fromClauseCore givenClause
  let mut clauses := #[]
  -- With given clause as side premise:
  trace[Rule.debug] "Superposition inferences with {givenClause} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true
    then 
      let restOfGivenClause ← givenMClause.eraseIdx i
      for lit in #[(givenMClause.lits[i]), (givenMClause.lits[i]).symm] do
        let cs ← superpositionAtLit mainPremiseIdx lit restOfGivenClause
        clauses := clauses.append (← cs.mapM MClause.toClause)
  -- TODO: with given clause as main premise:
  return clauses
  -- TODO: What about inference with itself?
      
open ProverM

def performEqualityResolution (givenClause : Clause) : ProverM Unit := do
  performUnaryInference equalityResolution givenClause

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause}"
  let mainPremiseIdx ← getSupMainPremiseIdx
  let cs ← runRuleM (superposition mainPremiseIdx givenClause)
  for c in cs do
    addNewToPassive c
  ()