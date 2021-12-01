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

def superpositionAtLit (idx : ProverM.ClauseDiscrTree) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : 
    RuleM (Array MClause) := do
  let potentialPartners ← idx.getUnify sidePremiseLit.lhs
  let res ← potentialPartners.foldrM
    fun (partnerClause, partnerTerm) res => do
      withoutModifyingMCtx $ do
        match ← superpositionAtLitWithPartner (← MClause.fromClause partnerClause) partnerTerm
          sidePremiseLit restOfSidePremise with
        | some c => res.push c
        | none => res
    #[]
  return res

def superposition (idx : ProverM.ClauseDiscrTree) (givenClause : Clause) : RuleM (Array Clause) := do
  let (mvars, givenMClause) ← MClause.fromClauseCore givenClause
  let mut clauses := #[]
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true
    then 
      let restOfGivenClause ← givenMClause.eraseIdx i
      for lit in #[(givenMClause.lits[i]), (givenMClause.lits[i]).symm] do
        let cs ← superpositionAtLit idx lit restOfGivenClause
        clauses := clauses.append (← cs.mapM MClause.toClause)
  return clauses
      
open ProverM

def performEqualityResolution (givenClause : Clause) : ProverM Unit := do
  performUnaryInference equalityResolution givenClause

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  let idx ← getSupSidePremiseIdx
  let cs ← runRuleM (superposition idx givenClause)
  for c in cs do
    addToPassive c
  ()