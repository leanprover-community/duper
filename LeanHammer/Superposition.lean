import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.Inference
import LeanHammer.MClause

open RuleM

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


open ProverM

def performEqualityResolution (givenClause : Clause): ProverM Unit := do
  performUnaryInference equalityResolution givenClause

def performSuperposition (givenClause : Clause): ProverM Unit := do
  let idx ← getSupSidePremiseIdx
  runRuleM do
    let (mvars, givenMClause) ← MClause.fromClauseCore givenClause
    givenMClause.foldM
      fun () e => do
        let potentialPartners ← idx.getUnify e
        -- TODO: Do something
        ()
      ()
  ()