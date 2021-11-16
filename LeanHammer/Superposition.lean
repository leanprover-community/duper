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