import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

open ProverM
open RuleM

def performUnaryInferenceAux (rule : MClause → RuleM (Array MClause)) : 
    Clause → ProverM (Array Clause) := 
  fun givenClause => do
    RuleM.runAsProverM do
      let mclause ← MClause.fromClause givenClause
      let cs ← rule mclause
      let cs ← cs.mapM fun c => c.toClause
      cs

def performUnaryInference (rule : MClause → RuleM (Array MClause)) (c : Clause) : ProverM Unit := do
  let cs ← performUnaryInferenceAux rule c
  for c in cs do
    addToPassive c