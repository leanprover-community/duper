import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction
import Duper.Util.Misc

namespace Duper
open Lean
open RuleM
open SimpResult

initialize Lean.registerTraceClass `Rule.processEmptyClause

def mkProcessEmptyClauseProof (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let (_, appliedPremises, _) ← instantiatePremises parents premises xs transferExprs
    let appliedPremise := appliedPremises[0]!
    Meta.mkLambdaFVars xs appliedPremise

/-- If c is the empty clause, attempt to provide witnesses for as many of its bVarTypes as possible -/
def processEmptyClause : MSimpRule := fun c => do
  if c.lits.size != 0 then return none
  let c ← loadClause c
  let mut numMVarsInstantiated := 0
  try
    for m in c.mvars do
      let ty ← inferType m
      let _ ← runMetaAsRuleM $ Meta.findInstance ty
      numMVarsInstantiated := numMVarsInstantiated + 1
    let yc ← yieldClause (MClause.mk #[] #[]) "process empty clause" (some mkProcessEmptyClauseProof)
    return some #[yc] 
  catch _ =>
    return none -- TODO: Process the first numMVarsInstantiated clauses