import Duper.Simp
import Duper.Util.ProofReconstruction
import Duper.Util.Reduction

set_option linter.unusedVariables false

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta
open Core

initialize registerTraceClass `duper.rule.betaEtaReduce

def mkBetaEtaReductionProof (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let appliedPremise := appliedPremises[0]!
    Meta.mkLambdaFVars xs appliedPremise

/-- Exhaustively apply beta, eta, and zeta reduction to every subterm in the clause -/
def betaEtaReduction : MSimpRule := fun c => do
  let c ← loadClause c
  let reducedC ← c.mapM (fun e => betaEtaReduce e)
  if reducedC == c then
    return none
  else
    let yc ← yieldClause reducedC "betaEtaReduce" $ some mkBetaEtaReductionProof
    return some #[yc]
