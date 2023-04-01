import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta
open Core

initialize registerTraceClass `Rule.betaEtaReduce

def mkBetaEtaReduceProof (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let appliedPremise := appliedPremises[0]!
    Meta.mkLambdaFVars xs appliedPremise

/-- This is the same as Core.betaReduce except that we set useZeta to true since we intend to zetaReduce as well -/
def betaReduce (e : Expr) : CoreM Expr :=
  transform e (pre := fun e => return if e.isHeadBetaTarget (useZeta := true) then .visit e.headBeta else .continue)

partial def reduceToFixedPoint (e : Expr) : RuleM Expr := do
  let e' ← betaReduce e
  let e' ← Meta.zetaReduce e'
  match e'.etaExpanded? with
  | some e' =>
    if e' == e then return e
    else reduceToFixedPoint e'
  | none =>
    if e' == e then return e
    else reduceToFixedPoint e'

/-- Exhaustively apply β and η reduction to every subterm in the clause -/
def betaEtaReduce : MSimpRule := fun c => do
  let c ← loadClause c
  let reducedC ← c.mapM reduceToFixedPoint
  if reducedC == c then
    return none
  else
    let yc ← yieldClause reducedC "betaEtaReduce" $ some mkBetaEtaReduceProof
    return some #[yc]