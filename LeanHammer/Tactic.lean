import Lean
import LeanHammer.Saturate
import LeanHammer.Unif

open Lean
open Lean.Meta
open Schroedinger
open ProverM


namespace Lean.Elab.Tactic

syntax (name := prover) "prover" : tactic


partial def printProof (state : ProverM.State) : TacticM Unit := do
  let rec go c : TacticM Unit := do
    let info ← getClauseInfo! c
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! pp.clause) 
    let parentIds ← parentInfo.map fun info => info.number
    trace[Prover.debug] "Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {c}"
    for proofParent in info.proof.parents do
      go proofParent.clause
  go Clause.empty
where 
  getClauseInfo! (c : Clause) : TacticM ClauseInfo := do
    let some ci ← state.allClauses.find? c
      | throwError "clause info not found: {c}"
    ci

partial def applyProof (state : ProverM.State) : TacticM (List MVarId) := do
  let rec go c : TacticM (Expr × List MVarId) := do
    let info ← getClauseInfo! c
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! pp.clause) 
    let parentIds ← parentInfo.map fun info => info.number
    let target ← info.proof.parents.foldrM
      (fun proofParent target => mkArrow proofParent.clause.toForallExpr target)
      c.toForallExpr
    let mvar ← mkFreshExprMVar target (userName := s!"Clause #{info.number} (by {info.proof.ruleName} {parentIds})")
    let mut goals := [mvar.mvarId!]
    let mut proof := mvar
    for proofParent in info.proof.parents do
      let parentMVar ← mkFreshExprMVar proofParent.clause.toForallExpr
      let (parentProof, newGoals) ← go proofParent.clause
      goals := goals ++ newGoals
      trace[Prover.debug] "mkApp {proof} {parentProof}"
      proof := mkApp proof parentProof
    return (proof, goals)
  let (proof, goals) ← go Clause.empty
  assignExprMVar (← getMainGoal) proof
  return goals
where 
  getClauseInfo! (c : Clause) : TacticM ClauseInfo := do
    let some ci ← state.allClauses.find? c
      | throwError "clause info not found: {c}"
    ci

def collectAssumptions : TacticM (Array Expr) := do
  let mut formulas := #[]
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← getLocalDecl fVarId
    unless ldecl.binderInfo.isAuxDecl ∨ not (← inferType ldecl.type).isProp do
      formulas := formulas.push ldecl.type
  return formulas

@[tactic prover]
partial def evalProver : Tactic
| `(tactic| prover) => do
  let formulas ← collectAssumptions
  trace[Meta.debug] "{formulas}"
  let (_, state) ← ProverM.runWithExprs ProverM.saturate formulas
  match state.result with
  | Result.contradiction => do
      printProof state
      setGoals $ ← applyProof state
  | Result.saturated => 
    trace[Prover.debug] "Final Active Set: {state.activeSet.toArray}"
    -- trace[Prover.debug] "supMainPremiseIdx: {state.supMainPremiseIdx}"
    throwError "Prover saturated."
  | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic

