import Lean
import LeanHammer.Saturate
import LeanHammer.Unif



open Lean
open Lean.Meta
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
  | Result.contradiction => printProof state
  | Result.saturated => throwError "Prover saturated."
  | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic