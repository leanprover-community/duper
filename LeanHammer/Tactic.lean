import Lean
import LeanHammer.Saturate
import LeanHammer.Unif



open Lean
open Lean.Meta
open ProverM

namespace Lean.Elab.Tactic

syntax (name := prover) "prover" : tactic

@[tactic prover]
partial def evalProver : Tactic
| `(tactic| prover) => do
  let goal ← Elab.Tactic.getMainGoal
  let mut formulas := #[]
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← getLocalDecl fVarId
    unless ldecl.binderInfo.isAuxDecl ∨ not (← inferType ldecl.type).isProp do
      formulas := formulas.push ldecl.type
  trace[Meta.debug] "{formulas}"
  ProverM.runWithExprs ProverM.saturate formulas
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic