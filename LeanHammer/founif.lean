import Lean
import LeanHammer.Clause
import LeanHammer.Unif



open Lean
open Lean.Meta


namespace Lean.Elab.Tactic

syntax (name := go) "go" : tactic

@[tactic go]
partial def evalGo : Tactic
| `(tactic| go) => do
  let goal ← Elab.Tactic.getMainGoal
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← getLocalDecl fVarId
    unless ldecl.binderInfo.isAuxDecl ∨ not (← inferType ldecl.type).isProp do
      let c ← Clause.ofExpr ldecl.type
      let subst : Option FVarSubst ← unify #[((c.lits.get! 0).lhs, (c.lits.get! 0).rhs)] {}
      trace[Meta.debug] "{subst}"
      trace[Meta.debug] "{(c.lits.get! 0).lhs}"
      trace[Meta.debug] "{(c.lits.get! 0).rhs}"
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic

set_option trace.Meta.debug true
-- set_option pp.all true

example (h : ∀ x, x ≠ c) : False := by
  go