
import Lean
import Std.Data.BinomialHeap

open Lean
open Lean.Meta
open Lean.Parser


namespace Testduper
open Lean.Elab.Tactic

def cnf (formulas : List (Expr × Expr)) : TacticM (List (Bool × Expr × Expr)) := do
  let formulas := formulas.map Prod.fst
  let formulas ← formulas.mapM fun f => do
    let c ← match f with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl]) ty) e₁) e₂ =>
      return (true, e₁, e₂)
    | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl]) ty) e₁) e₂) =>
      return (false, e₁, e₂)
    | _ => throwError "No match: {f}"
    return c
  return formulas


open Std

-- Note for when I update Lean version: TransformStep.visit has been renamed TransformStep.continue,
-- so when I update Lean, I need to replace TransformStep.visit with TransformStep.continue below
def replace (e : Expr) (target : Expr) (replacement : Expr) : MetaM Expr := do
  Core.transform e (pre := fun s => do
    if (← instantiateMVars s) == (← instantiateMVars target) then
      return TransformStep.done replacement
    else return TransformStep.visit s)

def saturate (clauses : List (Bool × Expr × Expr)) : TacticM Unit := do
  let mut passive : BinomialHeap (Nat × (Bool × Expr × Expr)) fun c d => c.1 ≤ d.1 := 
    BinomialHeap.empty
  let mut active := []
  let mut clauseCounter := 0
  let mut myPosClause : Option (Bool × Expr × Expr) := none

  for c in clauses.reverse do
    passive := passive.insert (clauseCounter, c)
    clauseCounter := clauseCounter + 1

  do repeat
    match passive.deleteMin with
    | some ((_, givenClause), passive') => 
      passive := passive'
      -- logInfo m!"Given Clause: {givenClause}"

      if givenClause.1 then
        myPosClause := some givenClause
      else
        -- EqRes
        if givenClause.2.1 == givenClause.2.2 then
          logInfo "contradiction"
          return ()
        -- Superposition
        let posClause := myPosClause.get!
        let res ← replace givenClause.2.1 posClause.2.1 posClause.2.2
        if res != givenClause.2.1 then
          let newClause := (givenClause.1, res, givenClause.2.2)
          passive := passive.insert (clauseCounter, newClause)
          clauseCounter := clauseCounter + 1
          -- logInfo m!"New Clause: {newClause}"

      active := givenClause :: active
    | none => 
      logInfo "saturated"
      return ()
    


end Testduper


namespace Lean.Elab.Tactic

def collectAssms : TacticM (List (Expr × Expr)) := do
  let mut formulas := []
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← Lean.FVarId.getDecl fVarId
    unless ldecl.binderInfo.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
      formulas := (← instantiateMVars ldecl.type, ← mkAppM ``eq_true #[mkFVar fVarId]) :: formulas
  return formulas

syntax (name := testduper) "testduper" (colGt ident) ? : tactic

@[tactic testduper]
def evalTestDuper : Tactic
| `(tactic| testduper) => do
  let startTime ← IO.monoMsNow
  replaceMainGoal [(← Lean.MVarId.intros (← getMainGoal)).2]
  let mvar ← withMainContext do mkFreshExprMVar (← mkArrow (← mkAppM ``Not #[← getMainTarget]) (mkConst ``False))
  Lean.MVarId.assign (← getMainGoal) (mkApp2 (mkConst ``Classical.byContradiction) (← getMainTarget) mvar)
  replaceMainGoal [mvar.mvarId!]
  replaceMainGoal [(← Lean.MVarId.intro (← getMainGoal) `h).2]
  withMainContext do
    let formulas ← collectAssms
    let cnf ← Testduper.cnf formulas
    Testduper.saturate cnf
    logInfo s!"Done. Time: {(← IO.monoMsNow) - startTime}ms"
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
