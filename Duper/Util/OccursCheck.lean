/-
Copyright (c) 2023 Duper development team. All rights reserved.
Author: Duper development team
-/
import Lean.MetavarContext

namespace Lean

/--
  Return true if `e` **must not** contain `mvarId` directly or indirectly
  This function considers assigments and delayed assignments. -/
partial def mustNotOccursCheck [Monad m] [MonadMCtx m] (mvarId : MVarId) (e : Expr) : m Bool := do
  if !e.hasExprMVar then
    return true
  else
    match (← visit e |>.run |>.run {}) with
    | (.ok .., _)    => return true
    | (.error .., _) => return false
where
  visitMVar (mvarId' : MVarId) : ExceptT Unit (StateT ExprSet m) Unit := do
    if mvarId == mvarId' then
      throw () -- found
    else
      let decl := (← getMCtx).getDecl mvarId
      -- Modification : We also need to check whether metavariables
      --   might depend on the metavariable being checked, so we also
      --   visit the type of the metavariable declaration
      visit decl.type
      match (← getExprMVarAssignment? mvarId') with
      | some v => visit v
      | none   =>
        match (← getDelayedMVarAssignment? mvarId') with
        | some d => visitMVar d.mvarIdPending
        | none   => return ()

  visit (e : Expr) : ExceptT Unit (StateT ExprSet m) Unit := do
    if !e.hasExprMVar then
      return ()
    else if (← get).contains e then
      return ()
    else
      modify fun s => s.insert e
      match e with
      | Expr.proj _ _ s      => visit s
      | Expr.forallE _ d b _ => visit d; visit b
      | Expr.lam _ d b _     => visit d; visit b
      | Expr.letE _ t v b _  => visit t; visit v; visit b
      | Expr.mdata _ b       => visit b
      | Expr.app f a         => visit f; visit a
      | Expr.mvar mvarId     => visitMVar mvarId
      | _                    => return ()

private def Expr.isOccursRigid [Monad m] [MonadLCtx m] : Expr → m Bool
| .bvar _ => pure true
-- fvar : rigid if it's `cdecl`, not rigid if it's `ldecl`
| e@(.fvar id) => do
  let lctx ← getLCtx
  match lctx.find? id with
  | none => panic! s!"Expr.isOccursRigid : Free variable {e} is not in local context"
  | some (.cdecl _ _ _ _ _ _) => pure true
  | some (.ldecl _ _ _ _ _ _ _) => pure false
| .mvar _ => pure false
| .sort _ => pure true
| .const _ _ => pure true
| .app _ _ => pure false
| .lam _ _ _ _ => pure false
| .forallE _ _ _ _ => pure true
| .letE _ _ _ _ _ => pure false
| .lit _ => pure true
| .mdata _ e => e.isOccursRigid
| .proj _ _ _ => pure false

/--
  Return true if `e` **must** contain `mvarId` as a subterm directly or
    indirectly after further mvar instantiation and β-reduction
  This function considers assigments and delayed assignments. -/
partial def mustOccursCheck [Monad m] [MonadMCtx m] [MonadLCtx m] (mvarId : MVarId) (e : Expr) : m Bool := do
  if !e.hasExprMVar then
    return false
  else
    match (← visit e |>.run |>.run {}) with
    | (.ok .., _)    => return false
    | (.error .., _) => return true
where
  visitMVar (mvarId' : MVarId) : ExceptT Unit (StateT ExprSet m) Unit := do
    if mvarId == mvarId' then
      throw () -- found
    else
      match (← getExprMVarAssignment? mvarId') with
      | some v => visit v
      | none   =>
        match (← getDelayedMVarAssignment? mvarId') with
        | some d => visitMVar d.mvarIdPending
        | none   => return ()

  visit (e : Expr) : ExceptT Unit (StateT ExprSet m) Unit := do
    if !e.hasExprMVar then
      return ()
    else if (← get).contains e then
      return ()
    else
      modify fun s => s.insert e
      match e with
      | Expr.proj _ _ s      => visit s
      | Expr.forallE _ d b _ => visit d; visit b
      -- does not visit type of lambda binders
      | Expr.lam _ _ b _     => visit b
      -- does not visit type and value of "let" binders
      | Expr.letE _ _ _ b _  => visit b
      | Expr.mdata _ b       => visit b
      | Expr.app _ _         =>
        let f := e.getAppFn
        visit f
        if ← f.isOccursRigid then
          let args := e.getAppArgs
          for arg in args do
            visit arg
      | Expr.mvar mvarId     => visitMVar mvarId
      | _                    => return ()

end Lean
