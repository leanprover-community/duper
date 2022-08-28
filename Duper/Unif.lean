import Lean

open Lean
open Lean.Meta

/-
partial def Lean.Meta.unify (l : Array (Expr × Expr)) : MetaM Bool := do
  let state ← saveState
  try
    for (t, s) in l do
      let t_type := (← instantiateMVars (← inferType t))
      let s_type := (← instantiateMVars (← inferType s))
      if (t_type != s_type) then
        state.restore
        return false
      else if ← isDefEq t s then
        continue
      else
        state.restore
        return false
    return true
  catch ex =>
    state.restore
    throw ex
-/

partial def Lean.Meta.unify (l : Array (Expr × Expr)) : MetaM Bool := do
  Core.checkMaxHeartbeats "unify"
  let state ← saveState
  try
    for (t, s) in l do
      let t_type := (← instantiateMVars (← inferType t))
      let s_type := (← instantiateMVars (← inferType s))
      if (t_type != s_type) then
        state.restore
        return false
      else if ← unify1 t s then
        continue
      else
        state.restore
        return false
    return true
  catch ex =>
    state.restore
    throw ex
where
  unify1 (s t : Expr) : MetaM Bool := do
    let s ← instantiateMVars s --TODO: instantiate more lazily?
    let t ← instantiateMVars t
    if s == t then return true else
    s.withApp fun f ss => t.withApp fun g tt =>
      match f, g with
      | Expr.fvar .., Expr.fvar .. =>
        unifyRigidRigid s t
      | Expr.const .., Expr.const .. =>
        unifyRigidRigid s t
      | Expr.mvar mVarId .., Expr.fvar .. =>
        unifyFlexRigid s t
      | Expr.mvar mVarId .., Expr.const .. =>
        unifyFlexRigid s t
      | Expr.fvar .., Expr.mvar mVarId .. =>
        unifyFlexRigid t s
      | Expr.const .., Expr.mvar mVarId .. =>
        unifyFlexRigid t s
      | Expr.mvar mVarId .., Expr.mvar .. =>
        unifyFlexFlex s t
      -- Adding cases involving forallE (treating it similar to Expr.const)
      | Expr.forallE .., Expr.forallE .. =>
        unifyRigidRigid s t
      | Expr.mvar .., Expr.forallE .. =>
        unifyFlexRigid s t
      | Expr.forallE .., Expr.mvar .. =>
        unifyFlexRigid t s
      | _, _ => return false
  unifyRigidRigid (s t : Expr) : MetaM Bool := do
    s.withApp fun f ss => t.withApp fun g tt =>
      if f == g
      then
        if tt.size == ss.size
        then unify (tt.zip ss)
        else return false
      else return false
  unifyFlexFlex (s t : Expr) : MetaM Bool := do
    s.withApp fun f ss => t.withApp fun g tt => do
      if tt.isEmpty && ss.isEmpty
      then
        if f == g
        then return true
        else
          Lean.MVarId.assign f.mvarId! t
          return true
      else return false
  unifyFlexRigid (s t : Expr) : MetaM Bool := do
    s.withApp fun f ss => t.withApp fun g tt => do
      match ← getExprMVarAssignment? f.mvarId! with
      | some e =>
        unify1 (mkAppN e ss) t
      | none => do
        if ss.isEmpty
        then
          if ← occursCheck f.mvarId! t
          then
            Lean.MVarId.assign f.mvarId! t
            return true
          else
            return false
        else return false