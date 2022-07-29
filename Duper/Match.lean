import Lean

open Lean
open Lean.Meta

/-- Given an array of expression pairs (match_target, e), attempts to assign mvars in e to make e equal to match_target.
    Returns true and performs mvar assignments if successful, returns false and does not perform any mvar assignments otherwise -/
partial def Lean.Meta.performMatch (l : Array (Expr × Expr)) : MetaM Bool := do
  Core.checkMaxHeartbeats "match"
  let state ← saveState
  try
    for (match_target, e) in l do
      let match_target_type := (← instantiateMVars (← inferType match_target))
      let e_type := (← instantiateMVars (← inferType e))
      if (match_target_type != e_type) then
        state.restore
        return false
      else if ← match1 match_target e then
        continue
      else
        state.restore
        return false
    return true
  catch ex =>
    state.restore
    throw ex
where
  match1 (match_target e : Expr) : MetaM Bool := do
    let match_target ← instantiateMVars match_target
    let e ← instantiateMVars e
    if match_target == e then return true else
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl =>
      match match_target_hd, e_hd with
      | Expr.fvar .., Expr.fvar .. => matchRigidRigid match_target e
      | Expr.const .., Expr.const .. => matchRigidRigid match_target e
      | Expr.forallE .., Expr.forallE .. => matchRigidRigid match_target e
      | Expr.fvar .., Expr.mvar .. => matchRigidFlex match_target e
      | Expr.const .., Expr.mvar .. => matchRigidFlex match_target e
      | Expr.forallE .., Expr.mvar .. => matchRigidFlex match_target e
      | _, _ => return false
  matchRigidRigid (match_target e : Expr) : MetaM Bool := do
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl =>
      if match_target_hd == e_hd then 
        if match_target_tl.size == e_tl.size then performMatch (match_target_tl.zip e_tl)
        else return false
      else return false
  matchRigidFlex (match_target e : Expr) : MetaM Bool := do
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl => do
      match ← getExprMVarAssignment? e_hd.mvarId! with
      | some exp => match1 match_target (mkAppN exp e_tl)
      | none => do
        if e_tl.isEmpty then
          -- Note: Despite the misleading message, occursCheck returns true iff match_target does not contain e_hd.mvarId!
          if ← occursCheck e_hd.mvarId! match_target then
            assignExprMVar e_hd.mvarId! match_target
            return true
          else return false
        else return false