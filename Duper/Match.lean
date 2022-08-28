import Lean

open Lean
open Lean.Meta

#check isDefEq
#check Lean.Meta.Simp.tryTheoremWithExtraArgs?
#check withNewMCtxDepth
#check MonadControlT
#check MonadControl
#check Lean.Expr.abstractM

/-- Given an array of expression pairs (match_target, e), attempts to assign mvars in e to make e equal to match_target (without
    making any assignments to mvars that appear in match_target).
    Returns true and performs mvar assignments if successful, returns false and does not perform any mvar assignments otherwise -/
partial def Lean.Meta.performMatch (l : Array (Expr × Expr)) : MetaM Bool := do
  Core.checkMaxHeartbeats "match"
  let state ← saveState
  try
    -- Collect all mvars from each match_target and store them in an array to ensure that performMatch never assigns to any of them
    let protected_mvars := l.foldl (fun acc (match_target, _) => match_target.collectMVars acc) {}
    let protected_mvars := protected_mvars.result

    for (match_target, e) in l do
      let match_target_type := (← instantiateMVars (← inferType match_target))
      let e_type := (← instantiateMVars (← inferType e))
      if (match_target_type != e_type) then
        state.restore
        return false
      else if ← match1 match_target e protected_mvars then
        continue
      else
        state.restore
        return false
    return true
  catch ex =>
    state.restore
    throw ex
where
  match1 (match_target e : Expr) (protected_mvars : Array MVarId) : MetaM Bool := do
    let match_target ← instantiateMVars match_target
    let e ← instantiateMVars e
    if match_target == e then return true else
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl =>
      match match_target_hd, e_hd with
      | Expr.fvar .., Expr.fvar .. => matchRigidRigid match_target e
      | Expr.const .., Expr.const .. => matchRigidRigid match_target e
      | Expr.forallE .., Expr.forallE .. => matchRigidRigid match_target e
      | Expr.fvar .., Expr.mvar .. => matchRigidFlex match_target e protected_mvars
      | Expr.const .., Expr.mvar .. => matchRigidFlex match_target e protected_mvars
      | Expr.forallE .., Expr.mvar .. => matchRigidFlex match_target e protected_mvars
      | Expr.mvar .., Expr.mvar .. => matchFlexFlex match_target e protected_mvars
      | _, _ => return false
  matchRigidRigid (match_target e : Expr) : MetaM Bool := do
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl =>
      if match_target_hd == e_hd then 
        if match_target_tl.size == e_tl.size then performMatch (match_target_tl.zip e_tl)
        else return false
      else return false
  matchRigidFlex (match_target e : Expr) (protected_mvars : Array MVarId) : MetaM Bool := do
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl => do
      match ← getExprMVarAssignment? e_hd.mvarId! with
      | some exp => match1 match_target (mkAppN exp e_tl) protected_mvars
      | none => do
        if e_tl.isEmpty then
          if (← occursCheck e_hd.mvarId! match_target) && not (protected_mvars.contains (e_hd.mvarId!)) then
            Lean.MVarId.assign e_hd.mvarId! match_target
            return true
          else return false
        else return false
  matchFlexFlex (match_target e : Expr) (protected_mvars : Array MVarId) : MetaM Bool := do
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl => do
      if match_target_tl.isEmpty && e_tl.isEmpty then
        if match_target_hd == e_hd then
          return true
        else
          if not (protected_mvars.contains (e_hd.mvarId!)) then
            Lean.MVarId.assign e_hd.mvarId! match_target
            return true
          else return false
      else return false