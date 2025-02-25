import Lean
import Duper.Util.Reduction

set_option linter.unusedVariables false

open Lean Lean.Meta Duper

initialize Lean.registerTraceClass `duper.match.debug

/-- Given an array of expression pairs (match_target, e), attempts to assign mvars in e to make e equal to match_target (without
    making any assignments to mvars that appear in protected_mvars).
    Returns true and performs mvar assignments if successful, returns false and does not perform any mvar assignments otherwise -/
partial def Lean.Meta.performMatch (l : Array (Expr × Expr)) (protected_mvars : Array MVarId) : MetaM Bool := do
  Core.checkMaxHeartbeats "match"
  let state ← saveState
  try
    trace[duper.match.debug] "About to attempt to match {l}"

    for (match_target, e) in l do
      let match_target_type ← betaEtaReduceInstMVars $ ← inferType match_target
      let e_type ← betaEtaReduceInstMVars $ ← inferType e
      if not (← match1 match_target_type e_type protected_mvars) then
        state.restore
        return false
      else if ← match1 match_target e protected_mvars then
        continue
      else
        state.restore
        return false

    trace[duper.match.debug] "Successfully matched {l}"
    return true
  catch ex =>
    trace[duper.match.debug] "Encountered error {ex.toMessageData} in match procedure"
    state.restore
    throw ex
where
  match1 (match_target e : Expr) (protected_mvars : Array MVarId) : MetaM Bool := do
    let match_target ← instantiateMVars match_target
    let e ← instantiateMVars e
    if match_target == e then return true else
    match_target.withApp fun match_target_hd match_target_tl => e.withApp fun e_hd e_tl => do
      match match_target_hd, e_hd with
      | Expr.fvar fid, Expr.fvar gid => do
        if fid == gid then
          matchArgs match_target_tl e_tl
        else
          return false
      | Expr.const fname flvls, Expr.const gname glvls => do
        if fname == gname &&
          (← (flvls.zip glvls).allM (fun (flvl, glvl) => isLevelDefEq flvl glvl)) then
          matchArgs match_target_tl e_tl
        else
          return false
      | Expr.forallE .., Expr.forallE .. =>
        return match_target_hd == e_hd && (← matchArgs match_target_tl e_tl)
      | Expr.lam .., Expr.lam .. =>
        return match_target_hd == e_hd && (← matchArgs match_target_tl e_tl)
      | Expr.fvar .., Expr.mvar .. =>
        matchRigidFlex match_target e protected_mvars
      | Expr.const .., Expr.mvar .. =>
        matchRigidFlex match_target e protected_mvars
      | Expr.forallE .., Expr.mvar .. =>
        matchRigidFlex match_target e protected_mvars
      | Expr.mvar .., Expr.mvar .. =>
        matchFlexFlex match_target e protected_mvars
      | _, _ => return false
  matchArgs (match_target_tl e_tl : Array Expr) : MetaM Bool := do
    if match_target_tl.size == e_tl.size then
      performMatch (match_target_tl.zip e_tl) protected_mvars
    else
      return false
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
