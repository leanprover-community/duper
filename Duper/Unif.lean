import Lean

open Lean
open Lean.Meta

partial def Lean.Meta.unify (l : Array (Expr × Expr)) : MetaM Bool := do
  Core.checkMaxHeartbeats "unify"
  let state ← saveState
  try
    for (t, s) in l do
      let t_type := (← instantiateMVars (← inferType t))
      let s_type := (← instantiateMVars (← inferType s))
      if ¬ (← unify1 t_type s_type) then
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
    trace[Prover.saturate] "UNIFY1 {s} {t}"
    let s ← instantiateMVars s --TODO: instantiate more lazily?
    let t ← instantiateMVars t
    if s == t then return true else
    s.withApp fun f ss => t.withApp fun g tt =>
      match f, g with
      | Expr.fvar fid, Expr.fvar gid =>
        if fid == gid
        then unifyArgs ss tt
        else return false
      | Expr.const fname flvls, Expr.const gname glvls => do
        if fname == gname 
          && (← (flvls.zip glvls).allM fun ((flvl, glvl)) => isLevelDefEq flvl glvl)
        then unifyArgs ss tt
        else return false
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
      | Expr.forallE .., Expr.forallE .. =>
        return s == t
      | Expr.mvar .., Expr.forallE .. =>
        unifyFlexRigid s t
      | Expr.forallE .., Expr.mvar .. =>
        unifyFlexRigid t s
      | Expr.sort flvl, Expr.sort glvl => do
        trace[Prover.saturate] "UNIF {flvl} {glvl}"
        isLevelDefEq flvl glvl
      | _, _ => return false
  unifyArgs (ss tt : Array Expr) : MetaM Bool := do
    if tt.size == ss.size
    then unify (tt.zip ss)
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