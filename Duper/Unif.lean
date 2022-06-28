import Lean

open Lean
open Lean.Meta

partial def Lean.Meta.unify (l : Array (Expr × Expr)) : MetaM Bool := do
  Core.checkMaxHeartbeats "unify"
  trace[Meta.debug] "unify: {l}"
  for (t, s) in l do
    let t_type := (← instantiateMVars (← inferType t))
    let s_type := (← instantiateMVars (← inferType s))
    if (t_type != s_type) then return false
    else if ← unify1 t s then continue
    else return false
  return true
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
          assignExprMVar f.mvarId! t
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
            assignExprMVar f.mvarId! t
            return true
          else 
            return false
        else return false

-- def test : MetaM Unit := do
--   let ty := mkConst ``Nat
--   let x ← mkFreshExprMVar ty
--   let y ← mkFreshExprMVar ty
--   let s := mkApp (mkConst ``Nat.succ) y
--   let t := y
--   let res ← unify #[(s, t)]
--   trace[Meta.debug] "s: {s}"
--   trace[Meta.debug] "t: {t}"
--   trace[Meta.debug] "x: {x}"
--   trace[Meta.debug] "y: {y}"
--   trace[Meta.debug] "res: {res}"

-- set_option trace.Meta.debug true
-- #eval test
