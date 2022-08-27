import Lean

open Lean
open Lean.Meta

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