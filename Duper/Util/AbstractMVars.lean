import Lean

namespace Duper

open Lean Meta abstractMVars

def abstractMVarsForall (e : Expr) : MetaM AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkForall s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }

def abstractMVarsLambdaWithIds (e : Expr) : MetaM (Expr × Array Expr) := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e

  let sfvars := s.fvars
  let mut fvarpos : HashMap FVarId Nat := {}
  for i in [:sfvars.size] do
    fvarpos := fvarpos.insert sfvars[i]!.fvarId! i
  let mut mvars := sfvars
  for (mid, fvar) in s.emap.toList do
    (_, mvars) := mvars.swapAt! (fvarpos.find! fvar.fvarId!) (mkMVar mid)
  pure (e, mvars)

def abstractMVarsLambda (e : Expr) : MetaM AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }