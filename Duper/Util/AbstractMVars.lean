import Lean
import Duper.Util.Misc

namespace Duper

open Lean Meta abstractMVars

def abstractMVarsForall (e : Expr) : MetaM AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkForall s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }

def abstractMVarsLambdaWithIds (e : Expr) : MetaM (Expr × Array Expr × Array Name × Array Level) := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e
  -- Restore the corresponding expr mvarId
  let sfvars := s.fvars
  let mut fvarpos : HashMap FVarId Nat := {}
  for i in [:sfvars.size] do
    fvarpos := fvarpos.insert sfvars[i]!.fvarId! i
  let mut mvars := sfvars
  for (mid, fvar) in s.emap.toList do
    mvars := mvars.set! (fvarpos.find! fvar.fvarId!) (mkMVar mid)
  -- Restore the corresponding level mvarId
  let sparams := s.paramNames
  let mut parampos : HashMap Name Nat := {}
  for i in [:sparams.size] do
    parampos := parampos.insert sparams[i]! i
  let mut lmvars := sparams.map (Level.param)
  for (lmid, paramname) in s.lmap.toList do
    lmvars := lmvars.set! (parampos.find! (Lean.getParamLevelName! paramname)) (mkLevelMVar lmid)
  pure (e, mvars, sparams, lmvars)

def abstractMVarsLambda (e : Expr) : MetaM AbstractMVarsResult := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkLambda s.fvars e
  pure { paramNames := s.paramNames, numMVars := s.fvars.size, expr := e }