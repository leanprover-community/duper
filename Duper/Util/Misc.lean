import Lean
open Lean

instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

-- The following two functions are copied from Lean's
-- standard library. The only difference is that we
-- replace `whnf e` with `e`.
private partial def instantiateForallAux (ps : Array Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩
    match e with
    | Expr.forallE _ _ b _ => instantiateForallAux ps (i+1) (b.instantiate1 p)
    | _                => throwError "invalid instantiateForallNoReducing, too many parameters"
  else
    return e

/-- Given `e` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `B[p_1, ..., p_n]`. -/
def Lean.Expr.instantiateForallNoReducing (e : Expr) (ps : Array Expr) : MetaM Expr :=
  instantiateForallAux ps 0 e

open Lean.Meta.AbstractMVars in
open Lean.Meta in
def withAbstractMVarsLambda (e : Expr) (m : Expr → MetaM Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let (e, s) := AbstractMVars.abstractExprMVars e { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen s.ngen
  setMCtx s.mctx
  withLCtx s.lctx (← getLocalInstances) $ do
    let e ← m e
    return s.lctx.mkLambda s.fvars e