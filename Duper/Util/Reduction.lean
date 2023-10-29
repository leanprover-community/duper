import Lean

namespace Duper
open Std
open Lean
open Meta
open Core

register_option reduceInstances : Bool := {
  defValue := true
  descr := "Whether to eliminate mdata and apply whnf to instances"
}

def getReduceInstances (opts : Options) : Bool :=
  reduceInstances.get opts

def getReduceInstancesM : CoreM Bool := do
  let opts ← getOptions
  return getReduceInstances opts

/-- This function is expensive and should only be used in preprocessing -/
partial def preprocessFact (fact : Expr) : MetaM Expr := do
  if (← getReduceInstancesM) then
    let red (e : Expr) : MetaM TransformStep := do
      let e := e.consumeMData
      let e ← whnf e
      return .continue e
    -- Reduce
    trace[Preprocessing.debug] "fact before preprocessing: {fact}"
    let fact ← withTransparency .instances <| Meta.transform fact (pre := red) (usedLetOnly := false)
    let restoreNE (e : Expr) : MetaM TransformStep := do
      match e with
      | .app (.const ``Not []) (.app (.app (.app (.const ``Eq lvls) ty) e₁) e₂) =>
        return .visit (.app (.app (.app (.const ``Ne lvls) ty) e₁) e₂)
      | _ => return .continue
    -- Restore ≠, i.e., ¬ a = b ⇒ a ≠ b
    -- If we don't do this, it seems that clausification will become more inefficient
    let fact ← Core.transform fact (pre := restoreNE)
    trace[Preprocessing.debug] "fact after preprocessing: {fact}"
    return fact
  else
    trace[Preprocessing.debug] "Skipping preprocessing because reduceInstances option is set to false"
    return fact

/-- Eta-expand a beta-reduced expression. This function is currently unused -/
partial def etaLong (e : Expr) : MetaM Expr := do
  match e with
  | Expr.forallE .. =>
    forallTelescope e fun xs b => do
      let bl ← etaLong b
      mkForallFVarsEtaLong xs bl
  | Expr.lam .. =>
    lambdaTelescope e fun xs b => do
      let bl ← etaLong b
      mkLambdaFVarsEtaLong xs bl
  | Expr.letE .. => do
      throwError "There should be no let binders because they should have been reduced during preprocessing"
  | Expr.app .. => do
      let e' ← etaExpand e
      if e'.isApp then
        e'.withApp fun f args => do
          return mkAppN f (← args.mapM etaLong)
      else
        etaLong e
  | Expr.proj _ _ b => return e.updateProj! (← etaLong b)
  | Expr.mdata _ b => etaLong b
  | _ => etaExpand e
where
  mkForallFVarsEtaLong (xs : Array Expr) (b : Expr) : MetaM Expr := do
    let mut ret := b
    for x in xs.reverse do
      ret ← mkForallFVars #[x] ret
      -- Eta-expand type
      let ty ← etaLong (ret.bindingDomain!)
      ret := ret.updateForall! ret.bindingInfo! ty ret.bindingBody!
    return ret
  mkLambdaFVarsEtaLong (xs : Array Expr) (b : Expr) : MetaM Expr := do
    let mut ret := b
    for x in xs.reverse do
      ret ← mkLambdaFVars #[x] ret
      -- Eta-expand type
      let ty ← etaLong (ret.bindingDomain!)
      ret := ret.updateLambda! ret.bindingInfo! ty ret.bindingBody!
    return ret

/-- Applies eta reduction to `e` and all of its subexpressions
  TODO: Make sure that when calling this function from other files,
  the term supplied to it does not contain loose bound variables. -/
partial def etaReduce (e : Expr) : MetaM Expr := do
  let post (e : Expr) : MetaM TransformStep := do
    match e.etaExpanded? with
    | some f => return .done f
    | none => return .done e
  Meta.transform e (post := post) (usedLetOnly := true)

/-- Instantiates mvars then applies beta, eta and zeta reduction exhaustively. -/
def betaEtaReduceInstMVars (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Core.betaReduce e
  etaReduce e

/-- Applies beta, eta and zeta reduction exhaustively -/
def betaEtaReduce (e : Expr) : MetaM Expr := do
  let e ← Core.betaReduce e
  etaReduce e