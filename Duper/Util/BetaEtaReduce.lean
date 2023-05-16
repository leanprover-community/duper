import Lean

namespace Duper
open Std
open Lean
open Meta
open Core

/-- Eta-expand a beta-reduced expression -/
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

/-- Instantiates mvars then applies beta and eta reduction exhaustively. -/
def betaEtaReduce (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Core.betaReduce e
  match e.etaExpanded? with
  | some e => return e
  | none => return e

/-- Applies beta, eta, and zeta reduction exhaustively. I believe that by applying zeta reduction
    first, then beta reduction, and finally eta reduction, it is not necessary to iterate this
    function until a fixed point is reached (the output should always be a fixed point) -/
def betaEtaZetaReduce (e : Expr) : MetaM Expr := do
  let e ← Meta.zetaReduce e
  let e ← betaReduce e
  match e.etaExpanded? with
  | some e => return e
  | none => return e