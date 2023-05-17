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

/-- Applies eta reduction to `e` and all of its subexpressions -/
partial def etaReduce (e : Expr) : MetaM Expr := do
  match e with
  | e@(Expr.lit _)           => return e
  | e@(Expr.bvar _)          => return e
  | e@(Expr.fvar _)          => return e
  | e@(Expr.sort u)          => return e
  | e@(Expr.const _ us)      => return e
  | e@(Expr.mvar mvarId)     => return e
  | e@(Expr.proj _ _ s)      => return e.updateProj! (← etaReduce s)
  | e@(Expr.app f a)         => return e.updateApp! (← etaReduce f) (← etaReduce a)
  | e@(Expr.mdata _ b)       => return e.updateMData! (← etaReduce b)
  | e@(Expr.forallE _ d b _) => -- Need to suitably do abstraction for body so bvars don't break
    let e := e.updateForallE! (← etaReduce d) b
    -- Meta.forallTelescope doesn't work because if I have p → q → r, then d will be p and b will be r and I'll have missed q.
    -- So we use a bounded telescope with a maxFVar limit of 1 to ensure that body corresponds with b
    Meta.forallBoundedTelescope e (some 1) fun xs body => do
      Meta.mkForallFVars xs (← etaReduce body)
  | e@(Expr.lam _ d b _)     => -- Need to suitably do abstraction for body so bvars don't break
    let e := e.updateLambdaE! (← etaReduce d) (mkMData .empty b)
    -- Ideally, we would use Meta.lambdaBoundedTelescope analogous to how Meta.forallTelescope was used for the forallE case.
    -- But Meta.lambdaBoundedTelescope no longer exists, so we add an mdata around b to ensure that Meta.lambdaTelescope's body
    -- corresponds to b (rather than the body of an inner lambda expression)
    Meta.lambdaTelescope e fun xs body => do
      let resLambda ← Meta.mkLambdaFVars xs (← etaReduce body.consumeMData)
      match resLambda.etaExpanded? with
      | some resLambdaReduced => return resLambdaReduced
      | none => return resLambda
  | e@(Expr.letE _ t v b _)  => -- Let expressions can have bvars in the body, so rather than deal with that, we just zetaReduce
    let e ← zetaReduce e
    etaReduce e

/-- Instantiates mvars then applies beta and eta reduction exhaustively. -/
def betaEtaReduce (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e ← Core.betaReduce e
  etaReduce e

/-- Applies beta, eta, and zeta reduction exhaustively. I believe that by applying zeta reduction
    first, then beta reduction, and finally eta reduction, it is not necessary to iterate this
    function until a fixed point is reached (the output should always be a fixed point) -/
def betaEtaZetaReduce (e : Expr) : MetaM Expr := do
  let e ← Meta.zetaReduce e
  let e ← betaReduce e
  match e.etaExpanded? with
  | some e => return e
  | none => return e