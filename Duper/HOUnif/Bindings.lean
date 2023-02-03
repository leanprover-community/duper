import Lean
import Duper.Util.Misc
import Duper.Util.LazyList
import Duper.HOUnif.UnifProblem
open Lean

-- TODO: Will `ListT` (Haskell "ListT done right") provide a more
-- elegant way of modelling monadic nondeterminism?

-- Note:
-- 1. Rules may modify the MetaM mctx arbitrarily, so they should
--    be run with "withoutModifyingMCtx"
-- 2. MetaM actions taken out of lazy lists returned by the rules
--    may modify the MetaM mctx arbitrarily, so they should also
--    be run with "withoutModifyingMCtx"

open Duper

namespace HOUnif

def withoutModifyingMCtx (x : MetaM α) : MetaM α := do
  let s ← getMCtx
  try
    x
  finally
    setMCtx s

def iteration (F : Expr) (p : UnifProblem) (funcArgOnly : Bool) : MetaM (LazyList <| MetaM (Array UnifProblem)) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescope Fty fun xs β₁ => (do
    let ctx₀ ← read
    let mut iterAtIFuns : Array (Nat → MetaM (Array UnifProblem)):= #[]
    for xi in xs do
      -- Iteration at xᵢ
      let αi ← Meta.inferType xi
      let (xys, _, _) ← Meta.forallMetaTelescope αi
      if xys.size == 0 ∧ funcArgOnly then
        continue
      let s₁ ← getMCtx
      -- Iteration at argument `i`
      -- Restore context and mctx
      iterAtIFuns := iterAtIFuns.push (fun i => withReader (fun _ => ctx₀) do
        setMCtx s₁
        -- `ytys` is an array of metavariables
        let mut ytys := #[]
        -- `ys` is an array of free variables
        let mut ys := #[]
        -- Adding `ys` to this `lctx` along with creating them
        let mut lctx ← getLCtx
        for _ in List.range i do
          let yty_ty ← Meta.mkFreshLevelMVar
          let yty ← withReader (fun ctx : Meta.Context => { ctx with lctx := lctx }) do
            let yty_absty ← 
              Meta.mkForallFVars (xs ++ ys) (mkSort yty_ty)
            return mkAppN (← Meta.mkFreshExprMVar yty_absty) (xs ++ ys)
          let fvarId ← mkFreshFVarId
          lctx := lctx.mkLocalDecl fvarId `_ yty .default
          let fvar := mkFVar fvarId
          ytys := ytys.push yty
          ys := ys.push fvar
        -- Make Gᵢs
        let lastExpr ← withReader (fun ctx : Meta.Context => { ctx with lctx := lctx }) do
          let mut appargs := #[]
          for xyi in xys do
            let γi ← Meta.inferType xyi
            let GiTy ← Meta.mkForallFVars (xs ++ ys) γi
            let mGi ← Meta.mkFreshExprMVar GiTy
            MVarId.assign xyi.mvarId! mGi
            appargs := appargs.push (mkAppN mGi (xs ++ ys))
          let body := mkAppN xi appargs
          return (← Meta.mkLambdaFVars ys body)
        -- Make H
        let lastExprTy ← Meta.inferType lastExpr
        -- Assuming that β₂ contains no loose bound variables
        let Hty ← Meta.mkForallFVars xs (.forallE `_ lastExprTy β₁ .default)
        let mH ← Meta.mkFreshExprMVar Hty
        let mt ← Meta.mkLambdaFVars xs (mkAppN mH xs)
        MVarId.assign F.mvarId! mt
        return #[{p with checked := false, mctx := ← getMCtx}]
      )
      -- Get rid of metavariables in `xys`
      setMCtx p.mctx
    let iterAtIArr := iterAtIFuns.map (fun f => (LazyList.nats 0).map f)
    return LazyList.interleaveN iterAtIArr
  )

-- `F` is a metavariable
def jpProjection (F : Expr) (p : UnifProblem) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescope Fty fun xs β => (do
    let mut ret : Array UnifProblem := #[]
    let s₀ ← getMCtx
    for xi in xs do
      let αi ← Meta.inferType xi
      -- TODO 2
      if αi == β then
        let t ← Meta.mkLambdaFVars xs xi
        MVarId.assign F.mvarId! t
        ret := ret.push {p with checked := false, mctx := ← getMCtx}
      setMCtx s₀
    return ret)

-- `F` is a metavariable
def huetProjection (F : Expr) (p : UnifProblem) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescope Fty fun xs β => (do
    let mut ret : Array UnifProblem := #[]
    for xi in xs do
      let αi ← Meta.inferType xi
      -- If the result types does not match, return #[]
      -- If the result type matches, return #[binding]
      let binding ← withoutModifyingMCtx <| Meta.withNewMCtxDepth <| do
        let (ys, _, β') ← Meta.forallMetaTelescope αi
        -- TODO 2
        if β' != β then
          return #[]
        let mut appargs := #[]
        for yi in ys do
          -- `xi`s are eliminated
          let mvarTy ← Meta.mkForallFVars xs (← Meta.inferType yi)
          -- newMVar : [α] → γi
          let newMVar ← Meta.mkFreshExprMVar mvarTy
          -- yi := newMVar [xs]
          MVarId.assign yi.mvarId! newMVar
          appargs := appargs.push (mkAppN newMVar xs)
        let mt ← Meta.mkLambdaFVars xs (mkAppN xi appargs)
        -- Metavariables are eliminated
        let res ← Meta.abstractMVars mt
        -- Assign metavariable
        let s' ← withoutModifyingMCtx <| do
          setMCtx p.mctx
          let (_, _, t) ← Meta.openAbstractMVarsResult res
          MVarId.assign F.mvarId! t
          return {p with checked := false, mctx := ← getMCtx}
        return #[s']
      ret := ret.append binding
    return ret)

-- `F` is a metavariable, and `g` is a constant
def imitation (F : Expr) (g : Expr) (p : UnifProblem) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  let gty ← Meta.inferType g
  Meta.forallTelescope Fty fun xs β => 
    Meta.withNewMCtxDepth <| do
      let (ys, _, β') ← Meta.forallMetaTelescope gty
      -- TODO 2
      if β' != β then
        return #[]
      let mut appargs := #[]
      for yi in ys do
        let γi ← Meta.inferType yi
        -- `xi`s are eliminated
        let mvarTy ← Meta.mkForallFVars xs γi
        -- newMVar : [α] → γi
        let newMVar ← Meta.mkFreshExprMVar mvarTy
        -- yi := newMVar [xs]
        MVarId.assign yi.mvarId! newMVar
        appargs := appargs.push (mkAppN newMVar xs)
      -- Metavariables are eliminated
      let mt ← Meta.mkLambdaFVars xs (mkAppN g appargs)
      let res ← Meta.abstractMVars mt
      let s' ← withoutModifyingMCtx <| do
        setMCtx p.mctx
        let (_, _, t) ← Meta.openAbstractMVarsResult res
        MVarId.assign F.mvarId! t
        return {p with checked := false, mctx := ← getMCtx}
      return #[s']

-- Both `F` and `G` are metavariables
-- Question: How to generalize to dependent types?
-- Proposal
--   Premises
--     F : (x₁ : α₁) → (x₂ : α₂) → ⋯ → (xₙ : αₙ) → β x₁ x₂ ⋯ xₙ (F : ∀ [x], β [x])
--     G : (y₁ : γ₁) → (y₂ : γ₂) → ⋯ → (yₘ : γₘ) → δ y₁ y₂ ⋯ yₙ (G : ∀ [y], δ [y])
---------------------------------------------------------------
--   Binding
--     η : ∀ [x] [y], Type ?u
--     H : ∀ [x] [y], η [x] [y]
--     F ↦ λ [x]. H [x] (F₁ [x]) ⋯ (Fₘ [x])
--     G ↦ λ [y]. H (G₁ [y]) ⋯ (Gₙ [y]) [y]
--   Extra Unification Problems:
--     λ[x]. η [x] (F₁ [x]) ⋯ (Fₘ [x]) =? λ[x]. β [x]
--     λ[y]. η (G₁ [y]) ⋯ (Gₙ [y]) [y] =? λ[y]. δ [y]
-- `Note`: Currently, we ignore dependent types. If any of β or η depends
--         on preceeding bound variables, we generate no bindings.
def identification (F : Expr) (G : Expr) (p : UnifProblem) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  let Gty ← Meta.inferType G
  let (same, Hty) ← Meta.forallTelescope Fty fun xs β => Meta.forallTelescope Gty fun ys β' => do
    -- TODO 2
    let Hty ← Meta.mkLambdaFVars (xs ++ ys) β
    return (β' == β, Hty)
  if ¬ same then
    return #[]
  Meta.withNewMCtxDepth <| do
    let mH ← Meta.mkFreshExprMVar Hty
    -- Binding for `F`
    let mtF ← Meta.forallTelescope Fty fun xs _ => do
      let (ys, _, _) ← Meta.forallMetaTelescope Gty
      let mut appargs := #[]
      for xi in xs do
        appargs := appargs.push xi
      for yi in ys do
        let γi ← Meta.inferType yi
        let mvarTy ← Meta.mkForallFVars xs γi
        let newMVar ← Meta.mkFreshExprMVar mvarTy
        MVarId.assign yi.mvarId! newMVar
        appargs := appargs.push (mkAppN newMVar xs)
      Meta.mkLambdaFVars xs (mkAppN mH appargs)
    -- Bindings for `G`
    let mtG ← Meta.forallTelescope Gty fun ys _ => do
      let (xs, _, _) ← Meta.forallMetaTelescope Fty    
      let mut appargs := #[]
      for xi in xs do
        let αi ← Meta.inferType xi
        let mvarTy ← Meta.mkForallFVars ys αi
        let newMVar ← Meta.mkFreshExprMVar mvarTy
        MVarId.assign xi.mvarId! newMVar
        appargs := appargs.push (mkAppN newMVar ys)
      for yi in ys do
        appargs := appargs.push yi
      Meta.mkLambdaFVars ys (mkAppN mH appargs)
    -- Combine them together, then abstract away all the metavariables
    let mtFG ← Meta.mkAppM ``Prod.mk #[mtF, mtG]
    let resFG ← Meta.abstractMVars mtFG
    let s' ← withoutModifyingMCtx <| do
      setMCtx p.mctx
      let (_, _, tFG) ← Meta.openAbstractMVarsResult resFG
      -- recall that `tFG = Meta.mkAppM ``Prod.mk #[mtF, mtG]`
      let args := Expr.getAppArgs tFG
      if args.size != 4 then
        trace[Meta.debug] s!"Bindings::identification::Argument number of \"Prod.mk\" is not 4"
      let tF := args[2]!
      let tG := args[3]!
      let mH := tF.getAppFn
      MVarId.assign F.mvarId! tF *> MVarId.assign G.mvarId! tG
      return {p with checked := false, mctx := ← getMCtx, identVar := p.identVar.insert mH}
    return #[s']

def elimination (F : Expr) (p : UnifProblem) : MetaM (LazyList <| MetaM (Array UnifProblem)) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescope Fty fun xs β => do
    let ctx₀ ← read
    let indsubseqs := List.lazySubsequences (List.range xs.size)
    let αs ← xs.mapM Meta.inferType
    let mut xsset := HashSet.empty
    for x in xs do
      xsset := xsset.insert x
    let nats2binding : List Nat → MetaM (Array UnifProblem) :=
    -- Restore mctx and context
    -- This action may modify mctx, so it should be run with
    --   "withoutModifyingMCtx"
    fun isub => withReader (fun _ => ctx₀) <| do
      setMCtx p.mctx
      let mut vars := #[]
      let mut tys := #[]
      for i in isub do
        vars := vars.push xs[i]!
        tys := tys.push αs[i]!
      let mvarTy ← Meta.mkForallFVars tys β
      -- If there is still dependency on variables in
      -- `xs`, then this set is invalid
      if let some _ := Expr.find? (fun x => xsset.contains x) mvarTy then
        return #[]
      let res ← (do
        let mvarTy ← Meta.mkForallFVars tys β
        let newMVar ← Meta.mkFreshExprMVar mvarTy
        let mt ← Meta.mkLambdaFVars xs (mkAppN newMVar vars)
        MVarId.assign F.mvarId! mt
        return {p with checked := false, mctx := ← getMCtx, elimVar := p.elimVar.insert newMVar})
      return #[res]
    return indsubseqs.map nats2binding