import Lean
import Duper.Util.Misc
import Duper.Util.LazyList
import Duper.DUnif.UnifProblem
open Lean

-- Note:
-- 1. Rules may modify the MetaM mctx arbitrarily, so they should
--    be run with "withoutModifyingMCtx"
-- 2. MetaM actions taken out of lazy lists returned by the rules
--    may modify the MetaM mctx arbitrarily, so they should also
--    be run with "withoutModifyingMCtx"

-- TODO: Use 'withLocalDeclD'

open Duper

namespace DUnif

def withoutModifyingMCtx (x : MetaM α) : MetaM α := do
  let s ← getMCtx
  try
    x
  finally
    setMCtx s

def iteration (F : Expr) (p : UnifProblem) (eq : UnifEq) (funcArgOnly : Bool) : MetaM (LazyList <| MetaM (Array UnifProblem)) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescopeReducing Fty fun xs β₁ => (do
    let ctx₀ ← read
    let mut iterAtIFuns : Array (Nat → MetaM (Array UnifProblem)):= #[]
    let mut argnp1 := 0
    for xi in xs do
      argnp1 := argnp1 + 1
      -- Iteration at xᵢ
      let αi ← Meta.inferType xi
      -- Functional type?
      let narg := Expr.countForalls αi
      if narg == 0 ∧ funcArgOnly then
        continue
      let s₁ ← getMCtx
      -- Iteration at argument `i`
      -- Restore context and mctx
      iterAtIFuns := iterAtIFuns.push (fun i => withReader (fun _ => ctx₀) do
        setMCtx s₁
        -- `ys` is an array of free variables
        let mut ys := #[]
        -- Adding `ys` to this `lctx` along with creating them
        let mut lctx ← getLCtx
        for j in List.range i do
          let yty_ty ← Meta.mkFreshLevelMVar
          let yty ← withReader (fun ctx : Meta.Context => { ctx with lctx := lctx }) do
            Meta.mkFreshExprMVar (mkSort yty_ty)
          let fvarId ← mkFreshFVarId
          lctx := lctx.mkLocalDecl fvarId s!"iter{i}.{j}" yty .default
          let fvar := mkFVar fvarId
          ys := ys.push fvar
        -- Make Gᵢs
        let lastExpr ← withReader (fun ctx : Meta.Context => { ctx with lctx := lctx }) do
          let (xys, _, _) ← Meta.forallMetaTelescopeReducing αi
          let body := mkAppN xi xys
          Meta.mkLambdaFVars ys body
        -- Make H
        let lastExprTy ← Meta.inferType lastExpr
        -- Assuming that β₂ contains no loose bound variables
        let Hty : Expr ← Meta.withLocalDeclD s!"iter{i}.last" lastExprTy <| fun fv =>
          Meta.mkForallFVars #[fv] β₁
        let mH ← Meta.mkFreshExprMVar Hty
        let mt ← Meta.mkLambdaFVars xs (mkApp mH lastExpr)
        MVarId.assign F.mvarId! mt
        return #[{(← p.pushParentRuleIfDbgOn (.Iteration eq F (argnp1 - 1) i mt))
                   with checked := false, mctx := ← getMCtx}]
      )
      -- Get rid of metavariables in `xys`
      setMCtx p.mctx
    let iterAtIArr := iterAtIFuns.map (fun f => (LazyList.nats 0).map f)
    return LazyList.interleaveN iterAtIArr
  )

-- `F` is a metavariable
def jpProjection (F : Expr) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescopeReducing Fty fun xs β => (do
    let mut ret : Array UnifProblem := #[]
    let s₀ ← getMCtx
    let mut argnp1 := 0
    for xi in xs do
      argnp1 := argnp1 + 1
      let αi ← Meta.inferType xi
      let mut p := p
      if β != αi then
        -- We need to unify their types first
        let βabst ← Meta.mkForallFVars xs β
        let αabst ← Meta.mkForallFVars xs αi
        p := p.pushPrioritized (.fromExprPair βabst αabst)
      let t ← Meta.mkLambdaFVars xs xi
      MVarId.assign F.mvarId! t
      ret := ret.push {(← p.pushParentRuleIfDbgOn (.JPProjection eq F (argnp1 - 1) t))
                        with checked := false, mctx := ← getMCtx}
      setMCtx s₀
    return ret)

-- `F` is a metavariable
def huetProjection (F : Expr) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescopeReducing Fty fun xs β => (do
    let mut ret : Array UnifProblem := #[]
    let mut argnp1 := 0
    for xi in xs do
      argnp1 := argnp1 + 1
      let αi ← Meta.inferType xi
      -- If the result types does not match, return #[]
      -- If the result type matches, return #[binding]
      let newProblem ← withoutModifyingMCtx <| do
        let (ys, _, β') ← Meta.forallMetaTelescopeReducing αi
        let mut p := p
        if β' != β then
          -- We need to unify their types first
          let β  ← Meta.mkLambdaFVars xs β
          let β' ← Meta.mkLambdaFVars xs β'
          p := p.pushPrioritized (UnifEq.fromExprPair β β')
        -- Apply the binding to `F`
        let mF ← Meta.mkLambdaFVars xs (mkAppN xi ys)
        MVarId.assign F.mvarId! mF
        return #[{(← p.pushParentRuleIfDbgOn (.HuetProjection eq F (argnp1 - 1) mF))
                  with checked := false, mctx := ← getMCtx}]
      ret := ret.append newProblem
    return ret)

-- `F` is a metavariable
def imitForall (F : Expr) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescopeReducing Fty fun xs β => do
    -- BinderType
    let bty_ty ← Meta.mkFreshLevelMVar
    let bty ← Meta.mkFreshExprMVar (mkSort bty_ty)
    let newt ← Meta.withLocalDeclD "imf" bty fun fv => do
      let newMVar ← Meta.mkFreshExprMVar β
      Meta.mkForallFVars #[fv] newMVar
    let mt ← Meta.mkLambdaFVars xs newt
    MVarId.assign F.mvarId! mt
    return #[{(← p.pushParentRuleIfDbgOn (.ImitForall eq F mt)) with checked := false, mctx := ← getMCtx}]

-- `F` is a metavariable
def imitProj (F : Expr) (nLam : Nat) (iTy : Expr) (oTy : Expr) (name : Name) (idx : Nat) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  Meta.forallTelescopeReducing Fty fun xs β => do
    let (ys, _, β') ← Meta.forallMetaTelescopeReducing oTy
    let mut p := p
    if β' != β then
      -- We need to unify their types first
      let β  ← Meta.mkLambdaFVars xs β
      let β' ← Meta.mkLambdaFVars xs β'
      p := p.pushPrioritized (UnifEq.fromExprPair β β')
    -- Apply the binding to `F`
    let innerTy ← Meta.instantiateForall iTy (ys.extract 0 nLam)
    let innerMVar ← Meta.mkFreshExprMVar innerTy
    let projTerm := Expr.proj name idx innerMVar
    let mt ← Meta.mkLambdaFVars xs (mkAppN projTerm (ys.extract nLam ys.size))
    MVarId.assign F.mvarId! mt
    return #[{(← p.pushParentRuleIfDbgOn (.ImitProj eq F idx mt)) with checked := false, mctx := ← getMCtx}]

-- `F` is a metavariable, and `g` is a constant
def imitation (F : Expr) (g : Expr) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  let gty ← Meta.inferType g
  Meta.forallTelescopeReducing Fty fun xs β => do
    let (ys, _, β') ← Meta.forallMetaTelescopeReducing gty
    let mut p := p
    if β' != β then
      -- We need to unify their types first
      let β  ← Meta.mkLambdaFVars xs β
      let β' ← Meta.mkLambdaFVars xs β'
      p := p.pushPrioritized (UnifEq.fromExprPair β β')
    -- Apply the binding to `F`
    let mt ← Meta.mkLambdaFVars xs (mkAppN g ys)
    MVarId.assign F.mvarId! mt
    return #[{(← p.pushParentRuleIfDbgOn (.Imitation eq F g mt)) with checked := false, mctx := ← getMCtx}]

-- Both `F` and `G` are metavariables
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
def identification (F : Expr) (G : Expr) (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  setMCtx p.mctx
  let Fty ← Meta.inferType F
  let Gty ← Meta.inferType G
  -- Unify sort
  let (typeη, samesort) ← Meta.forallTelescopeReducing Fty fun xs β => Meta.forallTelescopeReducing Gty fun ys δ => do
    let sortβ ← Meta.inferType β
    let sortδ ← Meta.inferType δ
    let typeη ← Meta.mkForallFVars (xs ++ ys) sortβ
    if let .sort lβ := sortβ then
      if let .sort lδ := sortδ then
        let same ← Meta.isLevelDefEq lβ lδ
        return (typeη, same)
      else
        trace[DUnif.debug] "identification : {sortδ} is not a sort"
        return (typeη, false)
    else
      trace[DUnif.debug] "identification : {sortβ} is not a sort"
      return (typeη, false)
  if ¬ samesort then
    return #[]
  -- make η and H
  let η ← Meta.mkFreshExprMVar typeη
  let Hty ← Meta.forallTelescopeReducing Fty fun xs β => Meta.forallTelescopeReducing Gty fun ys δ => do
    let applied := mkAppN η (xs ++ ys)
    Meta.mkForallFVars (xs ++ ys) applied
  let mH ← Meta.mkFreshExprMVar Hty
  -- Binding for `F`
  let mtF ← Meta.forallTelescopeReducing Fty fun xs _ => do
    let (ys, _, _) ← Meta.forallMetaTelescopeReducing Gty
    Meta.mkLambdaFVars xs (mkAppN mH (xs ++ ys))
  -- Bindings for `G`
  let mtG ← Meta.forallTelescopeReducing Gty fun ys _ => do
    let (xs, _, _) ← Meta.forallMetaTelescopeReducing Fty
    Meta.mkLambdaFVars ys (mkAppN mH (xs ++ ys))
  -- Unify types
  let mtFty ← Meta.inferType mtF
  let feq := mtFty == Fty
  let mtGty ← Meta.inferType mtG
  let geq := mtGty == Gty
  let mut p := p
  if ¬ feq then
    p := p.pushPrioritized (UnifEq.fromExprPair mtFty Fty)
  if ¬ geq then
    p := p.pushPrioritized (UnifEq.fromExprPair mtGty Gty)
  -- Assign metavariables
  MVarId.assign F.mvarId! mtF
  MVarId.assign G.mvarId! mtG
  return #[{(← p.pushParentRuleIfDbgOn (.Identification eq F G mtF mtG))
            with checked := false, mctx := ← getMCtx, identVar := p.identVar.insert mH}]

def elimination (F : Expr) (p : UnifProblem) (eq : UnifEq) : MetaM (LazyList <| MetaM (Array UnifProblem)) := do
  setMCtx p.mctx
  let lctx₀ ← getLCtx
  let Fty ← Meta.inferType F
  Meta.forallTelescopeReducing Fty fun xs β => do
    let ctx₁ ← read
    let indsubseqs := (List.lazySubsequences (List.range xs.size)).map List.toArray
    let mut xsset := HashSet.empty
    for x in xs do
      xsset := xsset.insert x
    let nats2binding : Array Nat → MetaM (Array UnifProblem) :=
    -- Restore mctx and context
    -- This action may modify mctx, so it should be run with
    --   "withoutModifyingMCtx"
    fun isub => withReader (fun _ => ctx₁) <| do
      setMCtx p.mctx
      -- `i < n`
      if isub.size == xs.size then
        return #[]
      let mut vars := #[]
      for i in isub do
        vars := vars.push xs[i]!
      let mvarTy ← Meta.mkForallFVars vars β
      let mvarTy ← instantiateMVars mvarTy
      -- If there is still dependency on variables in
      -- `xs`, then this set is invalid
      if let some _ := Expr.find? (fun x => xsset.contains x) mvarTy then
        return #[]
      let res ← (do
        let newMVar ← Meta.mkFreshExprMVar mvarTy
        MVarId.modifyLCtx newMVar.mvarId! lctx₀
        let mt ← Meta.mkLambdaFVars xs (mkAppN newMVar vars)
        MVarId.assign F.mvarId! mt
        return {(← p.pushParentRuleIfDbgOn (.Elimination eq F isub mt))
                 with checked := false, mctx := ← getMCtx, elimVar := p.elimVar.insert newMVar})
      return #[res]
    return indsubseqs.map nats2binding