import Lean
import Duper.Util.Misc
import Duper.Util.LazyList
import Duper.HOUnif.UnifProblem
open Lean

-- TODO: Will `ListT` (Haskell "ListT done right") provide a more
-- elegant way of modelling monadic nondeterminism?

namespace HOUnif

def iteration (mvar : Expr) : MetaM (LazyList (MetaM Unit)) := do
  let ty ← Meta.inferType mvar
  sorry

-- `F` is a metavariable
def jpProjection (F : Expr) : MetaM (Array (MetaM Unit)) := do
  let Fty ← Meta.inferType F
  let ret ← Meta.forallTelescope Fty fun xs β => (do
    let mut ret : Array (MetaM Unit) := #[]
    for xi in xs do
      let αi ← Meta.inferType xi
      -- TODO 2
      if αi == β then
        let t ← Meta.mkLambdaFVars xs xi
        ret := ret.push (MVarId.assign F.mvarId! t)
    return ret)
  return ret

-- `F` is a metavariable
def huetProjection (F : Expr) : MetaM (Array (MetaM Unit)) := do
  let Fty ← Meta.inferType F
  Meta.forallTelescope Fty fun xs β => (do
    let mut ret : Array (MetaM Unit) := #[]
    for xi in xs do
      let αi ← Meta.inferType xi
      -- If the result types does not match, return #[]
      -- If the result type matches, return #[binding]
      let binding ← withoutModifyingState <| Meta.withNewMCtxDepth <| do
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
        return #[do
          let (_, _, t) ← Meta.openAbstractMVarsResult res
          MVarId.assign F.mvarId! t]
      ret := ret.append binding
    return ret)

-- `F` is a metavariable, and `g` is a rigid symbol
def imitation (F : Expr) (g : Expr) : MetaM (Array (MetaM Unit)) := do
  let Fty ← Meta.inferType F
  let gty ← Meta.inferType g
  let ret ← Meta.forallTelescope Fty fun xs β => 
  withoutModifyingState <| Meta.withNewMCtxDepth <| do
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
    return #[do
      let (_, _, t) ← Meta.openAbstractMVarsResult res
      MVarId.assign F.mvarId! t]
  return ret

-- Both `F` and `G` are metavariables
def identification (F : Expr) (G : Expr) : MetaM (Array (MetaM Unit)) := do
  let Fty ← Meta.inferType F
  let Gty ← Meta.inferType G
  let ret ← Meta.forallTelescope Fty fun xs β =>
  withoutModifyingState <| Meta.withNewMCtxDepth <| do
    let (ys, _, β') ← Meta.forallMetaTelescope Gty
    -- TODO 2
    if β' != β then
      return #[]
    -- Type of `H`
    let Hty ← Meta.mkForallFVars (xs ++ ys) β
    let H ← Meta.mkFreshExprMVar Hty
    -- Binding for `F`
    let mut appargs := #[]
    for xi in xs do
      appargs := appargs.push xi
    for yi in ys do
      let γi ← Meta.inferType yi
      let mvarTy ← Meta.mkForallFVars xs γi
      let newMVar ← Meta.mkFreshExprMVar mvarTy
      MVarId.assign yi.mvarId! newMVar
      appargs := appargs.push (mkAppN newMVar xs)
    let mtF ← Meta.mkLambdaFVars xs (mkAppN H appargs)
    let resF ← Meta.abstractMVars mtF
    -- Bindings for `G`
    appargs := #[]
    for xi in xs do
      let αi ← Meta.inferType xi
      let mvarTy ← Meta.mkForallFVars ys αi
      let newMVar ← Meta.mkFreshExprMVar mvarTy
      MVarId.assign xi.mvarId! newMVar
      appargs := appargs.push (mkAppN newMVar ys)
    for yi in ys do
      appargs := appargs.push yi
    let mtG ← Meta.mkLambdaFVars ys (mkAppN H appargs)
    let resG ← Meta.abstractMVars mtG
    return #[do
      let (_, _, tF) ← Meta.openAbstractMVarsResult resF
      let (_, _, tG) ← Meta.openAbstractMVarsResult resG
      MVarId.assign F.mvarId! tF *> MVarId.assign G.mvarId! tG]
  return ret

def elimination (F : Expr) : MetaM (Array (MetaM Unit)) := do
  let Fty ← Meta.inferType F
  let ret ← Meta.forallTelescope Fty fun xs β => do
    let indsubseqs := List.subsequences (List.range xs.size)
    let αs ← xs.mapM Meta.inferType
    for isub in indsubseqs do
      let mut vars := #[]
      let mut tys := #[]
      for i in isub do
        vars := vars.push xs[i]!
        tys := tys.push αs[i]!
      let mvarTy ← Meta.mkForallFVars tys β
      let newMVar ← Meta.mkFreshExprMVar mvarTy
    sorry
  return ret