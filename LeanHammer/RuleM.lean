import Lean

namespace RuleM
open Lean
open Lean.Core

structure Context where
  blah : Bool := false
deriving Inhabited

structure State where
  mctx : MetavarContext := {}
  lctx : LocalContext := {}
deriving Inhabited

abbrev RuleM := ReaderT Context $ StateRefT State CoreM

instance : Monad RuleM := let i := inferInstanceAs (Monad RuleM); { pure := i.pure, bind := i.bind }

instance : MonadLCtx RuleM where
  getLCtx := return (← get).lctx

instance : Inhabited (RuleM α) where
  default := fun _ _ => arbitrary

@[inline] def RuleM.run (x : RuleM α) (ctx : Context := {}) (s : State := {}) : CoreM (α × State) :=
  x ctx |>.run s

@[inline] def RuleM.run' (x : RuleM α) (ctx : Context := {}) (s : State := {}) : CoreM α :=
  Prod.fst <$> x.run ctx s

@[inline] def RuleM.toIO (x : RuleM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context := {}) (s : State := {}) : IO (α × Core.State × State) := do
  let ((a, s), sCore) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, sCore, s)

instance [MetaEval α] : MetaEval (RuleM α) :=
  ⟨fun env opts x _ => MetaEval.eval env opts x.run' true⟩

def getBlah : RuleM Bool :=
  return (← read).blah

def getMCtx : RuleM MetavarContext :=
  return (← get).mctx

def setMCtx (mctx : MetavarContext) : RuleM Unit :=
  modify fun s => { s with mctx := mctx }

def setLCtx (lctx : LocalContext) : RuleM Unit :=
  modify fun s => { s with lctx := lctx }

def mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural) (userName := Name.anonymous) : RuleM Expr := do
  let lctx ← getLCtx
  let mctx ← getMCtx
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) do
    Meta.mkFreshExprMVar type? kind userName
  setMCtx state.mctx
  return res

def getMVarType (mvarId : MVarId) : RuleM Expr := do
  let lctx ← getLCtx
  let mctx ← getMCtx
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) do
    Meta.getMVarType mvarId
  setMCtx state.mctx
  return res



#check Meta.getMVarType

end RuleM