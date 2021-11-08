import Lean
import LeanHammer.ProverM

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

instance : MonadMCtx RuleM where
  getMCtx    := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

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

instance : AddMessageContext RuleM where
  addMessageContext := addMessageContextFull

def runMetaAsRuleM (x : MetaM α) : RuleM α := do
  let lctx ← getLCtx
  let mctx ← getMCtx
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) do
    x
  setMCtx state.mctx
  return res

def mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural) (userName := Name.anonymous) : RuleM Expr := do
  runMetaAsRuleM $ Meta.mkFreshExprMVar type? kind userName

def getMVarType (mvarId : MVarId) : RuleM Expr := do
  runMetaAsRuleM $ Meta.getMVarType mvarId

def forallMetaTelescope (e : Expr) (kind := MetavarKind.natural) : RuleM (Array Expr × Array BinderInfo × Expr) :=
  runMetaAsRuleM $ Meta.forallMetaTelescope e kind

def mkFreshFVar (name : Name) (type : Expr) : RuleM Expr := do
  let name := Name.mkNum name (← getLCtx).decls.size
  let (lctx, res) ← runMetaAsRuleM $ do
    Meta.withLocalDeclD name type fun x => do
      return (← getLCtx, x)
  setLCtx lctx
  return res

def mkForallFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : RuleM Expr :=
  runMetaAsRuleM $ Meta.mkForallFVars xs e usedOnly usedLetOnly

@[inline] def RuleM.runAsProverM (x : RuleM α) : ProverM.ProverM α := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx})
  ProverM.setLCtx state.lctx
  return res

-- runMetaAsRuleM do
--       trace[Prover.debug] "{cs?}"

end RuleM