import LeanHammer.Clause
import Std.Data.BinomialHeap

namespace ProverM
open Lean
open Lean.Core
open Std

inductive Result :=
| unknown
| saturated
| contadiction
  deriving Inhabited

open Result

abbrev ClauseSet := HashSet Clause
abbrev ClauseAgeHeap := BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1

instance : ToMessageData Result := 
⟨fun r => match r with
| unknown => "unknown"
| saturated => "saturated"
| contadiction => "contadiction"⟩

structure Context where
  blah : Bool := false
deriving Inhabited

structure State where
  result : Result := unknown
  activeSet : ClauseSet := {}
  passiveSet : ClauseSet := {}
  passiveSetHeap : ClauseAgeHeap := BinomialHeap.empty
  clauseAge : HashMap Clause Nat := {}
  lctx : LocalContext := {}

abbrev ProverM := ReaderT Context $ StateRefT State CoreM

instance : Monad ProverM := let i := inferInstanceAs (Monad ProverM); { pure := i.pure, bind := i.bind }

instance : MonadLCtx ProverM where
  getLCtx := return (← get).lctx

instance : Inhabited (ProverM α) where
  default := fun _ _ => arbitrary

instance : AddMessageContext ProverM where
  addMessageContext := fun msgData => do
    let env ← getEnv
    let lctx ← getLCtx
    let opts ← getOptions
    pure $ MessageData.withContext { env := env, mctx := {}, lctx := lctx, opts := opts } msgData

@[inline] def ProverM.run (x : ProverM α) (ctx : Context := {}) (s : State := {}) : CoreM (α × State) :=
  x ctx |>.run s

@[inline] def ProverM.run' (x : ProverM α) (ctx : Context := {}) (s : State := {}) : CoreM α :=
  Prod.fst <$> x.run ctx s

@[inline] def ProverM.toIO (x : ProverM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context := {}) (s : State := {}) : IO (α × Core.State × State) := do
  let ((a, s), sCore) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, sCore, s)

instance [MetaEval α] : MetaEval (ProverM α) :=
  ⟨fun env opts x _ => MetaEval.eval env opts x.run' true⟩

initialize
  registerTraceClass `Prover
  registerTraceClass `Prover.debug

def getBlah : ProverM Bool :=
  return (← read).blah

def getResult : ProverM Result :=
  return (← get).result

def getActiveSet : ProverM ClauseSet :=
  return (← get).activeSet

def getPassiveSet : ProverM ClauseSet :=
  return (← get).passiveSet

def getPassiveSetHeap : ProverM ClauseAgeHeap :=
  return (← get).passiveSetHeap

def setResult (result : Result) : ProverM Unit :=
  modify fun s => { s with result := result }

def setActiveSet (activeSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with activeSet := activeSet }

def setPassiveSet (passiveSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with passiveSet := passiveSet }

def setPassiveSetHeap (passiveSetHeap : ClauseAgeHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetHeap := passiveSetHeap }

def setLCtx (lctx : LocalContext) : ProverM Unit :=
  modify fun s => { s with lctx := lctx }

initialize emptyClauseExceptionId : InternalExceptionId ← registerInternalExceptionId `emptyClause

def throwEmptyClauseException : ProverM α :=
  throw <| Exception.internal emptyClauseExceptionId

def chooseGivenClause : ProverM (Option Clause) := do
  let some (c, h) ← (← getPassiveSetHeap).deleteMin
    | return none
  setPassiveSetHeap h
  -- TODO: Check if formula hasn't been removed from PassiveSet already
  -- Then we need to choose a different one.
  setPassiveSet $ (← getPassiveSet).erase c.2
  return c.2

def addToPassive (c : Clause) : ProverM Unit := do
  let clauseAgeMap := (← get).clauseAge
  let clauseAge : Nat ← match clauseAgeMap.find? c with
  | none => do
    let age := clauseAgeMap.size
    modify fun s => { s with clauseAge := clauseAgeMap.insert c age }
    age
  | some age => age
  setPassiveSet $ (← getPassiveSet).insert c
  setPassiveSetHeap $ (← getPassiveSetHeap).insert (clauseAge, c)
  

def addExprToPassive (e : Expr) : ProverM Unit := do
  addToPassive (Clause.fromExpr e)
  
def ProverM.runWithExprs (x : ProverM α) (es : Array Expr) : CoreM α := do
  ProverM.run' do
    for e in es do
      addExprToPassive e
    x

def addToActive (c : Clause) : ProverM Unit := do
  setActiveSet $ (← getActiveSet).insert c

def mkFreshFVarId (ty : Expr): ProverM FVarId := do
  let lctx ← getLCtx
  let n := lctx.decls.size
  let name := Name.mkNum `c n
  let fVarId := ⟨name⟩
  setLCtx $ LocalContext.mkLocalDecl lctx fVarId name ty
  return fVarId

end ProverM