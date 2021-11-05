import LeanHammer.Clause
import Std.Data.BinomialHeap

namespace Prover
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
abbrev ClauseAgeHeap := BinomialHeap Clause fun c d => c.id ≤ d.id

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
  nextClauseId : Nat := 0

abbrev ProverM := ReaderT Context $ StateRefT State CoreM

instance : Monad ProverM := let i := inferInstanceAs (Monad ProverM); { pure := i.pure, bind := i.bind }

instance : Inhabited (ProverM α) where
  default := fun _ _ => arbitrary

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

def setResult (result : Result) : ProverM Unit :=
  modify fun s => { s with result := result }

def getResult : ProverM Result :=
  return (← get).result

def getActiveSet : ProverM ClauseSet :=
  return (← get).activeSet

def getPassiveSet : ProverM ClauseSet :=
  return (← get).passiveSet

def chooseGivenClause : ProverM (Option Clause) := do
  let some (c, h) ← (← get).passiveSetHeap.deleteMin
    | return none
  modify fun s => { s with passiveSetHeap := h }
  return c

initialize emptyClauseExceptionId : InternalExceptionId ← registerInternalExceptionId `emptyClause