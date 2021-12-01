import LeanHammer.Clause
import Std.Data.BinomialHeap
import LeanHammer.DiscrTree
import LeanHammer.MClause

namespace ProverM
open Lean
open Lean.Core
open Std
open RuleM

inductive Result :=
| unknown
| saturated
| contradiction
  deriving Inhabited

open Result

abbrev ClauseSet := HashSet Clause
abbrev ClauseAgeHeap := BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1
abbrev ClauseDiscrTree := Schroedinger.DiscrTree (Clause × Expr)

instance : ToMessageData Result := 
⟨fun r => match r with
| unknown => "unknown"
| saturated => "saturated"
| contradiction => "contradiction"⟩

structure Context where
  blah : Bool := false
deriving Inhabited

structure State where
  result : Result := unknown
  activeSet : ClauseSet := {}
  passiveSet : ClauseSet := {}
  passiveSetHeap : ClauseAgeHeap := BinomialHeap.empty
  clauseAge : HashMap Clause Nat := {}
  supMainPremiseIdx : ClauseDiscrTree := {}
  supSidePremiseIdx : ClauseDiscrTree := {}
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

def getSupMainPremiseIdx : ProverM ClauseDiscrTree :=
  return (← get).supMainPremiseIdx

def getSupSidePremiseIdx : ProverM ClauseDiscrTree :=
  return (← get).supSidePremiseIdx

def setResult (result : Result) : ProverM Unit :=
  modify fun s => { s with result := result }

def setActiveSet (activeSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with activeSet := activeSet }

def setPassiveSet (passiveSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with passiveSet := passiveSet }

def setPassiveSetHeap (passiveSetHeap : ClauseAgeHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetHeap := passiveSetHeap }

def setSupSidePremiseIdx (supSidePremiseIdx : ClauseDiscrTree) : ProverM Unit :=
  modify fun s => { s with supSidePremiseIdx := supSidePremiseIdx }

def setSupMainPremiseIdx (supMainPremiseIdx : ClauseDiscrTree) : ProverM Unit :=
  modify fun s => { s with supMainPremiseIdx := supMainPremiseIdx }

def setLCtx (lctx : LocalContext) : ProverM Unit :=
  modify fun s => { s with lctx := lctx }

@[inline] def runRuleM (x : RuleM α) : ProverM.ProverM α := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx})
  ProverM.setLCtx state.lctx
  return res

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
  if c.lits.size == 0 then throwEmptyClauseException
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
  --TODO: use event listeners for this?
  -- Add to side premise index:
  let idx ← getSupSidePremiseIdx
  let idx ← runRuleM do
    let (mvars, mclause) ← MClause.fromClauseCore c
    mclause.foldM
      fun idx e => do
        return ← idx.insert e (c, ← e.abstractMVars mvars)
      idx
  setSupSidePremiseIdx idx
  -- Add to side premise index:
  let idx ← getSupMainPremiseIdx
  let idx ← runRuleM do
    let (mvars, mclause) ← MClause.fromClauseCore c
    mclause.foldM -- TODO visit subterms
      fun idx e => do
        return ← idx.insert e (c, ← e.abstractMVars mvars)
      idx
  setSupMainPremiseIdx idx
  -- add to active set:
  setActiveSet $ (← getActiveSet).insert c

def mkFreshFVarId (ty : Expr): ProverM FVarId := do
  let lctx ← getLCtx
  let n := lctx.decls.size
  let name := Name.mkNum `c n
  let fVarId := ⟨name⟩
  setLCtx $ LocalContext.mkLocalDecl lctx fVarId name ty
  return fVarId

end ProverM

