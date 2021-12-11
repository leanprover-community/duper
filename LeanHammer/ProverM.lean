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

structure ClauseInfo where
(number : Nat)

abbrev ClauseSet := HashMap Clause ClauseInfo
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
  allClauses : ClauseSet := {}
  activeSet : ClauseSet := {}
  passiveSet : ClauseSet := {}
  passiveSetHeap : ClauseAgeHeap := BinomialHeap.empty
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

def getAllClauses : ProverM ClauseSet :=
  return (← get).allClauses

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

def setAllClauses (allClauses : ClauseSet) : ProverM Unit :=
  modify fun s => { s with allClauses := allClauses }

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

/-- Registers a new clause, but does not add it to active or passive set.
  Typically, you'll want to use `addNewToPassive` instead. -/
def addNewClause (c : Clause) : ProverM ClauseInfo := do
  if c.lits.size == 0 then throwEmptyClauseException
  let allClauses ← (← get).allClauses
  let ci : ClauseInfo := {
    number := allClauses.size
  }
  setAllClauses (allClauses.insert c ci)
  return ci

def addNewToPassive (c : Clause) : ProverM Unit := do
  if (← getAllClauses).contains c
  then () -- clause is not new, ignore.
  else
    let ci ← addNewClause c
    setPassiveSet $ (← getPassiveSet).insert c ci
    setPassiveSetHeap $ (← getPassiveSetHeap).insert (ci.number, c)

def addNewExprToPassive (e : Expr) : ProverM Unit := do
  addNewToPassive (Clause.fromExpr e)
  
def ProverM.runWithExprs (x : ProverM α) (es : Array Expr) : CoreM α := do
  ProverM.run' do
    for e in es do
      addNewExprToPassive e
    x

def addToActive (c : Clause) : ProverM Unit := do
  let ci ← 
    match (← getAllClauses).find? c with
    | some ci => ci
    | none => addNewClause c
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
  setActiveSet $ (← getActiveSet).insert c ci

def mkFreshFVarId (ty : Expr): ProverM FVarId := do
  let lctx ← getLCtx
  let n := lctx.decls.size
  let name := Name.mkNum `c n
  let fVarId := ⟨name⟩
  setLCtx $ LocalContext.mkLocalDecl lctx fVarId name ty
  return fVarId

end ProverM

