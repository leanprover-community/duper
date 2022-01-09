import LeanHammer.Clause
import Std.Data.BinomialHeap
import LeanHammer.DiscrTree
import LeanHammer.MClause

namespace Schroedinger
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
(proof : Proof)

abbrev ClauseSet := HashSet Clause 
abbrev ClauseAgeHeap := BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1
abbrev ClauseDiscrTree α := Schroedinger.DiscrTree (Clause × α)

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
  allClauses : HashMap Clause ClauseInfo := {}
  activeSet : ClauseSet := {} --TODO: put clause into only in allClauses?
  passiveSet : ClauseSet := {}
  passiveSetHeap : ClauseAgeHeap := BinomialHeap.empty
  supMainPremiseIdx : ClauseDiscrTree ClausePos := {}
  supSidePremiseIdx : ClauseDiscrTree ClausePos := {}
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

def getAllClauses : ProverM (HashMap Clause ClauseInfo) :=
  return (← get).allClauses

def getActiveSet : ProverM ClauseSet :=
  return (← get).activeSet

def getPassiveSet : ProverM ClauseSet :=
  return (← get).passiveSet

def getPassiveSetHeap : ProverM ClauseAgeHeap :=
  return (← get).passiveSetHeap

def getSupMainPremiseIdx : ProverM (ClauseDiscrTree ClausePos) :=
  return (← get).supMainPremiseIdx

def getSupSidePremiseIdx : ProverM (ClauseDiscrTree ClausePos) :=
  return (← get).supSidePremiseIdx

def getClauseInfo! (c : Clause) : ProverM ClauseInfo := do
  let some ci ← (← getAllClauses).find? c
    | throwError "Clause not found: {c}"
  return ci

def setResult (result : Result) : ProverM Unit :=
  modify fun s => { s with result := result }

def setActiveSet (activeSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with activeSet := activeSet }

def setAllClauses (allClauses : HashMap Clause ClauseInfo) : ProverM Unit :=
  modify fun s => { s with allClauses := allClauses }

def setPassiveSet (passiveSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with passiveSet := passiveSet }

def setPassiveSetHeap (passiveSetHeap : ClauseAgeHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetHeap := passiveSetHeap }

def setSupSidePremiseIdx (supSidePremiseIdx : (ClauseDiscrTree ClausePos)) : ProverM Unit :=
  modify fun s => { s with supSidePremiseIdx := supSidePremiseIdx }

def setSupMainPremiseIdx (supMainPremiseIdx : (ClauseDiscrTree ClausePos)) : ProverM Unit :=
  modify fun s => { s with supMainPremiseIdx := supMainPremiseIdx }

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

/-- Registers a new clause, but does not add it to active or passive set.
  Typically, you'll want to use `addNewToPassive` instead. -/
def addNewClause (c : Clause) (proof : Proof) : ProverM ClauseInfo := do
  let allClauses ← (← get).allClauses
  let ci : ClauseInfo := {
    number := allClauses.size
    proof := proof
  }
  setAllClauses (allClauses.insert c ci)
  if c.lits.size == 0 then throwEmptyClauseException
  return ci

def addNewToPassive (c : Clause) (proof : Proof) : ProverM Unit := do
  if (← getAllClauses).contains c
  then () -- clause is not new, ignore.
  else
    let ci ← addNewClause c proof
    setPassiveSet $ (← getPassiveSet).insert c
    setPassiveSetHeap $ (← getPassiveSetHeap).insert (ci.number, c)

def addExprAssumptionToPassive (e : Expr) : ProverM Unit := do
  addNewToPassive (Clause.fromExpr e) {ruleName := "assumption"}
  
def ProverM.runWithExprs (x : ProverM α) (es : Array Expr) (ctx : Context := {}) (s : State := {}) : 
    CoreM (α × State) := do
  ProverM.run (s := s) (ctx := ctx) do
    for e in es do
      addExprAssumptionToPassive e
    x

@[inline] def runRuleM (x : RuleM α) : ProverM.ProverM α := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx})
  ProverM.setLCtx state.lctx
  return res

@[inline] def runInferenceRule (x : RuleM Unit) : ProverM.ProverM (Array (Clause × Proof)) := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx})
  ProverM.setLCtx state.lctx
  return state.resultClauses

@[inline] def runSimpRule (x : RuleM α) : 
    ProverM.ProverM (α × Array (Clause × Proof)) := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx})
  ProverM.setLCtx state.lctx
  return (res, state.resultClauses)

def performInference (rule : MClause → RuleM Unit) (c : Clause) : ProverM Unit := do
  let cs ← runInferenceRule do
    let c ← loadClause c
    rule c
  for (c, proof) in cs do
    addNewToPassive c proof

def addToActive (c : Clause) : ProverM Unit := do
  let ci ← getClauseInfo! c
  --TODO: use event listeners for this?
  -- Add to side premise index:
  let idx ← getSupSidePremiseIdx
  let idx ← runRuleM do
    let (mvars, mclause) ← loadClauseCore c
    mclause.foldM
      fun idx e pos => do
        if mclause.lits[pos.lit].sign
        then return ← idx.insert e (c, pos)
        else return idx
      idx
  setSupSidePremiseIdx idx
  -- Add to side premise index:
  let idx ← getSupMainPremiseIdx
  let idx ← runRuleM do
    let (mvars, mclause) ← loadClauseCore c
    mclause.foldGreenM
      fun idx e pos => do
        if e.isMVar
        then return idx
        else return ← idx.insert e (c, pos)
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
end Schroedinger
