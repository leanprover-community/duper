import Duper.Clause
import Std.Data.BinomialHeap
import Duper.DiscrTree
import Duper.Selection

namespace Duper
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
abbrev ClauseHeap := BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1
abbrev ClauseDiscrTree α := Duper.DiscrTree (Clause × α)

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
  passiveSetAgeHeap : ClauseHeap := BinomialHeap.empty
  passiveSetWeightHeap : ClauseHeap := BinomialHeap.empty
  fairnessCounter : Nat := 0
  mainPremiseIdx : ClauseDiscrTree ClausePos := {}
  supSidePremiseIdx : ClauseDiscrTree ClausePos := {}
  demodSidePremiseIdx : ClauseDiscrTree ClausePos := {}
  lctx : LocalContext := {}
  mctx : MetavarContext := {}

abbrev ProverM := ReaderT Context $ StateRefT State CoreM

instance : MonadLCtx ProverM where
  getLCtx := return (← get).lctx

instance : MonadMCtx ProverM where
  getMCtx    := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

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
  registerTraceClass `Prover.saturate
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

def getPassiveSetAgeHeap : ProverM ClauseHeap :=
  return (← get).passiveSetAgeHeap

def getPassiveSetWeightHeap : ProverM ClauseHeap :=
  return (← get).passiveSetWeightHeap

def getFairnessCounter : ProverM Nat :=
  return (← get).fairnessCounter

def getMainPremiseIdx : ProverM (ClauseDiscrTree ClausePos) :=
  return (← get).mainPremiseIdx

def getSupSidePremiseIdx : ProverM (ClauseDiscrTree ClausePos) :=
  return (← get).supSidePremiseIdx

def getDemodSidePremiseIdx : ProverM (ClauseDiscrTree ClausePos) :=
  return (← get).demodSidePremiseIdx

def getClauseInfo! (c : Clause) : ProverM ClauseInfo := do
  let some ci := (← getAllClauses).find? c
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

def setPassiveSetAgeHeap (passiveSetAgeHeap : ClauseHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetAgeHeap := passiveSetAgeHeap }

def setPassiveSetWeightHeap (passiveSetWeightHeap : ClauseHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetWeightHeap := passiveSetWeightHeap }

def setFairnessCounter (fairnessCounter : Nat) : ProverM Unit :=
  modify fun s => { s with fairnessCounter := fairnessCounter }

def setSupSidePremiseIdx (supSidePremiseIdx : (ClauseDiscrTree ClausePos)) : ProverM Unit :=
  modify fun s => { s with supSidePremiseIdx := supSidePremiseIdx }

def setDemodSidePremiseIdx (demodSidePremiseIdx : (ClauseDiscrTree ClausePos)) : ProverM Unit :=
  modify fun s => { s with demodSidePremiseIdx := demodSidePremiseIdx }

def setMainPremiseIdx (mainPremiseIdx : (ClauseDiscrTree ClausePos)) : ProverM Unit :=
  modify fun s => { s with mainPremiseIdx := mainPremiseIdx }

def setLCtx (lctx : LocalContext) : ProverM Unit :=
  modify fun s => { s with lctx := lctx }

def setMCtx (mctx : MetavarContext) : ProverM Unit :=
  modify fun s => { s with mctx := mctx }

initialize emptyClauseExceptionId : InternalExceptionId ← registerInternalExceptionId `emptyClause

def throwEmptyClauseException : ProverM α :=
  throw <| Exception.internal emptyClauseExceptionId

partial def chooseGivenClause : ProverM (Option Clause) := do
  Core.checkMaxHeartbeats "chooseGivenClause"
  -- Decide which heap to choose from
  let fc ← getFairnessCounter
  let (getHeap, setHeap) ←
    if fc ≥ 5 then
      setFairnessCounter 0
      trace[Prover.debug] "Clause selected by age ({fc})"
      pure (getPassiveSetAgeHeap, setPassiveSetAgeHeap)
    else
      trace[Prover.debug] "Clause selected by weight ({fc})"
      pure (getPassiveSetWeightHeap, setPassiveSetWeightHeap)
  -- Extract clause from heap
  let some (c, h) := (← getHeap).deleteMin
    | return none
  setHeap h
  -- If selected clause is no longer in passive set, restart.
  if not $ (← getPassiveSet).contains c.2 then
    return (← chooseGivenClause)
  -- Remove clause from passive
  setPassiveSet $ (← getPassiveSet).erase c.2
  -- Increase fairness counter
  setFairnessCounter (fc + 1)
  return c.2

/-- Registers a new clause, but does not add it to active or passive set.
  Typically, you'll want to use `addNewToPassive` instead. -/
def addNewClause (c : Clause) (proof : Proof) : ProverM ClauseInfo := do
  match (← getAllClauses).find? c with
  | some ci => return ci
  | none =>
    let allClauses := (← get).allClauses
    let ci : ClauseInfo := {
      number := allClauses.size
      proof := proof
    }
    setAllClauses (allClauses.insert c ci)
    if c.lits.size == 0 then throwEmptyClauseException
    return ci

def addNewToPassive (c : Clause) (proof : Proof) : ProverM Unit := do
  if (← getAllClauses).contains c
  then pure () -- clause is not new, ignore.
  else
    trace[Prover.saturate] "New passive clause: {c}"
    let ci ← addNewClause c proof
    setPassiveSet $ (← getPassiveSet).insert c
    setPassiveSetAgeHeap $ (← getPassiveSetAgeHeap).insert (ci.number, c)
    setPassiveSetWeightHeap $ (← getPassiveSetWeightHeap).insert (c.weight, c)

def addExprAssumptionToPassive (e : Expr) (proof : Expr) : ProverM Unit := do
  let c := Clause.fromExpr e
  -- TODO: remove sorry
  let mkProof := fun _ _ _ => pure proof
  addNewToPassive c {ruleName := "assumption", mkProof := mkProof}
  
def ProverM.runWithExprs (x : ProverM α) (es : Array (Expr × Expr)) (ctx : Context := {}) (s : State := {}) : 
    CoreM (α × State) := do
  ProverM.run (s := s) (ctx := ctx) do
    for (e, proof) in es do
      addExprAssumptionToPassive e proof
    x

@[inline] def runRuleM (x : RuleM α) : ProverM.ProverM α := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx, mctx := ← getMCtx})
  ProverM.setLCtx state.lctx
  ProverM.setMCtx state.mctx
  return res

@[inline] def runInferenceRule (x : RuleM Unit) : ProverM.ProverM (Array (Clause × Proof)) := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx, mctx := ← getMCtx})
  ProverM.setLCtx state.lctx
  return state.resultClauses

@[inline] def runSimpRule (x : RuleM α) : 
    ProverM.ProverM (α × Array (Clause × Proof)) := do
  let (res, state) ← RuleM.run x (s := {lctx := ← getLCtx, mctx := ← getMCtx})
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
  -- Add to superposition's side premise index:
  let idx ← getSupSidePremiseIdx
  let idx ← runRuleM do
    let (mvars, mclause) ← loadClauseCore c
    mclause.foldM
      fun idx e pos => do
        if mclause.lits[pos.lit].sign ∧ litSelectedOrNothingSelected mclause pos.lit
        then return ← idx.insert e (c, pos)
        else return idx
      idx
  setSupSidePremiseIdx idx
  -- Add to demodulation's side premise index iff c consists of exactly one positive literal:
  if(c.lits.size = 1 && c.lits[0].sign) then
    let idx ← getDemodSidePremiseIdx
    let idx ← runRuleM do
      let (mvars, mclause) ← loadClauseCore c
      mclause.foldM (fun idx e pos => idx.insert e (c, pos)) idx
    setDemodSidePremiseIdx idx
  -- Add to main premise index:
  let idx ← getMainPremiseIdx
  let idx ← runRuleM do
    let (mvars, mclause) ← loadClauseCore c
    mclause.foldGreenM
      fun idx e pos => do
        if e.isMVar
        then return idx
        else return ← idx.insert e (c, pos)
      idx
  setMainPremiseIdx idx
  -- add to active set:
  setActiveSet $ (← getActiveSet).insert c

/-- Remove c from mainPremiseIdx, supSidePremiseIdx, and demodSidePremiseIdx -/
def removeFromDiscriminationTrees (c : Clause) : ProverM Unit := do
  let mainIdx ← getMainPremiseIdx
  let supSideIdx ← getSupSidePremiseIdx
  let demodSideIdx ← getDemodSidePremiseIdx
  setMainPremiseIdx (← runRuleM $ mainIdx.delete c)
  setSupSidePremiseIdx (← runRuleM $ supSideIdx.delete c)
  setDemodSidePremiseIdx (← runRuleM $ demodSideIdx.delete c)

/-- Remove c from the active set and from all of the state's discrimination trees-/
def removeFromActive (c : Clause) : ProverM Unit := do
  let activeSet ← getActiveSet
  if activeSet.contains c then
    setActiveSet $ activeSet.erase c
    removeFromDiscriminationTrees c

def mkFreshFVarId (ty : Expr): ProverM FVarId := do
  let lctx ← getLCtx
  let n := lctx.decls.size
  let name := Name.mkNum `c n
  let fVarId := ⟨name⟩
  setLCtx $ LocalContext.mkLocalDecl lctx fVarId name ty
  return fVarId

end ProverM
end Duper
