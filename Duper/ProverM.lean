import Duper.Clause
import Std.Data.BinomialHeap
import Duper.Fingerprint
import Duper.Selection
import Duper.SubsumptionTrie
import Duper.Util.ClauseSubsumptionCheck

namespace Duper
namespace ProverM
open Lean
open Lean.Core
open Std
open RuleM
open Expr

initialize
  registerTraceClass `RemoveClause.debug
  registerTraceClass `ImmediateSimplification.debug

inductive Result :=
| unknown
| saturated
| contradiction
  deriving Inhabited

open Result

structure ClauseInfo where
(number : Nat)
(proof : Proof)
(generatingAncestors : List Clause)
(descendants : List Clause)
(wasSimplified : Bool)
(isOrphan : Bool)

abbrev ClauseSet := HashSet Clause 
abbrev ClauseHeap := BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1

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
  symbolPrecMap : SymbolPrecMap := HashMap.empty
  highesetPrecSymbolHasArityZero : Bool := false
  passiveSetAgeHeap : ClauseHeap := BinomialHeap.empty
  passiveSetWeightHeap : ClauseHeap := BinomialHeap.empty
  fairnessCounter : Nat := 0
  mainPremiseIdx : RootCFPTrie := {}
  supSidePremiseIdx : RootCFPTrie := {}
  demodSidePremiseIdx : RootCFPTrie := {}
  subsumptionTrie : SubsumptionTrie := SubsumptionTrie.emptyNode
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

@[inline] def ProverM.toIO (x : ProverM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context := {}) (s : State := {}) :
  IO (α × Core.State × State) := do
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

def getSymbolPrecMap : ProverM SymbolPrecMap :=
  return (← get).symbolPrecMap

def getHighesetPrecSymbolHasArityZero : ProverM Bool :=
  return (← get).highesetPrecSymbolHasArityZero

def getPassiveSetAgeHeap : ProverM ClauseHeap :=
  return (← get).passiveSetAgeHeap

def getPassiveSetWeightHeap : ProverM ClauseHeap :=
  return (← get).passiveSetWeightHeap

def getFairnessCounter : ProverM Nat :=
  return (← get).fairnessCounter

def getMainPremiseIdx : ProverM RootCFPTrie :=
  return (← get).mainPremiseIdx

def getSupSidePremiseIdx : ProverM RootCFPTrie :=
  return (← get).supSidePremiseIdx

def getDemodSidePremiseIdx : ProverM RootCFPTrie :=
  return (← get).demodSidePremiseIdx

def getSubsumptionTrie : ProverM SubsumptionTrie :=
  return (← get).subsumptionTrie

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

def setSymbolPrecMap (symbolPrecMap : SymbolPrecMap) : ProverM Unit :=
  modify fun s => { s with symbolPrecMap := symbolPrecMap }

def setHighesetPrecSymbolHasArityZero (highesetPrecSymbolHasArityZero : Bool) : ProverM Unit :=
  modify fun s => { s with highesetPrecSymbolHasArityZero := highesetPrecSymbolHasArityZero }

def setPassiveSetAgeHeap (passiveSetAgeHeap : ClauseHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetAgeHeap := passiveSetAgeHeap }

def setPassiveSetWeightHeap (passiveSetWeightHeap : ClauseHeap) : ProverM Unit :=
  modify fun s => { s with passiveSetWeightHeap := passiveSetWeightHeap }

def setFairnessCounter (fairnessCounter : Nat) : ProverM Unit :=
  modify fun s => { s with fairnessCounter := fairnessCounter }

def setSupSidePremiseIdx (supSidePremiseIdx : RootCFPTrie) : ProverM Unit :=
  modify fun s => { s with supSidePremiseIdx := supSidePremiseIdx }

def setDemodSidePremiseIdx (demodSidePremiseIdx : RootCFPTrie) : ProverM Unit :=
  modify fun s => { s with demodSidePremiseIdx := demodSidePremiseIdx }

def setMainPremiseIdx (mainPremiseIdx : RootCFPTrie) : ProverM Unit :=
  modify fun s => { s with mainPremiseIdx := mainPremiseIdx }

def setSubsumptionTrie (subsumptionTrie : SubsumptionTrie) : ProverM Unit :=
  modify fun s => { s with subsumptionTrie := subsumptionTrie }

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
    trace[Prover.debug] "Clause {c.2} no longer in passive set, choosing new clause"
    return (← chooseGivenClause)
  -- Remove clause from passive
  setPassiveSet $ (← getPassiveSet).erase c.2
  -- Increase fairness counter
  setFairnessCounter (fc + 1)
  return c.2

/-- Given a clause c and a list of ancestors, markAsDescendantToGeneratingAncestors adds c to each generating ancestor's list of descendants -/
def markAsDescendantToGeneratingAncestors (c : Clause) (generatingAncestors : List Clause) : ProverM Unit := do
  let mut allClauses ← getAllClauses
  for ancestor in generatingAncestors do
    match allClauses.find? ancestor with
    | some ancestorInfo =>
      let descendantList := ancestorInfo.descendants
      let ancestorInfo := {ancestorInfo with descendants := c :: descendantList}
      setAllClauses $ allClauses.insert ancestor ancestorInfo
      allClauses ← getAllClauses
    | none => throwError "Unable to find ancestor"

/-- Registers a new clause, but does not add it to active or passive set.
    Typically, you'll want to use `addNewToPassive` instead. -/
def addNewClause (c : Clause) (proof : Proof) (generatingAncestors : List Clause) : ProverM ClauseInfo := do
  markAsDescendantToGeneratingAncestors c generatingAncestors
  match (← getAllClauses).find? c with
  | some ci =>
    if ci.isOrphan then
      -- Update c's generating ancestors and orphan status because it has been added to the passiveSet by new ancestors
      let ci := {ci with generatingAncestors := generatingAncestors, isOrphan := false}
      setAllClauses ((← getAllClauses).insert c ci)
      return ci
    else return ci
  | none =>
    let allClauses := (← get).allClauses
    let ci : ClauseInfo := {
      number := allClauses.size
      proof := proof
      generatingAncestors := generatingAncestors
      descendants := []
      wasSimplified := false
      isOrphan := false
    }
    setAllClauses (allClauses.insert c ci)
    if c.lits.size == 0 then throwEmptyClauseException
    return ci

/-- Registers a new clause and adds it to the passive set. The `generatingAncestors` argument contains the list of clauses that were
    used to generate `c` (or `c`'s ancestor which generated `c` by a modifying inference). See page 8 of "E – A Brainiac Theorem Prover" -/
def addNewToPassive (c : Clause) (proof : Proof) (generatingAncestors : List Clause) : ProverM Unit := do
  match (← getAllClauses).find? c with
  | some ci =>
    if (ci.wasSimplified) then pure () -- No need to add c to the passive set because it would just be simplified away later
    else if(ci.isOrphan) then -- We've seen c before, but we should readd it because it was only removed as an orphan (and wasn't simplified away)
      trace[Prover.saturate] "Readding prior orphan to the passive set: {c}"
      -- Update c's generating ancestors and orphan status because it has been added to the passiveSet by new ancestors
      let ci := {ci with generatingAncestors := generatingAncestors, isOrphan := false}
      setAllClauses ((← getAllClauses).insert c ci)
      markAsDescendantToGeneratingAncestors c generatingAncestors -- For each generating ancestor of c, add c as a descendant of said ancestor
      setPassiveSet $ (← getPassiveSet).insert c
      setPassiveSetAgeHeap $ (← getPassiveSetAgeHeap).insert (ci.number, c)
      setPassiveSetWeightHeap $ (← getPassiveSetWeightHeap).insert (c.weight, c)
    else pure () -- c exists in allClauses and is not an orphan, so it has already been produced and can safely be ignored
  | none =>
    trace[Prover.saturate] "New passive clause: {c}"
    let ci ← addNewClause c proof generatingAncestors
    setPassiveSet $ (← getPassiveSet).insert c
    setPassiveSetAgeHeap $ (← getPassiveSetAgeHeap).insert (ci.number, c)
    setPassiveSetWeightHeap $ (← getPassiveSetWeightHeap).insert (c.weight, c)

/-- Takes a clause that was generated by preprocessing clausification and re-adds it to the passive set and its associated heaps -/
def addClausifiedToPassive (c : Clause) : ProverM Unit := do
  match (← getAllClauses).find? c with
  | some ci =>
    setPassiveSet $ (← getPassiveSet).insert c
    setPassiveSetAgeHeap $ (← getPassiveSetAgeHeap).insert (ci.number, c)
    setPassiveSetWeightHeap $ (← getPassiveSetWeightHeap).insert (c.weight, c)
  | none => throwError "Unable to find information for clausified clause {c}"

def addExprAssumptionToPassive (e : Expr) (proof : Expr) : ProverM Unit := do
  let c := Clause.fromSingleExpr e
  let mkProof := fun _ _ _ => pure proof
  addNewToPassive c {ruleName := "assumption", mkProof := mkProof} []

def ProverM.runWithExprs (x : ProverM α) (es : List (Expr × Expr)) (ctx : Context := {}) (s : State := {}) : 
    CoreM (α × State) := do
  ProverM.run (s := s) (ctx := ctx) do
    for (e, proof) in es do
      addExprAssumptionToPassive e proof
    x

@[inline] def runRuleM (x : RuleM α) : ProverM.ProverM α := do
  let symbolPrecMap ← getSymbolPrecMap
  let highesetPrecSymbolHasArityZero ← getHighesetPrecSymbolHasArityZero
  let order := λ e1 e2 => Order.kbo e1 e2 symbolPrecMap highesetPrecSymbolHasArityZero
  let (res, state) ← RuleM.run x (ctx := {order := order}) (s := {lctx := ← getLCtx, mctx := ← getMCtx})
  ProverM.setLCtx state.lctx
  ProverM.setMCtx state.mctx
  return res

@[inline] def runInferenceRule (x : RuleM Unit) : ProverM.ProverM (List (Clause × Proof)) := do
  let symbolPrecMap ← getSymbolPrecMap
  let highesetPrecSymbolHasArityZero ← getHighesetPrecSymbolHasArityZero
  let order := λ e1 e2 => Order.kbo e1 e2 symbolPrecMap highesetPrecSymbolHasArityZero
  let (_, state) ← RuleM.run x (ctx := {order := order}) (s := {lctx := ← getLCtx, mctx := ← getMCtx})
  ProverM.setLCtx state.lctx
  return state.resultClauses

@[inline] def runSimpRule (x : RuleM α) : ProverM.ProverM (α × List (Clause × Proof)) := do
  let symbolPrecMap ← getSymbolPrecMap
  let highesetPrecSymbolHasArityZero ← getHighesetPrecSymbolHasArityZero
  let order := λ e1 e2 => Order.kbo e1 e2 symbolPrecMap highesetPrecSymbolHasArityZero
  let (res, state) ← RuleM.run x (ctx := {order := order}) (s := {lctx := ← getLCtx, mctx := ← getMCtx})
  ProverM.setLCtx state.lctx
  return (res, state.resultClauses)

def addToActive (c : Clause) : ProverM Unit := do
  let _ ← getClauseInfo! c -- getClauseInfo! throws an error if c can't be found
  -- Add to superposition's side premise index:
  let idx ← getSupSidePremiseIdx
  let idx ← runRuleM do
    let (_, mclause) ← loadClauseCore c
    let sel := getSelections mclause
    mclause.foldM
      fun idx e pos => do
        let canNeverBeMaximal ← runMetaAsRuleM $ mclause.canNeverBeMaximal (← getOrder) pos.lit
        let eligible :=
          if not mclause.lits[pos.lit]!.sign then false
          else if(sel.contains pos.lit) then true
          else if(sel == []) then not canNeverBeMaximal
          else false
        if eligible then idx.insert e (c, pos)
        else return idx
      idx
  setSupSidePremiseIdx idx
  -- Add to demodulation's side premise index iff c consists of exactly one positive literal:
  if(c.lits.size = 1 && c.lits[0]!.sign) then
    let idx ← getDemodSidePremiseIdx
    let idx ← runRuleM do
      let (_, mclause) ← loadClauseCore c
      mclause.foldM (fun idx e pos => idx.insert e (c, pos)) idx
    setDemodSidePremiseIdx idx
  -- Add to main premise index:
  let idx ← getMainPremiseIdx
  let idx ← runRuleM do
    let (_, mclause) ← loadClauseCore c
    let sel := getSelections mclause
    mclause.foldGreenM
      fun idx e pos => do
        let canNeverBeMaximal ← runMetaAsRuleM $ mclause.canNeverBeMaximal (← getOrder) pos.lit
        let eligible :=
          if e.isMVar then false
          else if(sel.contains pos.lit) then true
          else if(sel == []) then not canNeverBeMaximal
          else false
        if eligible then idx.insert e (c, pos)
        else return idx
      idx
  setMainPremiseIdx idx
  -- Add to subsumption trie
  let idx ← getSubsumptionTrie
  let idx ← runRuleM $ idx.insert c
  setSubsumptionTrie idx
  -- add to active set:
  setActiveSet $ (← getActiveSet).insert c

/-- Remove c from mainPremiseIdx, supSidePremiseIdx, demodSidePremiseIdx, and subsumptionTrie -/
def removeFromDiscriminationTrees (c : Clause) : ProverM Unit := do
  let mainIdx ← getMainPremiseIdx
  let supSideIdx ← getSupSidePremiseIdx
  let demodSideIdx ← getDemodSidePremiseIdx
  let subsumptionTrie ← getSubsumptionTrie
  setMainPremiseIdx (← runRuleM $ mainIdx.delete c)
  setSupSidePremiseIdx (← runRuleM $ supSideIdx.delete c)
  setDemodSidePremiseIdx (← runRuleM $ demodSideIdx.delete c)
  setSubsumptionTrie (← runRuleM $ subsumptionTrie.delete c)

/-- If ci is the ClauseInfo corresponding to a clause c, then removeDescendants removes the direct descendants of c from the passive set.
    Additionally, it tags each direct descendant of c as "isOrphan" in allClauses so they can potentially be readded to
    the passive set. However, removeDescendants does not remove or mark any clause that appears in protectedClauses. -/
partial def removeDescendants (c : Clause) (ci : ClauseInfo) (protectedClauses : List Clause) : ProverM Unit := do
  let mut passiveSet ← getPassiveSet
  let mut allClauses ← getAllClauses
  for d in ci.descendants do
    if protectedClauses.contains d then continue
    trace[RemoveClause.debug] "Marking {d} as orphan because it is a descendant of {c} and does not appear in {protectedClauses}"
    match allClauses.find? d with
    | some dInfo =>
      -- Tag d as an orphan in allClauses
      let dInfo := {dInfo with generatingAncestors := [], isOrphan := true}
      setAllClauses $ allClauses.insert d dInfo
      allClauses ← getAllClauses
      -- Remove c from passive set
      if passiveSet.contains d then
        setPassiveSet $ passiveSet.erase d
        passiveSet ← getPassiveSet
    | none => throwError "Unable to find descendant"

/-- removeClause does the following:
    - Removes c from the active set, passive set, and all discrimination trees
    - Tags c as "wasSimplified" in allClauses
    - Removes each direct descendant of c from the passive set
    - Tags each direct descendant of c as "isOrphan" in allClauses

    protectedClauses is an additional argument that needs to be provided if a clause is being eliminated by a backward
    simplification rule. The idea is that protectedClauses contains the list of pre-existing clauses that appear in the
    conclusion of the backward simplification rule that eliminated c, and these clauses should not be removed even if
    they happen to be descendants of c. With backward simplification rules, it is possible for a clause to remove its
    ancestor (without intending to remove itself), so the protectedClauses argument ensures that no clause inadvertently
    removes itself in the process of simplifying away a different clause. -/
partial def removeClause (c : Clause) (protectedClauses := ([] : List Clause)) : ProverM Unit := do
  trace[RemoveClause.debug] "Calling removeClause with c: {c} and protectedClauses: {protectedClauses}"
  let mut activeSet ← getActiveSet
  let mut passiveSet ← getPassiveSet
  let mut allClauses ← getAllClauses
  match allClauses.find? c with
  | none => throwError "Attempted to remove {c} but was not able to find it in allClauses"
  | some ci =>
    -- Tag c as "wasSimplified" in allClauses
    let ci := {ci with wasSimplified := true}
    setAllClauses $ allClauses.insert c ci
    allClauses ← getAllClauses
    -- Remove c from active set
    if activeSet.contains c then
      setActiveSet $ activeSet.erase c
      removeFromDiscriminationTrees c
      activeSet ← getActiveSet
    -- Remove c from passive set
    if passiveSet.contains c then
      setPassiveSet $ passiveSet.erase c
      passiveSet ← getPassiveSet
    -- Remove the descendants of c and mark them as orphans
    removeDescendants c ci protectedClauses

/-- Checks whether any clause in resultClauses subsumes givenClause (by clause subsumption). If there is a clause
    c that subsumes givenClause, then `some c` is returned. Otherwise, `none` is returned.

    Note: Currently, we only check for clause subsumption, and we only check clauses in resultClauses against the
    givenClause. But it may be good in the future to:
    - Check whether any result clause can eliminate givenClause by equality subsumption (or some other simplification rule)
    - Inter-simplify the clauses in resultClauses (this would change the return type but would be more faithful to how
      immediate simplification is described in http://www.cs.man.ac.uk/~korovink/my_pub/iprover_ijcar_app_2020.pdf. See table
      1 to see which rules should be used for inter-simplification) -/
def immediateSimplification (givenClause : MClause) (resultClauses : List Clause) (givenClauseMVarIds : Array MVarId) :
  ProverM (Option Clause) := -- This is written as a ProverM rather than RuleM because subsumptionCheck depends on RuleM.lean
  runRuleM $ withoutModifyingLoadedClauses do
    for c in resultClauses do
      if ← subsumptionCheck (← loadClause c) givenClause givenClauseMVarIds then
        trace[ImmediateSimplification.debug] "Immediately simplified {givenClause.lits} with {c}"
        return some c
    return none

def performInferences (rules : List (MClause → RuleM Unit)) (c : Clause) : ProverM Unit := do
  let mut cs : List (Clause × Proof) := []
  for rule in rules do
    let curCs ← runInferenceRule do
      let c ← loadClause c
      rule c
    cs := cs.append curCs
  let (givenClauseMVars, givenClause) ← runRuleM $ RuleM.loadClauseCore c
  let givenClauseMVarIds := givenClauseMVars.map Expr.mvarId!
  let resultClauses := cs.map (fun (c, _) => c)
  match ← immediateSimplification givenClause resultClauses givenClauseMVarIds with
  | some subsumingClause => -- subsumingClause subsumes c so we can remove c and only need to add subsumingClause
    removeClause c [subsumingClause]
    match cs.find? (fun (c, _) => c == subsumingClause) with
    | some (subsumingClause, subsumingClauseProof) =>
      addNewToPassive subsumingClause subsumingClauseProof (List.map (fun p => p.clause) subsumingClauseProof.parents)
    | none => throwError "Unable to find {subsumingClause} in resultClauses"
  | none => -- No result clause subsumes c, so add each result clause to the passive set
    for (c, proof) in cs do
      addNewToPassive c proof (List.map (fun p => p.clause) proof.parents)

end ProverM
end Duper
