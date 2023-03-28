import Duper.Clause
import Std.Data.BinomialHeap
import Duper.Fingerprint
import Duper.Selection
import Duper.SubsumptionTrie
import Duper.Util.ClauseSubsumptionCheck
import Duper.Util.StrategyHeap
import Duper.Util.IdStrategyHeap
import Duper.Util.AbstractMVars

namespace Duper
namespace ProverM
open Lean
open Lean.Core
open Std
open RuleM
open Expr

initialize
  registerTraceClass `Simplification.debug
  registerTraceClass `ImmediateSimplification.debug
  registerTraceClass `typeInhabitationReasoning.debug

inductive Result :=
| unknown
| saturated
| contradiction
  deriving Inhabited

open Result

structure ClauseInfo where
(number : Nat)
(proof : Proof)
(generatingAncestors : Array Clause)
(descendants : List Clause)
(wasSimplified : Bool)
(isOrphan : Bool)
deriving Inhabited

abbrev ClauseSet := HashSet Clause
abbrev FairAgeClauseHeap := StrategyHeap Clause (β:=Nat)
abbrev abstractedMVarList := List Meta.AbstractMVarsResult
abbrev abstractedMVarAndClauseList := List (Meta.AbstractMVarsResult × Clause)

instance : ToMessageData Result := 
⟨fun r => match r with
| unknown => "unknown"
| saturated => "saturated"
| contradiction => "contradiction"⟩

structure Context where
deriving Inhabited

structure State where
  result : Result := unknown
  allClauses : HashMap Clause ClauseInfo := {}
  activeSet : ClauseSet := {}
  passiveSet : FairAgeClauseHeap := FairAgeHeap.empty Clause 5
  qStreamSet : ClauseStreamHeap ClauseStream := ClauseStreamHeap.empty ClauseStream
  symbolPrecMap : SymbolPrecMap := HashMap.empty
  highesetPrecSymbolHasArityZero : Bool := false
  mainPremiseIdx : RootCFPTrie := {}
  supSidePremiseIdx : RootCFPTrie := {}
  demodSidePremiseIdx : RootCFPTrie := {}
  subsumptionTrie : SubsumptionTrie := SubsumptionTrie.emptyNode
  skolemMap : HashMap Nat SkolemInfo := HashMap.empty
  skolemSorryName : Name := Name.anonymous
  verifiedInhabitedTypes : abstractedMVarList := [] -- List of (abstracted) types that we have determined are inhabited by typeclass inference
  verifiedNonemptyTypes : abstractedMVarAndClauseList := [] -- List of (abstracted) types that duper has derived are nonempty (along with the clause asserting that fact)
  potentiallyUninhabitedTypes : abstractedMVarList := []
  potentiallyVacuousClauses : ClauseSet := {}
  -- We need this field because empty clauses may contain
  --   level parameters, and we can't just use ```Clause.empty``` as
  --   a key to find the clauseInfo of the empty clause in ```allClauses```
  emptyClause : Option Clause := none

abbrev ProverM := ReaderT Context $ StateRefT State MetaM

instance : AddMessageContext ProverM where
  addMessageContext := fun msgData => do
    let env ← getEnv
    let lctx ← getLCtx
    let opts ← getOptions
    pure $ MessageData.withContext { env := env, mctx := {}, lctx := lctx, opts := opts } msgData

@[inline] def ProverM.run (x : ProverM α) (ctx : Context := {}) (s : State := {}) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def ProverM.run' (x : ProverM α) (ctx : Context := {}) (s : State := {}) : MetaM α :=
  Prod.fst <$> x.run ctx s

instance [MetaEval α] : MetaEval (ProverM α) :=
  ⟨fun env opts x _ => MetaEval.eval env opts x.run' true⟩

initialize
  registerTraceClass `Prover
  registerTraceClass `Prover.saturate

def getResult : ProverM Result :=
  return (← get).result

def getAllClauses : ProverM (HashMap Clause ClauseInfo) :=
  return (← get).allClauses

def getActiveSet : ProverM ClauseSet :=
  return (← get).activeSet

def getPassiveSet : ProverM FairAgeClauseHeap :=
  return (← get).passiveSet

def getSymbolPrecMap : ProverM SymbolPrecMap :=
  return (← get).symbolPrecMap

def getHighesetPrecSymbolHasArityZero : ProverM Bool :=
  return (← get).highesetPrecSymbolHasArityZero

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

def getQStreamSet : ProverM (ClauseStreamHeap ClauseStream) :=
  return (← get).qStreamSet

def getSkolemSorryName : ProverM Name :=
  return (← get).skolemSorryName

def getSkolemMap : ProverM (HashMap Nat SkolemInfo) :=
  return (← get).skolemMap

def getVerifiedInhabitedTypes : ProverM abstractedMVarList :=
  return (← get).verifiedInhabitedTypes

def getVerifiedNonemptyTypes : ProverM abstractedMVarAndClauseList :=
  return (← get).verifiedNonemptyTypes

def getPotentiallyUninhabitedTypes : ProverM abstractedMVarList :=
  return (← get).potentiallyUninhabitedTypes

def getPotentiallyVacuousClauses : ProverM ClauseSet :=
  return (← get).potentiallyVacuousClauses

def getEmptyClause : ProverM (Option Clause) :=
  return (← get).emptyClause

def setResult (result : Result) : ProverM Unit :=
  modify fun s => { s with result := result }

def setActiveSet (activeSet : ClauseSet) : ProverM Unit :=
  modify fun s => { s with activeSet := activeSet }

def setAllClauses (allClauses : HashMap Clause ClauseInfo) : ProverM Unit :=
  modify fun s => { s with allClauses := allClauses }

def setPassiveSet (passiveSet : FairAgeClauseHeap) : ProverM Unit :=
  modify fun s => { s with passiveSet := passiveSet }

def setSymbolPrecMap (symbolPrecMap : SymbolPrecMap) : ProverM Unit :=
  modify fun s => { s with symbolPrecMap := symbolPrecMap }

def setHighesetPrecSymbolHasArityZero (highesetPrecSymbolHasArityZero : Bool) : ProverM Unit :=
  modify fun s => { s with highesetPrecSymbolHasArityZero := highesetPrecSymbolHasArityZero }

def setSupSidePremiseIdx (supSidePremiseIdx : RootCFPTrie) : ProverM Unit :=
  modify fun s => { s with supSidePremiseIdx := supSidePremiseIdx }

def setDemodSidePremiseIdx (demodSidePremiseIdx : RootCFPTrie) : ProverM Unit :=
  modify fun s => { s with demodSidePremiseIdx := demodSidePremiseIdx }

def setMainPremiseIdx (mainPremiseIdx : RootCFPTrie) : ProverM Unit :=
  modify fun s => { s with mainPremiseIdx := mainPremiseIdx }

def setSubsumptionTrie (subsumptionTrie : SubsumptionTrie) : ProverM Unit :=
  modify fun s => { s with subsumptionTrie := subsumptionTrie }

def setQStreamSet (Q : ClauseStreamHeap ClauseStream) : ProverM Unit :=
  modify fun s => { s with qStreamSet := Q }

def setSkolemMap (skmap : HashMap Nat SkolemInfo) : ProverM Unit :=
  modify fun s => {s with skolemMap := skmap}

def setVerifiedInhabitedTypes (verifiedInhabitedTypes : abstractedMVarList) : ProverM Unit :=
  modify fun s => {s with verifiedInhabitedTypes := verifiedInhabitedTypes}

def setVerifiedNonemptyTypes (verifiedNonemptyTypes : abstractedMVarAndClauseList) : ProverM Unit :=
  modify fun s => {s with verifiedNonemptyTypes := verifiedNonemptyTypes}

def setPotentiallyUninhabitedTypes (potentiallyUninhabitedTypes : abstractedMVarList) : ProverM Unit :=
  modify fun s => {s with potentiallyUninhabitedTypes := potentiallyUninhabitedTypes}

def setPotentiallyVacuousClauses (potentiallyVacuousClauses : ClauseSet) : ProverM Unit :=
  modify fun s => {s with potentiallyVacuousClauses := potentiallyVacuousClauses}

def setEmptyClause (c : Clause) : ProverM Unit :=
  modify fun s => {s with emptyClause := some c}

initialize emptyClauseExceptionId : InternalExceptionId ← registerInternalExceptionId `emptyClause

def throwEmptyClauseException : ProverM α :=
  throw <| Exception.internal emptyClauseExceptionId

partial def chooseGivenClause : ProverM (Option Clause) := do
  Core.checkMaxHeartbeats "chooseGivenClause"
  if let some (clause, heap) := (← getPassiveSet).pop? then
    setPassiveSet heap
    return (some clause)
  else
    return none

/-- Given a clause c and a list of ancestors, markAsDescendantToGeneratingAncestors adds c to each generating ancestor's list of descendants -/
def markAsDescendantToGeneratingAncestors (c : Clause) (generatingAncestors : Array Clause) : ProverM Unit := do
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
def addNewClause (c : Clause) (proof : Proof) (generatingAncestors : Array Clause) : ProverM ClauseInfo := do
  markAsDescendantToGeneratingAncestors c generatingAncestors
  let allClauses ← getAllClauses
  let ci ← (do
    match allClauses.find? c with
    | some ci =>
      if ci.isOrphan then
        -- Update c's generating ancestors and orphan status because it has been added to the passiveSet by new ancestors
        let ci := {ci with generatingAncestors := generatingAncestors, isOrphan := false}
        setAllClauses (allClauses.insert c ci)
        return ci
      else return ci
    | none =>
      let ci : ClauseInfo := {
        number := allClauses.size
        proof := proof
        generatingAncestors := generatingAncestors
        descendants := []
        wasSimplified := false
        isOrphan := false
      }
      setAllClauses (allClauses.insert c ci)
      if ← getInhabitationReasoningM then
        if c.lits.size == 0 && c.bVarTypes.size == 0 then 
          setEmptyClause c
          throwEmptyClauseException
        return ci
      else
        if c.lits.size == 0 then
          setEmptyClause c
          throwEmptyClauseException
        return ci)
  trace[Prover.saturate] (
    let parentInfos := proof.parents.map (fun p => allClauses.find! p.clause)
    m!"New clause #{ci.number} by {proof.ruleName} on {parentInfos.map (fun i => i.number)}: {c}"
  )
  return ci

/-- Registers a new clause and adds it to the passive set. The `generatingAncestors` argument contains the list of clauses that were
    used to generate `c` (or `c`'s ancestor which generated `c` by a modifying inference). See page 8 of "E – A Brainiac Theorem Prover" -/
def addNewToPassive (c : Clause) (proof : Proof) (generatingAncestors : Array Clause) : ProverM Unit := do
  match (← getAllClauses).find? c with
  | some ci =>
    if (ci.wasSimplified) then pure () -- No need to add c to the passive set because it would just be simplified away later
    else if(ci.isOrphan) then -- We've seen c before, but we should readd it because it was only removed as an orphan (and wasn't simplified away)
      trace[Prover.saturate] "Reading prior orphan to the passive set: {c}"
      -- Update c's generating ancestors and orphan status because it has been added to the passiveSet by new ancestors
      let ci := {ci with generatingAncestors := generatingAncestors, isOrphan := false}
      setAllClauses ((← getAllClauses).insert c ci)
      markAsDescendantToGeneratingAncestors c generatingAncestors -- For each generating ancestor of c, add c as a descendant of said ancestor
      setPassiveSet $ (← getPassiveSet).insert c c.weight ci.number
    else pure () -- c exists in allClauses and is not an orphan, so it has already been produced and can safely be ignored
  | none =>
    let ci ← addNewClause c proof generatingAncestors
    setPassiveSet $ (← getPassiveSet).insert c c.weight ci.number

/-- Takes a clause that was generated by preprocessing clausification and re-adds it to the passive set and its associated heaps -/
def addClausifiedToPassive (c : Clause) : ProverM Unit := do
  match (← getAllClauses).find? c with
  | some ci =>
    setPassiveSet $ (← getPassiveSet).insert c c.weight ci.number
  | none => throwError "Unable to find information for clausified clause {c}"

def ProverM.runWithExprs (x : ProverM α) (es : List (Expr × Expr × Array Name)) (ctx : Context) (s : State) : MetaM (α × State) := do
  ProverM.run (s := s) (ctx := ctx) do
    for (e, proof, paramNames) in es do
      let c := Clause.fromSingleExpr paramNames e
      let mkProof := fun _ _ _ _ => pure proof
      addNewToPassive c {parents := #[], ruleName := "assumption", mkProof := mkProof} #[]
    x

@[inline] def runRuleM (x : RuleM α) : ProverM.ProverM α := do
  let mctx ← getMCtx
  let symbolPrecMap ← getSymbolPrecMap
  let highesetPrecSymbolHasArityZero ← getHighesetPrecSymbolHasArityZero
  let order := λ e1 e2 => Order.kbo e1 e2 symbolPrecMap highesetPrecSymbolHasArityZero
  let (res, state) ← RuleM.run x (ctx := {order := order, skolemSorryName := ← getSkolemSorryName}) (s := {skolemMap := ← getSkolemMap})
  ProverM.setSkolemMap state.skolemMap
  setMCtx mctx
  return res

def addPotentiallyVacuousClause (c : Clause) : ProverM Unit := do
  trace[typeInhabitationReasoning.debug] "Registering {c} as potentially vacuous"
  setPotentiallyVacuousClauses $ (← getPotentiallyVacuousClauses).insert c

def addToActive (c : Clause) : ProverM Unit := do
  let cInfo ← getClauseInfo! c -- getClauseInfo! throws an error if c can't be found
  let cNum := cInfo.number
  -- Add to superposition's side premise index:
  let idx ← getSupSidePremiseIdx
  let idx ← runRuleM do
    let (_, mclause) ← loadClauseCore c
    let sel := getSelections mclause
    mclause.foldM
      fun idx e pos => do
        let canNeverBeMaximal ← mclause.canNeverBeMaximal (← getOrder) pos.lit
        let eligible :=
          if not mclause.lits[pos.lit]!.sign then false
          else if(sel.contains pos.lit) then true
          else if(sel == []) then not canNeverBeMaximal
          else false
        if eligible then idx.insert e (cNum, c, pos)
        else return idx
      idx
  setSupSidePremiseIdx idx
  -- Add to demodulation's side premise index iff c consists of exactly one positive literal:
  if(c.lits.size = 1 && c.lits[0]!.sign) then
    let idx ← getDemodSidePremiseIdx
    let idx ← runRuleM do
      let (_, mclause) ← loadClauseCore c
      mclause.foldM (fun idx e pos => idx.insert e (cNum, c, pos)) idx
    setDemodSidePremiseIdx idx
  -- Add to main premise index:
  let idx ← getMainPremiseIdx
  let idx ← runRuleM do
    let (_, mclause) ← loadClauseCore c
    let sel := getSelections mclause
    mclause.foldGreenM
      fun idx e pos => do
        let canNeverBeMaximal ← mclause.canNeverBeMaximal (← getOrder) pos.lit
        let eligible :=
          if e.isMVar then false
          else if(sel.contains pos.lit) then true
          else if(sel == []) then not canNeverBeMaximal
          else false
        if eligible then idx.insert e (cNum, c, pos)
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
    trace[Simplification.debug] "Marking {d} as orphan because it is a descendant of {c} and does not appear in {protectedClauses}"
    match allClauses.find? d with
    | some dInfo =>
      -- Tag d as an orphan in allClauses
      let dInfo := {dInfo with generatingAncestors := #[], isOrphan := true}
      setAllClauses $ allClauses.insert d dInfo
      allClauses ← getAllClauses
      -- Remove c from passive set
      setPassiveSet $ passiveSet.erase d
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
  trace[Simplification.debug] "Calling removeClause with c: {c} and protectedClauses: {protectedClauses}"
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
    setPassiveSet $ passiveSet.erase c
    -- Remove the descendants of c and mark them as orphans
    -- removeDescendants c ci protectedClauses -- Currently commented out because tests indicate it currently worsens performance

/-- Checks whether any clause in resultClauses subsumes givenClause (by clause subsumption). If there is a clause
    c that subsumes givenClause, then `some c` is returned. Otherwise, `none` is returned.

    Note: Currently, we only check for clause subsumption, and we only check clauses in resultClauses against the
    givenClause. But it may be good in the future to:
    - Check whether any result clause can eliminate givenClause by equality subsumption (or some other simplification rule)
    - Inter-simplify the clauses in resultClauses (this would change the return type but would be more faithful to how
      immediate simplification is described in http://www.cs.man.ac.uk/~korovink/my_pub/iprover_ijcar_app_2020.pdf. See table
      1 to see which rules should be used for inter-simplification) -/
def immediateSimplification (givenClause : Clause) (resultClause : Clause) :
  ProverM (Option Clause) := -- This is written as a ProverM rather than RuleM because subsumptionCheck depends on RuleM.lean
  runRuleM $ withoutModifyingLoadedClauses do
    let (givenMClauseMVars, givenMClause) ← RuleM.loadClauseCore givenClause
    let givenMClauseMVarIds := givenMClauseMVars.map Expr.mvarId!
    let c := resultClause
    if c != givenClause && (← subsumptionCheck (← loadClause c) givenMClause givenMClauseMVarIds) then
      trace[ImmediateSimplification.debug] "Immediately simplified {givenClause} with {c}"
      return some c
    return none

end ProverM
end Duper