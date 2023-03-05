import Lean
import Duper.Saturate

open Lean
open Lean.Meta
open Duper
open ProverM
open Lean.Parser

initialize 
  registerTraceClass `TPTP_Testing
  registerTraceClass `Print_Proof
  registerTraceClass `Saturate.debug

namespace Lean.Elab.Tactic

partial def printProof (state : ProverM.State) : MetaM Unit := do
  Core.checkMaxHeartbeats "printProof"
  let rec go c (hm : Array (Nat × Clause) := {}) : MetaM (Array (Nat × Clause)) := do
    let info ← getClauseInfo! c
    if hm.contains (info.number, c) then return hm
    let mut hm := hm.push (info.number, c)
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! pp.clause) 
    let parentIds := parentInfo.map fun info => info.number
    trace[Print_Proof] "Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {c}"
    for proofParent in info.proof.parents do
      hm ← go proofParent.clause hm
    return hm
  let _ ← go Clause.empty
where 
  getClauseInfo! (c : Clause) : MetaM ClauseInfo := do
    let some ci := state.allClauses.find? c
      | throwError "clause info not found: {c}"
    return ci

def getClauseInfo! (state : ProverM.State) (c : Clause) : MetaM ClauseInfo := do
  let some ci := state.allClauses.find? c
    | throwError "clause info not found: {c}"
  return ci

abbrev ClauseHeap := Std.BinomialHeap (Nat × Clause) fun c d => c.1 ≤ d.1

partial def collectClauses (state : ProverM.State) (c : Clause) (acc : (Array Nat × ClauseHeap)) : MetaM (Array Nat × ClauseHeap) := do
  Core.checkMaxHeartbeats "collectClauses"
  let info ← getClauseInfo! state c
  if acc.1.contains info.number then return acc -- No need to recall collectClauses on c because we've already collected c
  let mut acc := acc
  -- recursive calls
  acc := (acc.1.push info.number, acc.2.insert (info.number, c))
  for proofParent in info.proof.parents do
    acc ← collectClauses state proofParent.clause acc
  return acc

-- Map from clause `id` to Array of request of levels
abbrev LevelRequests := HashMap Nat (HashMap (Array Level) Nat)

partial def collectLevelRequests (state : ProverM.State) (c : Clause)
  (lvls : Array Level) (acc : LevelRequests) : MetaM LevelRequests := do
  Core.checkMaxHeartbeats "collectLevelRequests"
  let info ← getClauseInfo! state c
  if let some set := acc.find? info.number then
    if set.contains lvls then
      return acc
  let mut acc := acc
  let lvlset :=
    match acc.find? info.number with
    | some set => set
    | none     => HashMap.empty
  trace[Meta.debug] "Request {lvls} for {c}"
  acc := acc.insert info.number (lvlset.insert lvls lvlset.size)
  for proofParent in info.proof.parents do
    let lvls' := proofParent.paramSubst.map
      (fun lvl => lvl.instantiateParams c.paramNames.data lvls.data)
    acc ← collectLevelRequests state proofParent.clause lvls' acc
  return acc

partial def mkSkProof (state : ProverM.State) : List Clause → MetaM Expr → MetaM Expr
| [], mexpr => mexpr
| c :: cs, mexpr => do
  Core.checkMaxHeartbeats "mkSkProof"
  let info ← getClauseInfo! state c
  if let some ⟨skProof, fvarId⟩ := info.proof.introducedSkolems then
    trace[Print_Proof] "Reconstructing skolem, fvar = {mkFVar fvarId}"
    let ty := (state.lctx.get! fvarId).type
    trace[Meta.debug] "Reconstructing skolem, type = {ty}"
    let userName := (state.lctx.get! fvarId).userName
    trace[Print_Proof] "Reconstructed skloem, userName = {userName}"
    trace[Meta.debug] "Reconstructed skolem definition: {skProof}"
    let lctx ← getLCtx
    let lctx' := lctx.mkLetDecl fvarId userName ty skProof
    withLCtx lctx' (← getLocalInstances) do
      mkLambdaFVars (usedLetOnly := false) #[mkFVar fvarId] (← mkSkProof state cs mexpr)
  else
    mkSkProof state cs mexpr

-- `Nat` is the id of the clause
-- `Array Level` is the requested levels for the clause
-- `Expr` is the fvarId corresponding to the proof for the clause in the current `lctx`
abbrev ConstructedClauses := HashMap (Nat × Array Level) Expr

partial def mkClauseProofHelper (state : ProverM.State) (reqs : LevelRequests) :
  List Clause → ConstructedClauses → MetaM (Expr × ConstructedClauses)
| [], _ => panic! "mkClauseProof :: empty clause list"
| c :: cs, ctrc => do
  Core.checkMaxHeartbeats "mkClauseProof"
  let info ← getClauseInfo! state c
  let lvlreqs := reqs.find! info.number
  -- let mut parentss := #[]
  let mut remainingProofConsCode : ConstructedClauses → MetaM (Expr × ConstructedClauses) :=
    mkClauseProofHelper state reqs cs
  for (req, reqid) in lvlreqs.toList do
    let mut parents : Array Expr := #[]
    let mut instantiatedProofParents := #[]
    for parent in info.proof.parents do
      let parentInfo ← getClauseInfo! state parent.clause
      let parentNumber := parentInfo.number
      let instantiatedParentParamSubst := parent.paramSubst.map (fun lvl => lvl.instantiateParams c.paramNames.data req.data)
      let parentPrfFvar := ctrc.find! (parentNumber, instantiatedParentParamSubst)
      parents := parents.push parentPrfFvar
      let instPP := {parent with paramSubst := instantiatedParentParamSubst}
      instantiatedProofParents := instantiatedProofParents.push instPP
    -- Now `parents[i] : info.proof.parents[i].toForallExpr`, for all `i`
    let instCLits := c.lits.map (fun l => l.instantiateLevelParamsArray c.paramNames req)
    let instBvarTys := c.bVarTypes.map (fun e => e.instantiateLevelParamsArray c.paramNames req)
    let instC := {c with lits := instCLits, bVarTypes := instBvarTys}
    trace[Meta.debug] "Reconstructing proof for #{info.number}: {instC}, Rule Name: {info.proof.ruleName}"
    let newProof ← (do
      let prf ← info.proof.mkProof parents.data instantiatedProofParents.data info.proof.newVarIndices instC
      if info.proof.ruleName != "assumption" then
        return prf
      else
        -- If the rule is "assumption", then there is no proofparent and
        --   we have to manually instantiate the universe mvars
        return prf.instantiateLevelParamsArray c.paramNames req)
    let newTarget := instC.toForallExpr
    trace[Meta.debug] "#{info.number}'s newProof: {newProof}"
    if cs == [] then return (newProof, ctrc)
    remainingProofConsCode := fun ctrc =>
      withLetDecl (Name.mkNum (Name.mkNum `clause info.number) reqid) newTarget newProof fun g => do
        let ctrc' := ctrc.insert (info.number, req) g
        let (remainingProof, ctrc') ← remainingProofConsCode ctrc'
        let rexpr ← mkLambdaFVars (usedLetOnly := false) #[g] remainingProof
        return (rexpr, ctrc')
  remainingProofConsCode ctrc

partial def mkClauseProof (state : ProverM.State) (cs : List Clause) : MetaM Expr := do
  let cs := Array.mk cs
  let cslen := cs.size
  if cslen == 0 then
    throwError "mkClauseProof :: Empty Clause List"
  -- The final empty clause
  let emptyClause := cs[cslen - 1]!
  -- Other clauses
  let zeroLvlsForEmptyClause := emptyClause.paramNames.map (fun _ => Level.zero)
  let reqs ← collectLevelRequests state emptyClause zeroLvlsForEmptyClause HashMap.empty
  let (e, _) ← mkClauseProofHelper state reqs cs.data HashMap.empty
  return e

def applyProof (state : ProverM.State) : TacticM Unit := do
  let l := (← collectClauses state Clause.empty (#[], Std.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[Meta.debug] "{l}"
  -- First make proof for skolems, then make proof for clauses
  let proof ← mkSkProof state l (mkClauseProof state l)
  trace[Print_Proof] "Proof: {proof}"
  Lean.MVarId.assign (← getMainGoal) proof -- TODO: List.last?

def elabFact (stx : Term) : TacticM (Array (Expr × Array Name)) := do
  match stx with
  | `($id:ident) =>
    -- Try to look up any defining equations for this identifier
    let some expr ← Term.resolveId? id
      | throwError "Unknown identifier {id}"
    match ← getEqnsFor? expr.constName! (nonRec := true) with
    | some eqns => do
      eqns.mapM fun eq => do elabFactAux (← `($(mkIdent eq)))
    | none =>
      -- Identifier is not a definition
      return #[← elabFactAux stx]
  | _ => return #[← elabFactAux stx]
where elabFactAux (stx : Term) : TacticM (Expr × Array Name) :=
  -- elaborate term as much as possible and abstract any remaining mvars:
  Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let abstres ← abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return (e, paramNames)

def collectAssumptions (facts : Array Term) : TacticM (List (Expr × Expr × Array Name)) := do
  let mut formulas := []
  -- Load all local decls:
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← Lean.FVarId.getDecl fVarId
    unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
      formulas := (← instantiateMVars ldecl.type, ← mkAppM ``eq_true #[mkFVar fVarId], #[]) :: formulas
  -- load user-provided facts
  for facts in ← facts.mapM elabFact do
    for (fact, params) in facts do
      let type ← inferType fact
      if ← isProp type then
        formulas := (← inferType fact, ← mkAppM ``eq_true #[fact], params) :: formulas
      else
        throwError "invalid fact for duper, proposition expected {indentExpr fact}"

  return formulas

syntax (name := duper) "duper" (colGt ident)? ("[" term,* "]")? : tactic

macro_rules
| `(tactic| duper) => `(tactic| duper [])

def runDuper (facts : Syntax.TSepArray `term ",") : TacticM ProverM.State := withNewMCtxDepth do
  let formulas ← collectAssumptions facts.getElems
  trace[Meta.debug] "Formulas from collectAssumptions: {formulas}"
  let (_, state) ←
    ProverM.runWithExprs (s := {lctx := ← getLCtx, mctx := ← getMCtx})
      ProverM.saturateNoPreprocessingClausification
      formulas
  return state

@[tactic duper]
def evalDuper : Tactic
| `(tactic| duper [$facts,*]) => withMainContext do
  let startTime ← IO.monoMsNow
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let state ← runDuper facts
    match state.result with
    | Result.contradiction => do
      logInfo s!"Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
      logInfo s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    | Result.saturated =>
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| `(tactic| duper $ident:ident [$facts,*]) => withMainContext do
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let state ← runDuper facts
    match state.result with
    | Result.contradiction => do
      logInfo s!"{ident} test succeeded in finding a contradiction"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
    | Result.saturated =>
      logInfo s!"{ident} test resulted in prover saturation"
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

syntax (name := duper_no_timing) "duper_no_timing" ("[" term,* "]")? : tactic

macro_rules
| `(tactic| duper_no_timing) => `(tactic| duper_no_timing [])

@[tactic duper_no_timing]
def evalDuperNoTiming : Tactic
| `(tactic| duper_no_timing [$facts,*]) => withMainContext do
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let state ← runDuper facts
    match state.result with
    | Result.contradiction => do
      logInfo s!"Contradiction found"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
      logInfo s!"Constructed proof"
    | Result.saturated =>
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic

