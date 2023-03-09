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

def getClauseInfo! (state : ProverM.State) (c : Clause) : CoreM ClauseInfo := do
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

structure PRContext where
  pmstate : ProverM.State
  reqs  : LevelRequests

structure PRState where
  -- `Nat` is the `id` of the clause
  -- `Array Level` is the requested levels for the clause
  -- `Expr` is the fvarId corresponding to the proof for the clause in the current `lctx`
  constructedClauses : HashMap (Nat × Array Level) Expr
  -- Map from `id` of skolem constant to the constructed `fvar`
  constructedSkolems : HashMap Nat FVarId
  lctx : LocalContext
  mctx : MetavarContext
  localInstances : LocalInstances
  fvars : Array Expr
deriving Inhabited

def PRState.insertConstructedClauses (prs : PRState) (key : Nat × Array Level) (val : Expr) :=
  {prs with constructedClauses := prs.constructedClauses.insert key val}

abbrev PRM := ReaderT PRContext <| StateRefT PRState CoreM

-- Does not update the metavariable context !
def runMetaAsPRM {α} (x : MetaM α) : PRM α := do
    let lctx := (← get).lctx
    let mctx := (← get).mctx
    let localInstances := (← get).localInstances
    let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx, localInstances := localInstances}) (s := {mctx := mctx}) do
      x
    modify fun s => {s with mctx := state.mctx}
    return res

def PRM.run (m : PRM α) (ctx : PRContext) (st : PRState) : CoreM (α × PRState) :=
  StateRefT'.run (m ctx) st

private instance : Inhabited TransformStep where
  default := TransformStep.continue

partial def PRM.matchSkolem : Expr → PRM TransformStep
| e@(.app ..) => e.withApp fun f args => do
  let (.const skName lvl) := f
    | return .continue
  let skolemSorryName := (← read).pmstate.skolemSorryName
  if skName == skolemSorryName then
    let lvarr := args[0]!
    let .natVal skid := args[1]!.litValue!
      | throwError "PRM.matchSkolem :: Invalid skolem id!"
    let skTy := args[2]!
    let skmap := (← read).pmstate.skolemMap
    let consk := (← get).constructedSkolems
    if let some fvarId := consk.find? skid then
      let trailingArgs := args.extract 3 args.size
      let trailingArgs ← trailingArgs.mapM (fun e => Core.transform e PRM.matchSkolem)
      return .done (mkAppN (mkFVar fvarId) trailingArgs)
    if let some isk := skmap.find? skid then
      let ⟨skProof, params⟩ := isk
      let skProof ← Core.transform skProof PRM.matchSkolem
      let skTy ← Core.transform skTy PRM.matchSkolem
      let fvarId ← mkFreshFVarId
      let userName := Name.num `skol skid
      runMetaAsPRM <| do
        trace[Print_Proof] "Reconstructing skolem, fvar = {mkFVar fvarId}"
        trace[Meta.debug] "Reconstructing skolem, type = {skTy}"
        trace[Print_Proof] "Reconstructed skolem, userName = {userName}"
        trace[Meta.debug] "Reconstructed skolem definition: {skProof}"
      let lctx := (← get).lctx
      let lctx' := lctx.mkLetDecl fvarId userName skTy skProof
      modify fun s => {s with lctx := lctx'}
      modify fun s => {s with constructedSkolems := s.constructedSkolems.insert skid fvarId}
      modify fun s => {s with fvars := s.fvars.push (mkFVar fvarId)}
      let trailingArgs := args.extract 3 args.size
      let trailingArgs ← trailingArgs.mapM (fun e => Core.transform e PRM.matchSkolem)
      return .done (mkAppN (mkFVar fvarId) trailingArgs)
    else
      throwError "PRM.matchSkolem :: Unable to find skolem {skid} in skolem map!"
  else
    return .continue
| _ => return .continue

partial def mkSkProof : List Clause → PRM Unit
| [] => pure ()
| c :: cs => do
  Core.checkMaxHeartbeats "mkSkProof"
  let cexpr := c.toForallExpr
  let _ ← Core.transform cexpr PRM.matchSkolem
  mkSkProof cs

partial def mkClauseProof : List Clause → PRM Expr
| [] => panic! "mkClauseProof :: empty clause list"
| c :: cs => do
  let state := (← read).pmstate
  let reqs := (← read).reqs
  Core.checkMaxHeartbeats "mkClauseProof"
  let info ← getClauseInfo! state c
  let lvlreqs := reqs.find! info.number
  for (req, reqid) in lvlreqs.toList do
    let mut parents : Array Expr := #[]
    let mut instantiatedProofParents := #[]
    for parent in info.proof.parents do
      let parentInfo ← getClauseInfo! state parent.clause
      let parentNumber := parentInfo.number
      let instantiatedParentParamSubst := parent.paramSubst.map (fun lvl => lvl.instantiateParams c.paramNames.data req.data)
      let parentPrfFvar := (← get).constructedClauses.find! (parentNumber, instantiatedParentParamSubst)
      -- TODO : Move param instantiation here
      parents := parents.push parentPrfFvar
      let parentClauseLits ← parent.clause.lits.mapM (fun l => l.mapM fun e => Core.transform e PRM.matchSkolem)
      let parentClause := {parent.clause with lits := parentClauseLits}
      let parentExpr ← Core.transform parent.expr PRM.matchSkolem
      let instPP := {parent with expr := parentExpr, clause := parentClause, paramSubst := instantiatedParentParamSubst}
      instantiatedProofParents := instantiatedProofParents.push instPP
    -- Now `parents[i] : info.proof.parents[i].toForallExpr`, for all `i`
    let instCLits := c.lits.map (fun l => l.instantiateLevelParamsArray c.paramNames req)
    let instCLits ← instCLits.mapM (fun l => l.mapM fun e => Core.transform e PRM.matchSkolem)
    let instBVarTys := c.bVarTypes.map (fun e => e.instantiateLevelParamsArray c.paramNames req)
    let instC := {c with lits := instCLits, bVarTypes := instBVarTys}
    runMetaAsPRM <|
      do trace[Meta.debug] "Reconstructing proof for #{info.number}: {instC}, Rule Name: {info.proof.ruleName}"
    let instTr := info.proof.transferExprs.map (fun e => e.instantiateLevelParamsArray c.paramNames req)
    let newProof ← (do
      let prf ← runMetaAsPRM <|
        info.proof.mkProof parents.data instantiatedProofParents.data instTr instC
      if info.proof.ruleName != "assumption" then
        return prf
      else
        -- If the rule is "assumption", then there is no proofparent and
        --   we have to manually instantiate the universe mvars
        return prf.instantiateLevelParamsArray c.paramNames req)
    let newTarget := instC.toForallExpr
    runMetaAsPRM <|
      do trace[Meta.debug] "#{info.number}'s newProof: {newProof}"
    if cs == [] then return newProof
    -- Add the new proof to the local context
    let fvarId ← mkFreshFVarId
    let declName := (Name.mkNum (Name.mkNum `clause info.number) reqid)
    let lctx' := (← get).lctx.mkLetDecl fvarId declName newTarget newProof
    modify fun ctrc => ctrc.insertConstructedClauses (info.number, req) (mkFVar fvarId)
    modify fun ctrc => {ctrc with lctx := lctx'}
    modify fun ctrc => {ctrc with fvars := ctrc.fvars.push (mkFVar fvarId)}
  mkClauseProof cs

partial def mkAllProof (state : ProverM.State) (cs : List Clause) : MetaM Expr := do
  let cs := Array.mk cs
  let cslen := cs.size
  if cslen == 0 then
    throwError "mkClauseProof :: Empty Clause List"
  -- The final empty clause
  let emptyClause := cs[cslen - 1]!
  -- Other clauses
  let zeroLvlsForEmptyClause := emptyClause.paramNames.map (fun _ => Level.zero)
  let reqs ← collectLevelRequests state emptyClause zeroLvlsForEmptyClause HashMap.empty
  let (e, prstate) ← (do mkSkProof cs.data; mkClauseProof cs.data).run
      {pmstate := state, reqs := reqs}
      {constructedClauses := HashMap.empty, constructedSkolems := HashMap.empty,
       lctx := ← getLCtx, mctx := ← getMCtx, localInstances := ← getLocalInstances, fvars := #[]}
  setMCtx prstate.mctx
  let lctx := prstate.lctx
  let fvars := prstate.fvars
  let abstLet ← withLCtx lctx (← getLocalInstances) do
    mkLambdaFVars (usedLetOnly := false) fvars e
  return abstLet

def applyProof (state : ProverM.State) : TacticM Unit := do
  let l := (← collectClauses state Clause.empty (#[], Std.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[Meta.debug] "Collected clauses: {l}"
  -- First make proof for skolems, then make proof for clauses
  let proof ← mkAllProof state l
  trace[Print_Proof] "Proof: {proof}"
  Lean.MVarId.assign (← getMainGoal) proof -- TODO: List.last?

/-- Produces definional equations for a recursor `recVal` such as

  `@Nat.rec m z s (Nat.succ n) = s n (@Nat.rec m z s n)`
  
  The returned list contains one equation
  for each constructor, a proof of the equation, and the contained level
  parameters. -/
def addRecAsFact (recVal : RecursorVal): TacticM (List (Expr × Expr × Array Name)) := do
  let some (.inductInfo indVal) := (← getEnv).find? recVal.getInduct
    | throwError "Expected inductive datatype: {recVal.getInduct}"
      
  let expr := mkConst recVal.name (recVal.levelParams.map Level.param)
  let res ← forallBoundedTelescope (← inferType expr) recVal.getMajorIdx fun xs _ => do
    let expr := mkAppN expr xs
    return ← indVal.ctors.mapM fun ctorName => do
      let ctor ← mkAppOptM ctorName #[]
      let (eq, proof) ← forallTelescope (← inferType ctor) fun ys _ => do
        let ctor := mkAppN ctor ys
        let expr := mkApp expr ctor
        let some redExpr ← reduceRecMatcher? expr
          | throwError "Could not reduce recursor application: {expr}"
        let redExpr ← Core.betaReduce redExpr -- TODO: The prover should be able to beta-reduce!
        let eq ← mkEq expr redExpr
        let proof ← mkEqRefl expr
        return (← mkForallFVars ys eq, ← mkLambdaFVars ys proof)
      return (← mkForallFVars xs eq, ← mkLambdaFVars xs proof, recVal.levelParams.toArray)

  return res

/-- From a user-provided fact `stx`, produce a suitable fact, its proof, and a
    list of universe parameter names-/
def elabFact (stx : Term) : TacticM (Array (Expr × Expr × Array Name)) := do
  match stx with
  | `($id:ident) =>
    let some expr ← Term.resolveId? id
      | throwError "Unknown identifier {id}"

    match (← getEnv).find? expr.constName! with
    | some (.recInfo val) =>
      let facts ← addRecAsFact val
      let facts ← facts.mapM fun (fact, proof, paramNames) => do
        return (← instantiateMVars fact, ← instantiateMVars proof, paramNames)
      return facts.toArray
    | some (.defnInfo val) =>
      let some eqns ← getEqnsFor? expr.constName! (nonRec := true)
        | throwError "Could not generate definition equations for {expr.constName!}"
        eqns.mapM fun eq => do elabFactAux (← `($(mkIdent eq)))
    | some (.axiomInfo _)  => return #[← elabFactAux stx]
    | some (.thmInfo _)    => return #[← elabFactAux stx]
    | some (.opaqueInfo _) => throwError "Opaque constants cannot be provided as facts"
    | some (.quotInfo _)   => throwError "Quotient constants cannot be provided as facts"
    | some (.inductInfo _) => throwError "Inductive types cannot be provided as facts"
    | some (.ctorInfo _)   => throwError "Constructors cannot be provided as facts"
    | none => throwError "Unknown constant {expr.constName!}"
  | _ => return #[← elabFactAux stx]
where elabFactAux (stx : Term) : TacticM (Expr × Expr × Array Name) :=
  -- elaborate term as much as possible and abstract any remaining mvars:
  Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let abstres ← abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return (← inferType e, e, paramNames)

def collectAssumptions (facts : Array Term) : TacticM (List (Expr × Expr × Array Name)) := do
  let mut formulas := []
  -- Load all local decls:
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← Lean.FVarId.getDecl fVarId
    unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
      formulas := (← instantiateMVars ldecl.type, ← mkAppM ``eq_true #[mkFVar fVarId], #[]) :: formulas
  -- load user-provided facts
  for facts in ← facts.mapM elabFact do
    for (fact, proof, params) in facts do
      if ← isProp fact then
        formulas := (fact, ← mkAppM ``eq_true #[proof], params) :: formulas
      else
        throwError "invalid fact for duper, proposition expected {indentExpr fact}"
  return formulas

-- Add the constant `skolemSorry` to the environment.
-- Add suitable postfix to avoid name conflict.
def addSkolemSorry : CoreM Name := do
  let nameS := "skolemSorry"
  let env := (← get).env
  let mut cnt := 0
  let currNameSpace := (← read).currNamespace
  while true do
    let name := Name.num (Name.str currNameSpace nameS) cnt
    if env.constants.contains name then
      cnt := cnt + 1
    else
      break
  let name := Name.num (Name.str currNameSpace nameS) cnt
  let lvlName := `u
  let lvl := Level.param lvlName
  -- Type = ∀ (p : Prop) (n : Nat) (α : Sort u), α
  -- The preceeding ```Prop``` is needed for recording level parameters.
  --   We'll show how it is used using the following example:
  -- Suppose we are clausifying
  --   ``∃ (x : Nat), f (Type u) x = g (Type v) x``
  -- Then the skolem constant should be
  --   ``Skolem.some (fun x => f (Type u) x = g (Type v) x)``
  -- In the ``skolemSorry`` approach without the ```Prop```, the skolem
  --   constant is stored as ```SkolemSorry <id> Nat```, which makes it
  --   difficult to keep track of ``u`` and ``v``. For example, sometimes
  --   superposition can cause a literal to contain two skolem constants
  --   with the same id and different levels. It's cumbersome to
  --   recover the levels, as we have to identify for each skolem constant
  --   in the result clause which parent it's from, and backtrack all the
  --   way to the clause where the skolem was created.
  -- To solve this problem, we record the levels within the ``Prop`` argument.
  --   In the above example, it will be recorded as ```Type u → Type v → opaqueBool```.
  let type := Expr.forallE `p (Expr.sort .zero) (Expr.forallE `n (Expr.const ``Nat []) (
    Expr.forallE `α (Expr.sort lvl) (.bvar 0) .default
  ) .default) .default
  -- Term = fun (p : Prop) (n : Nat) (α : Sort u) => sorryAx.{u} α false
  let term := Expr.lam `p (Expr.sort .zero) (Expr.lam `n (Expr.const ``Nat []) (
    Expr.lam `α (Expr.sort lvl) (
      Expr.app (Expr.app (Expr.const ``sorryAx [lvl]) (.bvar 0)) (Expr.const ``false [])
    ) .default
  ) .default) .default
  -- TODO : Change `unsafe` to `true`
  let opaqueVal : OpaqueVal := {name := name, levelParams := [lvlName],
                                type := type, value := term, isUnsafe := false, all := [name]}
  let decl : Declaration := (.opaqueDecl opaqueVal)
  match (← getEnv).addDecl decl with
  | Except.ok    env => setEnv env
  | Except.error ex  => throwKernelException ex
  return name

syntax (name := duper) "duper" (colGt ident)? ("[" term,* "]")? : tactic

macro_rules
| `(tactic| duper) => `(tactic| duper [])

def runDuper (facts : Syntax.TSepArray `term ",") : TacticM ProverM.State := withNewMCtxDepth do
  let formulas ← collectAssumptions facts.getElems
  -- Add the constant `skolemSorry` to the environment
  let skSorryName ← addSkolemSorry
  trace[Meta.debug] "Formulas from collectAssumptions: {formulas}"
  let (_, state) ←
    ProverM.runWithExprs (ctx := {}) (s := {skolemSorryName := skSorryName})
      ProverM.saturateNoPreprocessingClausification
      formulas
  return state

def evalDuperUnsafe : Tactic
| `(tactic| duper [$facts,*]) => withMainContext do
  let startTime ← IO.monoMsNow
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let state ← runDuper facts
    match state.result with
    | Result.contradiction => do
      IO.println s!"Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
      IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
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
      IO.println s!"{ident} test succeeded in finding a contradiction"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
    | Result.saturated =>
      IO.println s!"{ident} test resulted in prover saturation"
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

-- We save the `CoreM` state. This is because we will add a constant
-- `skolemSorry` to the environment to support skolem constants with
-- universe levels. We want to erase this constant after the saturation
-- procedure ends
def withoutModifyingCoreEnv (m : TacticM α) : TacticM α :=
  try
    let env := (← liftM (get : CoreM Core.State)).env
    let ret ← m
    liftM (modify fun s => {s with env := env} : CoreM Unit)
    return ret
  catch e =>
    throwError e.toMessageData

@[tactic duper]
def evalDuper : Tactic
| `(tactic| $stx) => withoutModifyingCoreEnv <|
  evalDuperUnsafe stx

syntax (name := duper_no_timing) "duper_no_timing" ("[" term,* "]")? : tactic

macro_rules
| `(tactic| duper_no_timing) => `(tactic| duper_no_timing [])

def evalDuperNoTimingUnsafe : Tactic
| `(tactic| duper_no_timing [$facts,*]) => withMainContext do
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let state ← runDuper facts
    match state.result with
    | Result.contradiction => do
      IO.println s!"Contradiction found"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
      IO.println s!"Constructed proof"
    | Result.saturated =>
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

@[tactic duper_no_timing]
def evalDuperNoTiming : Tactic
| `(tactic| $stx) => withoutModifyingCoreEnv <|
  evalDuperNoTimingUnsafe stx

end Lean.Elab.Tactic