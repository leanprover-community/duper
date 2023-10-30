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
  registerTraceClass `ProofReconstruction
  registerTraceClass `Saturate.debug
  registerTraceClass `Preprocessing.debug
  registerTraceClass `Portfolio.debug

namespace Lean.Elab.Tactic

def getClauseInfo! (state : ProverM.State) (c : Clause) : CoreM ClauseInfo := do
  let some ci := state.allClauses.find? c
    | throwError "clause info not found: {c}"
  return ci

partial def printProof (state : ProverM.State) : MetaM Unit := do
  Core.checkMaxHeartbeats "printProof"
  let rec go c (hm : Array (Nat × Clause) := {}) : MetaM (Array (Nat × Clause)) := do
    let info ← getClauseInfo! state c
    if hm.contains (info.number, c) then return hm
    let mut hm := hm.push (info.number, c)
    for proofParent in info.proof.parents do
      hm ← go proofParent.clause hm
    return hm
  let some emptyClause := state.emptyClause
    | throwError "printProof :: Can't find empty clause in ProverM's state"
  let proofClauses ← go emptyClause
  let proofClauses := proofClauses.qsort (fun (n1, _) => fun (n2, _) => n1 < n2)
  for (_, c) in proofClauses do
    let info ← getClauseInfo! state c
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! state pp.clause)
    let parentIds := parentInfo.map fun info => info.number
    trace[Print_Proof] "Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {c}"
    -- println!  s!"Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {toString (← ppExpr c.toForallExpr)}"

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
  trace[ProofReconstruction] "Request {c.paramNames} ↦ {lvls} for {c}"
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

def PRM.mkLetDecl (fvarId : FVarId) (userName : Name) (type : Expr) (value : Expr) (nonDep := false) (kind : LocalDeclKind := default) : PRM Unit := do
  let lctx := (← get).lctx
  let lctx' := lctx.mkLetDecl fvarId userName type value nonDep kind
  modify fun s => {s with lctx := lctx'}
  modify fun s => {s with fvars := s.fvars.push (mkFVar fvarId)}

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
    let opqn := args[0]!
    let lvls ← runMetaAsPRM <| RuleM.unWrapSort opqn
    let .natVal skid := args[1]!.litValue!
      | throwError "PRM.matchSkolem :: Invalid skolem id!"
    let skTy := args[2]!
    let skmap := (← read).pmstate.skolemMap
    let consk := (← get).constructedSkolems
    if let some isk := skmap.find? skid then
      let trailingArgs := args.extract 3 args.size
      let trailingArgs ← trailingArgs.mapM (fun e => Core.transform e PRM.matchSkolem)
      if let some fvarId := consk.find? skid then
        return .done (mkAppN (mkFVar fvarId) trailingArgs)
      let ⟨skProof, params⟩ := isk
      let skProof := skProof.instantiateLevelParamsArray params lvls
      let skProof ← Core.transform skProof PRM.matchSkolem
      -- Don't need to instantiate level params for `skTy`, because
      --   it's already instantiated
      let skTy ← Core.transform skTy PRM.matchSkolem
      let fvarId ← mkFreshFVarId
      let userName := Name.num `skol skid
      PRM.mkLetDecl fvarId userName skTy skProof
      runMetaAsPRM <| do
        trace[ProofReconstruction] "Reconstructing skolem, {(mkFVar fvarId).dbgToString} ≡≡ {mkFVar fvarId} : {skTy} := {skProof}"
      modify fun s => {s with constructedSkolems := s.constructedSkolems.insert skid fvarId}
      let trailingArgs := args.extract 3 args.size
      let trailingArgs ← trailingArgs.mapM (fun e => Core.transform e PRM.matchSkolem)
      return .done (mkAppN (mkFVar fvarId) trailingArgs)
    else
      throwError "PRM.matchSkolem :: Unable to find skolem {skid} in skolem map!"
  else
    return .continue
| _ => return .continue

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
      parents := parents.push parentPrfFvar
      runMetaAsPRM <| do
        trace[ProofReconstruction] (
          m!"Instantiating parent {parent.clause} ≡≡ {parent.expr} with " ++
          m!"param subst {parent.clause.paramNames} ↦ {instantiatedParentParamSubst}"
        )
      let parentClause := parent.clause.instantiateLevelParamsArray parent.clause.paramNames instantiatedParentParamSubst
      let parentClause ← parentClause.mapMUpdateType (fun e => Core.transform e PRM.matchSkolem)
      let parentExpr := parent.expr.instantiateLevelParamsArray parentClause.paramNames instantiatedParentParamSubst
      -- We need to instantiate `c`'s params with `req`. This is because universe metavariables
      --   might be introduces during unification
      let parentExpr := parentExpr.instantiateLevelParamsArray c.paramNames req
      let parentExpr ← Core.transform parentExpr PRM.matchSkolem
      let instPP := {parent with expr := parentExpr, clause := parentClause}
      instantiatedProofParents := instantiatedProofParents.push instPP
    -- Now `parents[i] : info.proof.parents[i].toForallExpr`, for all `i`
    let instC := c.instantiateLevelParamsArray c.paramNames req
    let instC ← instC.mapMUpdateType (fun e => Core.transform e PRM.matchSkolem)
    runMetaAsPRM <| do 
      trace[ProofReconstruction] (
        m!"Reconstructing proof for #{info.number} " ++
        m!": {instC.paramNames} ↦ {req} @ {instC}, Rule Name: {info.proof.ruleName}"
      )
    let instTr := info.proof.transferExprs.map (fun e => e.instantiateLevelParamsArray c.paramNames req)
    let instTr ← instTr.mapM (fun e => Core.transform e PRM.matchSkolem)
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
      do trace[ProofReconstruction] "#{info.number}'s newProof: {newProof}"
    if cs == [] then return newProof
    -- Add the new proof to the local context
    let fvarId ← mkFreshFVarId
    let declName := (Name.mkNum (Name.mkNum `clause info.number) reqid)
    PRM.mkLetDecl fvarId declName newTarget newProof
    modify fun ctrc => ctrc.insertConstructedClauses (info.number, req) (mkFVar fvarId)
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
  let (e, prstate) ← (do mkClauseProof cs.data).run
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
  let some emptyClause := state.emptyClause
    | throwError "applyProof :: Can't find empty clause in ProverM's state"
  let l := (← collectClauses state emptyClause (#[], Std.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[ProofReconstruction] "Collected clauses: {l}"
  -- First make proof for skolems, then make proof for clauses
  let proof ← mkAllProof state l
  trace[ProofReconstruction] "Proof: {proof}"
  Lean.MVarId.assign (← getMainGoal) proof

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
    | some (.defnInfo defval) =>
      let term := defval.value
      let type ← Meta.inferType term
      let sort ← Meta.reduce (← Meta.inferType type) true true false
      -- If the fact is of sort `Prop`, add itself as a fact
      let mut ret := #[]
      if sort.isProp then
        ret := ret.push (← elabFactAux stx)
      -- Generate definitional equation for the fact
      if let some eqns ← getEqnsFor? expr.constName! (nonRec := true) then
        ret := ret.append (← eqns.mapM fun eq => do elabFactAux (← `($(mkIdent eq))))
      return ret
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
    let abstres ← Duper.abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return (← inferType e, e, paramNames)

def collectAssumptions (facts : Array Term) : TacticM (List (Expr × Expr × Array Name)) := do
  let mut formulas := []
  -- Load all local decls:
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← Lean.FVarId.getDecl fVarId
    unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
      let ldecltype ← preprocessFact (← instantiateMVars ldecl.type)
      formulas := (ldecltype, ← mkAppM ``eq_true #[mkFVar fVarId], #[]) :: formulas
  -- load user-provided facts
  for facts in ← facts.mapM elabFact do
    for (fact, proof, params) in facts do
      if ← isProp fact then
        let fact ← preprocessFact (← instantiateMVars fact)
        formulas := (fact, ← mkAppM ``eq_true #[proof], params) :: formulas
      else
        throwError "invalid fact for duper, proposition expected {indentExpr fact}"
  return formulas

def collectedAssumptionToMessageData : Expr × Expr × Array Name → MessageData
| (ty, term, names) => MessageData.compose (.compose m!"{names} @ " m!"{term} : ") m!"{ty}"

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

-- Add the constant `skolemSorry` to the environment.
-- Add suitable postfix to avoid name conflict.
def addSkolemSorry : CoreM Name := do
  let nameS := "skS"
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
  trace[Meta.debug] "Created Skolem Sorry, name = {name}"
  let vlvlName := `v
  let vlvl := Level.param vlvlName
  let ulvlName := `u
  let ulvl := Level.param ulvlName
  -- Type = ∀ (p : Sort v) (n : Nat) (α : Sort u), α
  -- The preceeding ```Sort v``` is needed for recording level parameters.
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
  -- To solve this problem, we record the levels within the ``p`` argument.
  --   In the above example, it will be recorded as ```Type u → Type v → Type```.
  let type := Expr.forallE `p (Expr.sort vlvl) (Expr.forallE `n (Expr.const ``Nat []) (
    Expr.forallE `α (Expr.sort ulvl) (.bvar 0) .implicit
  ) .default) .implicit
  -- Term = fun (p : Nat) (n : Nat) (α : Sort u) => sorryAx.{u} α false
  let term := Expr.lam `p (Expr.sort vlvl) (Expr.lam `n (Expr.const ``Nat []) (
    Expr.lam `α (Expr.sort ulvl) (
      Expr.app (Expr.app (Expr.const ``sorryAx [ulvl]) (.bvar 0)) (Expr.const ``false [])
    ) .implicit
  ) .default) .implicit
  let opaqueVal : OpaqueVal := {name := name, levelParams := [vlvlName, ulvlName],
                                type := type, value := term, isUnsafe := true, all := [name]}
  let decl : Declaration := (.opaqueDecl opaqueVal)
  match (← getEnv).addDecl decl with
  | Except.ok    env => setEnv env
  | Except.error ex  => throwKernelException ex
  return name

def unfoldDefinitions (formulas : List (Expr × Expr × Array Name)) : MetaM (List (Expr × Expr × Array Name)) := do
  withTransparency .reducible do
    let mut newFormulas := formulas
    for (e, proof, paramNames) in formulas do
      let update (ty lhs rhs : Expr) newFormulas (containedIn : Expr → Bool) : MetaM _ := do
        if containedIn rhs then pure newFormulas else
          newFormulas.mapM fun (f, fproof, fparamNames) => do
            if !containedIn f then
              return (f, fproof, fparamNames)
            else
              let us ← paramNames.mapM fun _ => mkFreshLevelMVar
              let lhs'   := lhs.instantiateLevelParamsArray paramNames us
              let ty'    := ty.instantiateLevelParamsArray paramNames us
              let rhs'   := rhs.instantiateLevelParamsArray paramNames us
              -- proof has the form: `eq_true h : fact = True` where `h : fact`
              let proof' ← Meta.mkAppM ``of_eq_true #[proof.instantiateLevelParamsArray paramNames us]
              let abstracted ← Meta.kabstract f lhs'
              let f := abstracted.instantiate1 rhs'
              let fproof ← withTransparency .default do mkAppOptM ``Eq.ndrec #[none,
                some lhs,
                some $ mkLambda `x .default ty' (← Meta.mkAppM ``Eq #[abstracted, mkConst ``True]),
                some fproof,
                rhs',
                proof']
              return (f, ← instantiateMVars $ fproof, fparamNames)
      match e with
      | .app ( .app ( .app (.const ``Eq _) ty) (.fvar fid)) rhs =>
        let containedIn := fun e => (e.find? (· == .fvar fid)).isSome
        newFormulas ← update ty (.fvar fid) rhs newFormulas containedIn
      | .app ( .app ( .app (.const ``Eq _) ty) (.const cname lvls)) rhs =>
        let containedIn := fun e => (e.find? (·.isConstOf cname)).isSome
        newFormulas ← update ty (.const cname lvls) rhs newFormulas containedIn
      | _ => pure ()
    return newFormulas

/-- Entry point for calling duper. Facts should consist of lemmas supplied by the user, instanceMaxHeartbeats should indicate how many
    heartbeats duper should run for before timing out (if instanceMaxHeartbeats is set to 0, then duper will run until it is timed out
    by the Core `maxHeartbeats` option). -/
def runDuper (facts : Syntax.TSepArray `term ",") (instanceMaxHeartbeats : Nat) : TacticM ProverM.State := withNewMCtxDepth do
  let formulas ← collectAssumptions facts.getElems
  let formulas ← unfoldDefinitions formulas
  trace[Meta.debug] "Formulas from collectAssumptions: {Duper.ListToMessageData formulas collectedAssumptionToMessageData}"
  /- `collectAssumptions` should not be wrapped by `withoutModifyingCoreEnv` because new definitional equations might be
      generated during `collectAssumptions` -/
  withoutModifyingCoreEnv <| do
    -- Add the constant `skolemSorry` to the environment
    let skSorryName ← addSkolemSorry
    let (_, state) ←
      ProverM.runWithExprs (ctx := {}) (s := {instanceMaxHeartbeats := instanceMaxHeartbeats, skolemSorryName := skSorryName})
        ProverM.saturateNoPreprocessingClausification
        formulas
    return state

/-- Default duper instance (does not modify any options except inhabitationReasoning if specified) -/
def runDuperInstance0 (facts : Syntax.TSepArray `term ",") (inhabitationReasoning : Option Bool)
  (instanceMaxHeartbeats : Nat) : TacticM ProverM.State :=
  match inhabitationReasoning with
  | none => runDuper facts instanceMaxHeartbeats
  | some b => withOptions (fun o => o.set `inhabitationReasoning b) $ runDuper facts instanceMaxHeartbeats

/-- Runs duper with selFunction 4 (which corresponds to Zipperposition's default selection function) -/
def runDuperInstance1 (facts : Syntax.TSepArray `term ",") (inhabitationReasoning : Option Bool)
  (instanceMaxHeartbeats : Nat) : TacticM ProverM.State :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 4) $ runDuper facts instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 4).set `inhabitationReasoning b) $ runDuper facts instanceMaxHeartbeats

/-- Runs duper with selFunction 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel) -/
def runDuperInstance2 (facts : Syntax.TSepArray `term ",") (inhabitationReasoning : Option Bool)
  (instanceMaxHeartbeats : Nat) : TacticM ProverM.State :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 11) $ runDuper facts instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 11).set `inhabitationReasoning b) $ runDuper facts instanceMaxHeartbeats

/-- Runs duper with selFunction 12 (which corresponds to E's SelectCQIPrecWNTNp and Zipperposition's e_sel2) -/
def runDuperInstance3 (facts : Syntax.TSepArray `term ",") (inhabitationReasoning : Option Bool)
  (instanceMaxHeartbeats : Nat) : TacticM ProverM.State :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 12) $ runDuper facts instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 12).set `inhabitationReasoning b) $ runDuper facts instanceMaxHeartbeats

/-- Runs duper with selFunction 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3) -/
def runDuperInstance4 (facts : Syntax.TSepArray `term ",") (inhabitationReasoning : Option Bool)
  (instanceMaxHeartbeats : Nat) : TacticM ProverM.State :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 13) $ runDuper facts instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 13).set `inhabitationReasoning b) $ runDuper facts instanceMaxHeartbeats

def printSaturation (state : ProverM.State) : TacticM Unit := do
  trace[Prover.saturate] "Final Active Set: {state.activeSet.toArray}"
  trace[Saturate.debug] "Final active set numbers: {state.activeSet.toArray.map (fun c => (state.allClauses.find! c).number)}"
  trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
  trace[Saturate.debug] "Verified Inhabited Types: {state.verifiedInhabitedTypes.map (fun x => x.expr)}"
  trace[Saturate.debug] "Verified Nonempty Types: {state.verifiedNonemptyTypes.map (fun x => x.1.expr)}"
  trace[Saturate.debug] "Potentially Uninhabited Types: {state.potentiallyUninhabitedTypes.map (fun x => x.expr)}"
  trace[Saturate.debug] "Potentially Vacuous Clauses: {state.potentiallyVacuousClauses.toArray}"

def getMaxHeartbeats : CoreM Nat := return (← read).maxHeartbeats

declare_syntax_cat Duper.bool_lit (behavior := symbol)

syntax "true" : Duper.bool_lit
syntax "false" : Duper.bool_lit

def elabBoolLit [Monad m] [MonadError m] (stx : TSyntax `Duper.bool_lit) : m Bool :=
  withRef stx do
    match stx with
    | `(bool_lit| true) => return true
    | `(bool_lit| false) => return false
    | _ => throwUnsupportedSyntax

def boolToBoolLit [Monad m] [MonadQuotation m] (b : Bool) : m (TSyntax `Duper.bool_lit) := do
  match b with
  | true => `(bool_lit| true)
  | false => `(bool_lit| false)

declare_syntax_cat Duper.configOption (behavior := symbol)

syntax (&"portfolioMode" " := " Duper.bool_lit) : Duper.configOption
syntax (&"portfolioInstance" " := " numLit) : Duper.configOption
syntax (&"inhabitationReasoning" " := " Duper.bool_lit) : Duper.configOption

structure ConfigurationOptions where
  portfolioMode : Bool -- True by default (unless portfolio instance is specified)
  portfolioInstance : Option Nat -- None by default (unless portfolioMode is false, in which case, some 0 is default)
  inhabitationReasoning : Option Bool -- None by default

syntax (name := duper) "duper" (ppSpace "[" term,* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic
syntax (name := duperTrace) "duper?" (ppSpace "[" term,* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic

macro_rules
| `(tactic| duper) => `(tactic| duper [] {}) -- Missing both facts and config options
| `(tactic| duper [$facts,*]) => `(tactic| duper [$facts,*] {}) -- Mising just config options
| `(tactic| duper {$configOptions,*}) => `(tactic| duper [] {$configOptions,*}) -- Missing just facts

macro_rules
| `(tactic| duper?) => `(tactic| duper? [] {}) -- Missing both facts and config options
| `(tactic| duper? [$facts,*]) => `(tactic| duper? [$facts,*] {}) -- Mising just config options
| `(tactic| duper? {$configOptions,*}) => `(tactic| duper? [] {$configOptions,*}) -- Missing just facts

/-- Determines what configuration options Duper should use based on a (potentially partial) set of configuration options passed in by
    the user. If configuration options are not fully specified, this function gives the following default options:
    - Enables portfolio mode by default unless a portfolio instance is specified
    - Sets the portfolio instance to 0 by default if portfolio mode is explicitly disabled and no instance is specified
    - Sets inhabitationReasoning to none by default (which means each instance will use the inhabitationReasoning option determined by set_option)

    Additionally, this function throws an error is the user attempts to explicitly enable portfolio mode and specify a portfolio instance. -/
def parseConfigOptions [Monad m] [MonadError m] (configOptionsStx : TSyntaxArray `Duper.configOption) : m ConfigurationOptions := do
  let mut portfolioModeOpt : Option Bool := none
  let mut portfolioInstanceOpt : Option Nat := none
  let mut inhabitationReasoningOpt : Option Bool := none
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(configOption| portfolioMode := $portfolioModeStx:Duper.bool_lit) =>
      if portfolioModeOpt.isSome then
        throwError "Erroneous invocation of duper: The portfolio mode option has been specified multiple times"
      let portfolioMode ← elabBoolLit portfolioModeStx
      if portfolioMode && portfolioInstanceOpt.isSome then
        throwError "Ambiguous invocation of duper. Cannot run duper with portfolio mode enabled and with a particular instance specified"
      portfolioModeOpt := some portfolioMode
    | `(configOption| portfolioInstance := $portfolioInstanceStx) =>
      if portfolioInstanceOpt.isSome then
        throwError "Erroneous invocation of duper: The portfolio instance option has been specified multiple times"
      if portfolioModeOpt == some true then
        throwError "Ambiguous invocation of duper. Cannot run duper with portfolio mode enabled and with a particular instance specified"
      let portfolioInstance := portfolioInstanceStx.getNat
      portfolioInstanceOpt := some portfolioInstance
    | `(configOption| inhabitationReasoning := $inhabitationReasoningStx:Duper.bool_lit) =>
      if inhabitationReasoningOpt.isSome then
        throwError "Erroneous invocation of duper: The inhabitation reasoning option has been specified multiple times"
      let inhabitationReasoning ← elabBoolLit inhabitationReasoningStx
      inhabitationReasoningOpt := some inhabitationReasoning
    | _ => throwUnsupportedSyntax
  let portfolioMode :=
    match portfolioModeOpt with
    | none =>
      match portfolioInstanceOpt with
      | none => true -- If neither portfolioMode nor portfolioInstance are specified, then portfolioMode should be enabled
      | some _ => false -- If portfolioInstance is specified then portfolioMode should be disabled
    | some portfolioMode => portfolioMode
  let portfolioInstance :=
    match portfolioInstanceOpt with
    | some portfolioInstance => some portfolioInstance
    | none =>
      if portfolioMode then none -- If portfolio mode is enabled then no portfolio instance should be specified
      else some 0 -- If portfolio mode was explicitly disabled and no portfolio instance was specified, choose instance 0 by default
  return {portfolioMode := portfolioMode, portfolioInstance := portfolioInstance, inhabitationReasoning := inhabitationReasoningOpt}

/-- If `n` is a Nat that corresponds to one of Duper's portfolio instances, then `portfolioInstanceToConfigOptionStx n` returns the
    syntax object corresponding to `portfolioInstance := n`. This is necessary so that `duper?` can produce its suggestion. -/
def portfolioInstanceToConfigOptionStx [Monad m] [MonadError m] [MonadQuotation m] (n : Nat) : m (TSyntax `Duper.configOption) := do
  match n with
  | 0 => `(configOption| portfolioInstance := 0)
  | 1 => `(configOption| portfolioInstance := 1)
  | 2 => `(configOption| portfolioInstance := 2)
  | 3 => `(configOption| portfolioInstance := 3)
  | 4 => `(configOption| portfolioInstance := 4)
  | _ => throwError "Invalid Duper instance {n}"

/-- Constructs and suggests the syntax for a duper call, for use with `duper?` -/
def mkDuperCallSuggestion (duperStxRef : Syntax) (origSpan : Syntax) (facts : Syntax.TSepArray `term ",")
  (portfolioInstance : Nat) (inhabitationReasoning : Option Bool) : TacticM Unit := do
  let mut configOptionsArr : Array Syntax := #[] -- An Array containing configuration option elements and separators (",")
  let portfolioInstanceStx ← portfolioInstanceToConfigOptionStx portfolioInstance
  configOptionsArr := configOptionsArr.push portfolioInstanceStx

  match inhabitationReasoning with
  | none => pure ()
  | some b =>
    let inhabitationReasoningStx ← boolToBoolLit b
    configOptionsArr := configOptionsArr.push (mkAtom ",") -- Add separator before each additional element
    configOptionsArr := configOptionsArr.push $ ← `(configOption| inhabitationReasoning := $inhabitationReasoningStx)

  let configOptionsStx : Syntax.TSepArray `Duper.configOption "," := {elemsAndSeps := configOptionsArr}
  let suggestion ←`(tactic| duper [$facts,*] {$configOptionsStx,*})
  Std.Tactic.TryThis.addSuggestion duperStxRef suggestion (origSpan? := origSpan)

/-- Implements duper calls when portfolio mode is enabled. If `duperStxInfo` is not none and `runDuperPortfolioMode` succeeds in deriving
    a contradiction, then `Std.Tactic.TryThis.addSuggestion` will be used to give the user a more specific invocation of duper that can
    reproduce the proof (without having to run duper in portfolio mode) -/
def runDuperPortfolioMode (facts : Syntax.TSepArray `term ",") (configOptions : ConfigurationOptions)
  (startTime : Nat) (duperStxInfo : Option (Syntax × Syntax)) : TacticM Unit := do
  let maxHeartbeats ← getMaxHeartbeats
  let instances :=
    #[(0, runDuperInstance0 facts),
      (1, runDuperInstance1 facts),
      (2, runDuperInstance2 facts),
      (3, runDuperInstance3 facts),
      (4, runDuperInstance4 facts)]
  let numInstances := instances.size
  let maxInstanceHeartbeats := maxHeartbeats / numInstances -- Allocate total heartbeats among all instances
  let mut inhabitationReasoningEnabled : Bool :=
    match configOptions.inhabitationReasoning with
    | some true => true
    | some false => false
    | none => false -- If inhabitationReasoning is not specified, disable it unless it becomes clear it is needed
  for (duperInstanceNum, duperInstanceFn) in instances do
    let state ← duperInstanceFn inhabitationReasoningEnabled maxInstanceHeartbeats
    match state.result with
    | Result.contradiction => do
      let timeToFindContradiction := (← IO.monoMsNow) - startTime
      printProof state
      let successfulProofReconstruction ←
        try
          applyProof state
          pure true
        catch e =>
          if (← e.toMessageData.toString).startsWith "instantiatePremises :: Failed to find instance for" then
            if inhabitationReasoningEnabled then
              throw e -- Throw the error rather than try to continue because inhabitation reasoning is already enabled
            else if configOptions.inhabitationReasoning = some false then
              IO.println "Duper determined that this problem requires inhabitation reasoning"
              throw e -- Throw the error rather than try to continue because the user explicitly specified that inhabitation reasoning should be disabled
            else
              pure false -- Attempting to solve this problem with inhabitation reasoning disabled leads to failed proof reconstruction
          else
            throw e -- Throw the error because it doesn't appear to pertain to inhabitation reasoning
      if successfulProofReconstruction then
        IO.println s!"Contradiction found by instance {duperInstanceNum}. Time: {timeToFindContradiction}ms"
        IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
        match duperStxInfo with
        | none => return
        | some (duperStxRef, origSpan) =>
          mkDuperCallSuggestion duperStxRef origSpan facts duperInstanceNum inhabitationReasoningEnabled
          return
      else
        -- Attempting to solve this problem with inhabitation reasoning disabled leads to failed proof reconstruction
        inhabitationReasoningEnabled := true
        IO.println "Duper determined that this problem requires inhabitation reasoning, continuing portfolio mode with it enabled"
        -- Retry the portfolio instance that was able to find a proof when inhabitation reasoning was disabled
        let state ← duperInstanceFn inhabitationReasoningEnabled maxInstanceHeartbeats
        match state.result with
        | Result.contradiction => do
          let timeToFindContradiction := (← IO.monoMsNow) - startTime
          printProof state
          applyProof state
          IO.println s!"Contradiction found by instance {duperInstanceNum}. Time: {timeToFindContradiction}ms"
          IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
          match duperStxInfo with
          | none => return
          | some (duperStxRef, origSpan) =>
            mkDuperCallSuggestion duperStxRef origSpan facts duperInstanceNum inhabitationReasoningEnabled
            return
        | Result.saturated =>
          -- Since inhabitationReasoning has been enabled, the fact that this instance has been saturated means all instances should saturate
          /- Note: The above is currently true because there are presently no portfolio instances that disable hoist rules, fluid sup, or
             the higher order unification procedure. Once that changes, this code will need to be edited. -/
          printSaturation state
          throwError "Prover saturated."
        | Result.unknown => continue -- Instance ran out of time
    | Result.saturated =>
      if inhabitationReasoningEnabled then
        -- Since inhabitationReasoning has been enabled, the fact that this instance has been saturated means all instances should saturate
        /- Note: The above is currently true because there are presently no portfolio instances that disable hoist rules, fluid sup, or
           the higher order unification procedure. Once that changes, this code will need to be edited. -/
        printSaturation state
        throwError "Prover saturated."
      else if configOptions.inhabitationReasoning = some false then
        -- Since inhabitationReasoning has been enabled, the fact that this instance has been saturated means all instances should saturate
        /- Note: The above is currently true because there are presently no portfolio instances that disable hoist rules, fluid sup, or
           the higher order unification procedure. Once that changes, this code will need to be edited. -/
        IO.println "Duper determined that this problem may require inhabitation reasoning"
        printSaturation state
        -- Throw the error rather than try to continue because the user explicitly specified that inhabitation reasoning should be disabled
        throwError "Prover saturated."
      else
        /- Duper may have saturated because it can't solve the problem, or it may have saturated because the problem requires inhabitation
           reasoning. Choosing to proceed -/
        inhabitationReasoningEnabled := true
        IO.println "Duper determined that this problem may require inhabitation reasoning, continuing portfolio mode with it enabled"
        -- Retry the portfolio instance that was able to find a proof when inhabitation reasoning was disabled
        let state ← duperInstanceFn inhabitationReasoningEnabled maxInstanceHeartbeats
        match state.result with
        | Result.contradiction => do
          let timeToFindContradiction := (← IO.monoMsNow) - startTime
          printProof state
          applyProof state
          IO.println s!"Contradiction found by instance {duperInstanceNum}. Time: {timeToFindContradiction}ms"
          IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
          match duperStxInfo with
          | none => return
          | some (duperStxRef, origSpan) =>
            mkDuperCallSuggestion duperStxRef origSpan facts duperInstanceNum inhabitationReasoningEnabled
            return
        | Result.saturated =>
          -- Since inhabitationReasoning has been enabled, the fact that this instance has been saturated means all instances should saturate
          /- Note: The above is currently true because there are presently no portfolio instances that disable hoist rules, fluid sup, or
             the higher order unification procedure. Once that changes, this code will need to be edited. -/
          printSaturation state
          throwError "Prover saturated."
        | Result.unknown => continue -- Instance ran out of time
    | Result.unknown => continue -- Instance ran out of time
  throwError "Prover ran out of time before solving the goal"

@[tactic duper]
def evalDuper : Tactic
| `(tactic| duper [$facts,*] {$configOptions,*}) => withMainContext do
  let startTime ← IO.monoMsNow
  let configOptions ← parseConfigOptions configOptions
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    if configOptions.portfolioMode then
      runDuperPortfolioMode facts configOptions startTime none
    else
      let portfolioInstance ←
        match configOptions.portfolioInstance with
        | some portfolioInstance => pure portfolioInstance
        | none => throwError "parseConfigOptions error: portfolio mode is disabled and no portfolio instance is specified"
      let state ←
        match portfolioInstance with
        | 0 => runDuperInstance0 facts configOptions.inhabitationReasoning 0
        | 1 => runDuperInstance1 facts configOptions.inhabitationReasoning 0
        | 2 => runDuperInstance2 facts configOptions.inhabitationReasoning 0
        | 3 => runDuperInstance3 facts configOptions.inhabitationReasoning 0
        | 4 => runDuperInstance4 facts configOptions.inhabitationReasoning 0
        | _ => throwError "Portfolio instance {portfolioInstance} not currently defined. Please choose instance 0-4"
      match state.result with
      | Result.contradiction => do
        IO.println s!"Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
        printProof state
        applyProof state
        IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
      | Result.saturated =>
        printSaturation state
        throwError "Prover saturated."
      | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

@[tactic duperTrace]
def evalDuperTrace : Tactic
| `(tactic| duper?%$duperStxRef [$facts,*] {$configOptions,*}) => withMainContext do
  let startTime ← IO.monoMsNow
  let configOptions ← parseConfigOptions configOptions
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    if configOptions.portfolioMode then
      runDuperPortfolioMode facts configOptions startTime (some (duperStxRef, ← getRef))
    else
      let portfolioInstance ←
        match configOptions.portfolioInstance with
        | some portfolioInstance => pure portfolioInstance
        | none => throwError "parseConfigOptions error: portfolio mode is disabled and no portfolio instance is specified"
      let state ←
        match portfolioInstance with
        | 0 => runDuperInstance0 facts configOptions.inhabitationReasoning 0
        | 1 => runDuperInstance1 facts configOptions.inhabitationReasoning 0
        | 2 => runDuperInstance2 facts configOptions.inhabitationReasoning 0
        | 3 => runDuperInstance3 facts configOptions.inhabitationReasoning 0
        | 4 => runDuperInstance4 facts configOptions.inhabitationReasoning 0
        | _ => throwError "Portfolio instance {portfolioInstance} not currently defined. Please choose instance 0-4"
      match state.result with
      | Result.contradiction => do
        IO.println s!"Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
        printProof state
        applyProof state
        IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
        mkDuperCallSuggestion duperStxRef (← getRef) facts portfolioInstance configOptions.inhabitationReasoning
      | Result.saturated =>
        printSaturation state
        throwError "Prover saturated."
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
    let state ← runDuper facts 0
    match state.result with
    | Result.contradiction => do
      IO.println s!"Contradiction found"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      -- printProof state
      applyProof state
      IO.println s!"Constructed proof"
    | Result.saturated =>
      trace[Prover.saturate] "Final Active Set: {state.activeSet.toArray}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic