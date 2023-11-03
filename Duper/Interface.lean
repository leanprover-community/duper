import Duper.ProofReconstruction

open Lean
open Lean.Meta
open Duper
open ProverM

initialize
  registerTraceClass `Saturate.debug

/-- We save the `CoreM` state. This is because we will add a constant `skolemSorry` to the environment to support skolem constants with
    universe levels. We want to erase this constant after the saturation procedure ends -/
def withoutModifyingCoreEnv (m : MetaM α) : MetaM α :=
  try
    let env := (← liftM (get : CoreM Core.State)).env
    let ret ← m
    liftM (modify fun s => {s with env := env} : CoreM Unit)
    return ret
  catch e =>
    throwError e.toMessageData

/-- Add the constant `skolemSorry` to the environment and add suitable postfix to avoid name conflict. -/
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

def printSaturation (state : ProverM.State) : MetaM Unit := do
  trace[Prover.saturate] "Final Active Set: {state.activeSet.toArray}"
  trace[Saturate.debug] "Final active set numbers: {state.activeSet.toArray.map (fun c => (state.allClauses.find! c).number)}"
  trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
  trace[Saturate.debug] "Verified Inhabited Types: {state.verifiedInhabitedTypes.map (fun x => x.expr)}"
  trace[Saturate.debug] "Verified Nonempty Types: {state.verifiedNonemptyTypes.map (fun x => x.1.expr)}"
  trace[Saturate.debug] "Potentially Uninhabited Types: {state.potentiallyUninhabitedTypes.map (fun x => x.expr)}"
  trace[Saturate.debug] "Potentially Vacuous Clauses: {state.potentiallyVacuousClauses.toArray}"

def formulasToMessageData : Expr × Expr × Array Name → MessageData
| (ty, term, names) => MessageData.compose (.compose m!"{names} @ " m!"{term} : ") m!"{ty}"

/-- Entry point for calling a single instance of duper using the options determined by (← getOptions).

    Formulas should consist of lemmas supplied by the user (to see how to obtain formulas from duper's input syntax, see `collectAssumptions`).
    InstanceMaxHeartbeats should indicate how many heartbeats duper should run for before timing out (if instanceMaxHeartbeats is set to 0,
    then duper will run until it is timed out by the Core `maxHeartbeats` option). If Duper succeeds in deriving a contradiction and constructing
    a proof for it, then `runDuper` returns that proof as an expression. Otherwise, Duper will throw an error. -/
def runDuper (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr := do
  let state ←
    withNewMCtxDepth do
      let formulas ← unfoldDefinitions formulas
      trace[Meta.debug] "Formulas from collectAssumptions: {Duper.ListToMessageData formulas formulasToMessageData}"
      /- `collectAssumptions` should not be wrapped by `withoutModifyingCoreEnv` because new definitional equations might be
          generated during `collectAssumptions` -/
      withoutModifyingCoreEnv <| do
        -- Add the constant `skolemSorry` to the environment
        let skSorryName ← addSkolemSorry
        let (_, state) ←
          ProverM.runWithExprs (ctx := {}) (s := {instanceMaxHeartbeats := instanceMaxHeartbeats, skolemSorryName := skSorryName})
            ProverM.saturateNoPreprocessingClausification
            formulas
        pure state
  match state.result with
  | Result.contradiction => do
    printProof state
    let contradictionProof ← reconstructProof state
    return contradictionProof
  | Result.saturated =>
    printSaturation state
    throwError "Prover saturated."
  | Result.unknown =>
    /- Note: If this error message changes, make sure to edit Tactic.lean since `runDuperPortfolioMode` uses this error message to
       determine whether Duper threw an error due to an actual problem or due to a timeout -/
    throwError "Prover was terminated."

/-- Default duper instance (does not modify any options except inhabitationReasoning if specified) -/
def runDuperInstance0 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  match inhabitationReasoning with
  | none => runDuper formulas instanceMaxHeartbeats
  | some b => withOptions (fun o => o.set `inhabitationReasoning b) $ runDuper formulas instanceMaxHeartbeats

/-- Runs duper with selFunction 4 (which corresponds to Zipperposition's default selection function) -/
def runDuperInstance1 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 4) $ runDuper formulas instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 4).set `inhabitationReasoning b) $ runDuper formulas instanceMaxHeartbeats

/-- Runs duper with selFunction 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel) -/
def runDuperInstance2 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 11) $ runDuper formulas instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 11).set `inhabitationReasoning b) $ runDuper formulas instanceMaxHeartbeats

/-- Runs duper with selFunction 12 (which corresponds to E's SelectCQIPrecWNTNp and Zipperposition's e_sel2) -/
def runDuperInstance3 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 12) $ runDuper formulas instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 12).set `inhabitationReasoning b) $ runDuper formulas instanceMaxHeartbeats

/-- Runs duper with selFunction 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3) -/
def runDuperInstance4 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 13) $ runDuper formulas instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 13).set `inhabitationReasoning b) $ runDuper formulas instanceMaxHeartbeats
