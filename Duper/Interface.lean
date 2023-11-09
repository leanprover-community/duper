import Std.Lean.CoreM
import Duper.ProofReconstruction
import Auto.Tactic

open Lean
open Lean.Meta
open Duper
open ProverM
open Lean.Parser

initialize
  registerTraceClass `Saturate.debug
  registerTraceClass `Portfolio.debug
  registerTraceClass `Monomorphization.debug

register_option printPortfolioInstance : Bool := {
  defValue := false
  descr := "Whether to print the portfolio instance that solved the proof"
}

register_option throwPortfolioErrors : Bool := {
  defValue := false
  descr := "Whether to halt portfolio mode and throw an error if a subinstance throws an error"
}

def getPrintPortfolioInstance (opts : Options) : Bool :=
  printPortfolioInstance.get opts

def getThrowPortfolioErrors (opts : Options) : Bool :=
  throwPortfolioErrors.get opts

def getPrintPortfolioInstanceM : CoreM Bool := do
  let opts ← getOptions
  return getPrintPortfolioInstance opts

def getThrowPortfolioErrorsM : CoreM Bool := do
  let opts ← getOptions
  return getThrowPortfolioErrors opts

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

/- Note for converting between Duper's formulas format and Auto's lemmas format. If `hp : p`, then Duper stores the formula
   `(p, eq_true hp, #[])` whereas Auto stores the lemma `⟨hp, p, #[]⟩`. Importantly, Duper stores the proof of `p = True` and
   Auto stores the proof of `p`, so this must be accounted for in the conversion (maybe later, it will be good to refactor Duper
   to be in alignment with how Auto stores lemmas to avoid the unnecessary cost of this conversion, but for now, it suffices to
   add or remove `eq_true` as needed) -/

/-- Converts formulas/lemmas from the format used by Duper to the format used by Auto. -/
def formulasToAutoLemmas (formulas : List (Expr × Expr × Array Name)) : MetaM (Array Auto.Lemma) :=
  formulas.toArray.mapM
    (fun (fact, proof, params) =>
      return {proof := ← Meta.mkAppM ``of_eq_true #[proof], type := fact, params := params})

/-- Converts formulas/lemmas from the format used by Auto to the format used by Duper. -/
def autoLemmasToFormulas (lemmas : Array Auto.Lemma) : MetaM (List (Expr × Expr × Array Name)) :=
  lemmas.toList.mapM (fun lem => return (lem.type, ← Meta.mkAppM ``eq_true #[lem.proof], lem.params))

/-- Given `formulas`, `instanceMaxHeartbeats`, and an instance of Duper `inst`, runs `inst` with monomorphization preprocessing. -/
def runDuperInstanceWithMonomorphization (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat)
  (inst : List (Expr × Expr × Array Name) → Nat → MetaM Expr) : MetaM Expr := do
  let lemmas ← formulasToAutoLemmas formulas
  -- Calling Auto.unfoldConstAndPreprocessLemma is an essential step for the monomorphization procedure
  let lemmas ← lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[])
  let inhFacts ← Auto.Inhabitation.getInhFactsFromLCtx
  let prover : Array Auto.Lemma → MetaM Expr :=
    fun lemmas => do
      let monomorphizedFormulas ← autoLemmasToFormulas lemmas
      trace[Monomorphization.debug] "Original formulas: {formulas}"
      trace[Monomorphization.debug] "Lemmas (translated from formulas): {lemmas}"
      trace[Monomorphization.debug] "Monomorphized formulas: {monomorphizedFormulas}"
      inst monomorphizedFormulas instanceMaxHeartbeats
  Auto.monoInterface lemmas inhFacts prover

/-- This is a special instance that does not modify any options and is not called by portfolio mode. It is used to allow
    the user to manually specify configuration options. -/
def runDuperInstance0 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat)
  (inhabitationReasoning : Option Bool) (monomorphization : Option Bool) (includeExpensiveRules : Option Bool)
  (selFunction : Option Nat) : MetaM Expr :=
  let addInhabitationReasoningOption : MetaM Expr → MetaM Expr :=
    match inhabitationReasoning with
    | some b => fun inst => withOptions (fun o => o.set `inhabitationReasoning b) inst
    | none => id
  let addIncludeExpensiveRulesOption : MetaM Expr → MetaM Expr :=
    match includeExpensiveRules with
    | some b => fun inst => withOptions (fun o => o.set `includeExpensiveRules b) inst
    | none => id
  let addSelFunctionOption : MetaM Expr → MetaM Expr :=
    match selFunction with
    | some n => fun inst => withOptions (fun o => o.set `selFunction n) inst
    | none => id
  match monomorphization with
  | some true =>
    addInhabitationReasoningOption ∘ addIncludeExpensiveRulesOption ∘ addSelFunctionOption $
      runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats runDuper
  | _ => -- Treat both `some false` and `none` as an indication that monomorphization should be disabled
    addInhabitationReasoningOption ∘ addIncludeExpensiveRulesOption ∘ addSelFunctionOption $
      runDuper formulas instanceMaxHeartbeats

/-- First instance called by portfolio mode. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance1 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning false).set `selFunction 4).set `includeExpensiveRules false)
        (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 1 except inhabitation reasoning is enabled. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance2 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning true).set `selFunction 4).set `includeExpensiveRules false)
        (runDuper formulas instanceMaxHeartbeats)

/-- Second instance called by portfolio mode. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance3 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning false).set `selFunction 11).set `includeExpensiveRules true)
        (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 3 except inhabitation reasoning is enabled. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance4 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning true).set `selFunction 11).set `includeExpensiveRules true)
        (runDuper formulas instanceMaxHeartbeats)

/-- Third instance called by portfolio mode. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance5 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning false).set `selFunction 13).set `includeExpensiveRules false)
        (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 5 except inhabitation reasoning is enabled. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance6 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning true).set `selFunction 13).set `includeExpensiveRules false)
        (runDuper formulas instanceMaxHeartbeats)

/-- Fourth instance called by portfolio mode. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance7 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning true).set `selFunction 2).set `includeExpensiveRules true)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 7 except inhabitation reasoning is disabled. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance8 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning false).set `selFunction 2).set `includeExpensiveRules true)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 1 except monomorphization is disabled. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance9 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning false).set `selFunction 4).set `includeExpensiveRules false)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 2 except monomorphization is disabled. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance10 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning true).set `selFunction 4).set `includeExpensiveRules false)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 3 except monomorphization is disabled. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance11 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning false).set `selFunction 11).set `includeExpensiveRules true)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 4 except monomorphization is disabled. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance12 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning true).set `selFunction 11).set `includeExpensiveRules true)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 5 except monomorphization is disabled. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance13 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning false).set `selFunction 13).set `includeExpensiveRules false)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 6 except monomorphization is disabled. Has the following options:
    - monomorphization = false
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance14 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  withOptions
    (fun o => ((o.set `inhabitationReasoning true).set `selFunction 13).set `includeExpensiveRules false)
    (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 7 except monomorphization is enabled. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance15 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning true).set `selFunction 2).set `includeExpensiveRules true)
        (runDuper formulas instanceMaxHeartbeats)

/-- Same as duper instance 8 except monomorphization is enabled. Has the following options:
    - monomorphization = true
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance16 (formulas : List (Expr × Expr × Array Name)) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats $
    fun formulas instanceMaxHeartbeats =>
      withOptions
        (fun o => ((o.set `inhabitationReasoning false).set `selFunction 2).set `includeExpensiveRules true)
        (runDuper formulas instanceMaxHeartbeats)

/-- Returns true iff the given duper instance `n` has inhabitation reasoning enabled. Returns false iff the given duper instance
    `n` has inhabitation reasoning disabled. Throws an error if given an invalid duper instance. -/
def instanceHasInhabitationReasoning [Monad m] [MonadError m] (n : Nat) : m Bool := do
  match n with
  | 0 => throwError "instanceHasInhabitationReasoning should not be given instance 0. Instance 0 not meant to be used with portfolio mode"
  | 1 => return false
  | 2 => return true
  | 3 => return false
  | 4 => return true
  | 5 => return false
  | 6 => return true
  | 7 => return true
  | 8 => return false
  | 9 => return false
  | 10 => return true
  | 11 => return false
  | 12 => return true
  | 13 => return false
  | 14 => return true
  | 15 => return true
  | 16 => return false
  | _ => throwError "Invalid duper instance {n}"

/-- If the given duper instance `n` has inhabitation reasoning disabled and there is another instance `m` that is identical
    except that it has inhabitation reasoning enabled, then `getInstanceWithInhabitationReasoning` returns `some m`. Otherwise,
    `getInstanceWithInhabitationReasoning` returns `none`. -/
def getInstanceWithInhabitationReasoning (n : Nat) : Option (Nat × (List (Expr × Expr × Array Name) → Nat → MetaM Expr)) := do
  match n with
  | 1 => some (2, runDuperInstance2)
  | 3 => some (4, runDuperInstance4)
  | 5 => some (6, runDuperInstance6)
  | 8 => some (7, runDuperInstance7)
  | 9 => some (10, runDuperInstance10)
  | 11 => some (12, runDuperInstance12)
  | 13 => some (14, runDuperInstance14)
  | 16 => some (15, runDuperInstance15)
  | _ => none

declare_syntax_cat Duper.bool_lit (behavior := symbol)

syntax "true" : Duper.bool_lit
syntax "false" : Duper.bool_lit

def elabBoolLit [Monad m] [MonadError m] (stx : TSyntax `Duper.bool_lit) : m Bool :=
  withRef stx do
    match stx with
    | `(bool_lit| true) => return true
    | `(bool_lit| false) => return false
    | _ => Elab.throwUnsupportedSyntax

def boolToBoolLit [Monad m] [MonadQuotation m] (b : Bool) : m (TSyntax `Duper.bool_lit) := do
  match b with
  | true => `(bool_lit| true)
  | false => `(bool_lit| false)

declare_syntax_cat Duper.configOption (behavior := symbol)

syntax (&"portfolioMode" " := " Duper.bool_lit) : Duper.configOption
syntax (&"portfolioInstance" " := " numLit) : Duper.configOption
syntax (&"inhabitationReasoning" " := " Duper.bool_lit) : Duper.configOption
syntax (&"monomorphization" " := " Duper.bool_lit) : Duper.configOption
syntax (&"includeExpensiveRules" " := " Duper.bool_lit) : Duper.configOption
syntax (&"selFunction" " := " numLit) : Duper.configOption

structure ConfigurationOptions where
  portfolioMode : Bool -- True by default (unless portfolio instance is specified)
  portfolioInstance : Option Nat -- None by default (unless portfolioMode is false, in which case, some 0 is default)
  inhabitationReasoning : Option Bool -- None by default
  monomorphization : Option Bool -- None by default
  includeExpensiveRules : Option Bool -- None by default
  selFunction : Option Nat -- None by default

syntax duperStar := "*"
syntax (name := duper) "duper" (ppSpace "[" (duperStar <|> term),* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic
syntax (name := duperTrace) "duper?" (ppSpace "[" (duperStar <|> term),* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic

/-- If `n` is a Nat that corresponds to one of Duper's portfolio instances, then `portfolioInstanceToConfigOptionStx n` returns the
    syntax object corresponding to `portfolioInstance := n`. This is necessary so that `duper?` can produce its suggestion. -/
def portfolioInstanceToConfigOptionStx [Monad m] [MonadError m] [MonadQuotation m] (n : Nat) : m (TSyntax `Duper.configOption) := do
  match n with
  | 0 => `(configOption| portfolioInstance := 0)
  | 1 => `(configOption| portfolioInstance := 1)
  | 2 => `(configOption| portfolioInstance := 2)
  | 3 => `(configOption| portfolioInstance := 3)
  | 4 => `(configOption| portfolioInstance := 4)
  | 5 => `(configOption| portfolioInstance := 5)
  | 6 => `(configOption| portfolioInstance := 6)
  | 7 => `(configOption| portfolioInstance := 7)
  | 8 => `(configOption| portfolioInstance := 8)
  | 9 => `(configOption| portfolioInstance := 9)
  | 10 => `(configOption| portfolioInstance := 10)
  | 11 => `(configOption| portfolioInstance := 11)
  | 12 => `(configOption| portfolioInstance := 12)
  | 13 => `(configOption| portfolioInstance := 13)
  | 14 => `(configOption| portfolioInstance := 14)
  | 15 => `(configOption| portfolioInstance := 15)
  | 16 => `(configOption| portfolioInstance := 16)
  | _ => throwError "Invalid Duper instance {n}"

/-- If `n` is a Nat that corresponds to one of Duper's selection functions, then `selFunctionNumToConfigOptionStx n` returns the
    syntax object corresponding to `selFunction := n`. This is necessary so that `duper?` can produce its suggestion. -/
def selFunctionNumToConfigOptionStx [Monad m] [MonadError m] [MonadQuotation m] (n : Nat) : m (TSyntax `Duper.configOption) := do
  match n with
  | 0 => `(configOption| selFunction := 0)
  | 1 => `(configOption| selFunction := 1)
  | 2 => `(configOption| selFunction := 2)
  | 3 => `(configOption| selFunction := 3)
  | 4 => `(configOption| selFunction := 4)
  | 5 => `(configOption| selFunction := 5)
  | 6 => `(configOption| selFunction := 6)
  | 7 => `(configOption| selFunction := 7)
  | 8 => `(configOption| selFunction := 8)
  | 9 => `(configOption| selFunction := 9)
  | 10 => `(configOption| selFunction := 10)
  | 11 => `(configOption| selFunction := 11)
  | 12 => `(configOption| selFunction := 12)
  | 13 => `(configOption| selFunction := 13)
  | _ => throwError "Invalid selFunction option"

/-- Constructs and suggests the syntax for a duper call, for use with `duper?` If a portfolioInstance other than 0 is specified, then
    the returned tactic will only specify that instance (since it is all that is necessary). If the portfolioInstance specified is 0, then
    the returned tactic will use all of the optional arguments to construct the suggested syntax. -/
def mkDuperCallSuggestion (duperStxRef : Syntax) (origSpan : Syntax) (facts : Syntax.TSepArray `term ",")
  (withDuperStar : Bool) (portfolioInstance : Nat) (inhabitationReasoning : Option Bool := none) (monomorphization : Option Bool := none)
  (includeExpensiveRules : Option Bool := none) (selFunction : Option Nat := none) : MetaM Unit := do
  let mut configOptionsArr : Array Syntax := #[] -- An Array containing configuration option elements and separators (",")
  let portfolioInstanceStx ← portfolioInstanceToConfigOptionStx portfolioInstance
  configOptionsArr := configOptionsArr.push portfolioInstanceStx

  /- For all other portfolio instances, the instance specifies all configuration options. But for portfolioInstance 0 in particular,
     it is necessary to manually add each configuration option. -/
  if portfolioInstance = 0 then
    match inhabitationReasoning with
    | none => pure ()
    | some b =>
      let inhabitationReasoningStx ← boolToBoolLit b
      configOptionsArr := configOptionsArr.push (mkAtom ",") -- Add separator before each additional element
      configOptionsArr := configOptionsArr.push $ ← `(configOption| inhabitationReasoning := $inhabitationReasoningStx)
    match monomorphization with
    | none => pure ()
    | some b =>
      let monomorphizationStx ← boolToBoolLit b
      configOptionsArr := configOptionsArr.push (mkAtom ",") -- Add separator before each additional element
      configOptionsArr := configOptionsArr.push $ ← `(configOption| monomorphization := $monomorphizationStx)
    match includeExpensiveRules with
    | none => pure ()
    | some b =>
      let includeExpensiveRulesStx ← boolToBoolLit b
      configOptionsArr := configOptionsArr.push (mkAtom ",") -- Add separator before each additional element
      configOptionsArr := configOptionsArr.push $ ← `(configOption| includeExpensiveRules := $includeExpensiveRulesStx)
    match selFunction with
    | none => pure ()
    | some selFunctionNum =>
      let selFunctionSyntax ← selFunctionNumToConfigOptionStx selFunctionNum
      configOptionsArr := configOptionsArr.push (mkAtom ",") -- Add separator before each additional element
      configOptionsArr := configOptionsArr.push selFunctionSyntax

  let configOptionsStx : Syntax.TSepArray `Duper.configOption "," := {elemsAndSeps := configOptionsArr}
  if withDuperStar && facts.elemsAndSeps.isEmpty then
    let suggestion ←`(tactic| duper [*] {$configOptionsStx,*})
    Std.Tactic.TryThis.addSuggestion duperStxRef suggestion (origSpan? := origSpan)
  else if withDuperStar then
    let suggestion ←`(tactic| duper [*, $facts,*] {$configOptionsStx,*})
    Std.Tactic.TryThis.addSuggestion duperStxRef suggestion (origSpan? := origSpan)
  else
    let suggestion ←`(tactic| duper [$facts,*] {$configOptionsStx,*})
    Std.Tactic.TryThis.addSuggestion duperStxRef suggestion (origSpan? := origSpan)

/-- Implements duper calls when portfolio mode is enabled. If `duperStxInfo` is not none and `runDuperPortfolioMode` succeeds in deriving
    a contradiction, then `Std.Tactic.TryThis.addSuggestion` will be used to give the user a more specific invocation of duper that can
    reproduce the proof (without having to run duper in portfolio mode). As with the other `runDuper` functions, `runDuperPortfolioMode`
    ultimately returns a proof if successful and throws an error if unsuccessful. -/
def runDuperPortfolioMode (formulas : List (Expr × Expr × Array Name)) (configOptions : ConfigurationOptions)
  (duperStxInfo : Option (Syntax × Syntax × Syntax.TSepArray `term ","  × Bool)) : MetaM Expr := do
  let initHeartbeats ← IO.getNumHeartbeats
  let maxHeartbeats ← getMaxHeartbeats
  let instances :=
    match configOptions.monomorphization with
    | none =>
      #[(1, runDuperInstance1 formulas),
        (3, runDuperInstance3 formulas),
        (5, runDuperInstance5 formulas),
        (7, runDuperInstance7 formulas)]
    | some true => -- Replace instance 7 which has monomorphization disabled
      #[(1, runDuperInstance1 formulas),
        (3, runDuperInstance3 formulas),
        (5, runDuperInstance5 formulas),
        (15, runDuperInstance15 formulas)]
    | some false => -- Replaces instances 1, 3, and 5 which have monomorphization enabled
      #[(9, runDuperInstance9 formulas),
        (11, runDuperInstance11 formulas),
        (13, runDuperInstance13 formulas),
        (7, runDuperInstance7 formulas)]
  let numInstances := instances.size
  let mut maxInstanceHeartbeats := maxHeartbeats / numInstances -- Allocate total heartbeats among all instances
  let mut numInstancesTried := 0
  let mut inhabitationReasoningEnabled : Bool :=
    match configOptions.inhabitationReasoning with
    | some true => true
    | some false => false
    | none => false -- If inhabitationReasoning is not specified, disable it unless it becomes clear it is needed
  for (duperInstanceNum, duperInstanceFn) in instances do
    /- If Duper finds a contradiction and successfully performs proof reconstruction, `proofOption` will be `some proof` and
       `retryWithInhabitationReasoning` will be false.

       If Duper saturates or fails proof reconstruction specifically because inhabitation reasoning is disabled, `proofOption`
       will be `none` and `retryWithInhabitationReasoning` will be true.

       If Duper times out (achieving ProverM.Result.unknown and throwing the error "Prover was terminated.") then `proofOption`
       will be `none` and `retryWithInhabitationReasoning` will be false.

       If Duper fails for any other reason, then Duper will either continue to the next instance or throw an error depending on
       the `throwPortfolioErrors` option. -/
    let (duperInstanceNum, duperInstanceFn) :=
      if inhabitationReasoningEnabled then
        /- If inhabitationReasoningEnabled and duperInstanceNum has inhabitation reasoning disabled, then replace the current
           duper instance with the corresponding instance that has inhabitation reasoning enabled -/
        match getInstanceWithInhabitationReasoning duperInstanceNum with
        | none => (duperInstanceNum, duperInstanceFn)
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas)
      else (duperInstanceNum, duperInstanceFn)
    let (proofOption, retryWithInhabitationReasoning) ←
      try
        let proof ← duperInstanceFn maxInstanceHeartbeats
        pure $ (some proof, false)
      catch e =>
        let errorMessage ← e.toMessageData.toString
        if errorMessage.startsWith "instantiatePremises :: Failed to find instance for" then
          if inhabitationReasoningEnabled || (← instanceHasInhabitationReasoning duperInstanceNum) then
            if ← getThrowPortfolioErrorsM then
              throw e -- Throw the error rather than try to continue because inhabitation reasoning is already enabled
            else
              pure (none, false)
          else if configOptions.inhabitationReasoning = some false then
            if ← getThrowPortfolioErrorsM then
              IO.println "Duper determined that this problem requires inhabitation reasoning"
              throw e -- Throw the error rather than try to continue because the user explicitly specified that inhabitation reasoning should be disabled
            else
              pure (none, false) -- Don't retry with inhabitation reasoning because the user specifically indicated not to
          else
            pure (none, true) -- Attempting to solve this problem with inhabitation reasoning disabled leads to failed proof reconstruction
        else if errorMessage.startsWith "Prover was terminated" then
          pure (none, false) -- No reason to retry with inhabitation reasoning, portfolio mode should just move on to the next instance in the loop
        else if ← getThrowPortfolioErrorsM then
          throw e -- Throw the error because it doesn't appear to pertain to inhabitation reasoning or a timeout
        else
          pure (none, false) -- Even though the instance threw an error, keep trying other instances
    -- Update numInstancesTried
    numInstancesTried := numInstancesTried + 1
    match proofOption with
    | some proof =>
      if ← getPrintPortfolioInstanceM then IO.println s!"Solved by Duper instance {duperInstanceNum}"
      match duperStxInfo with
      | none => return proof
      | some (duperStxRef, origSpan, facts, withDuperStar) =>
        mkDuperCallSuggestion duperStxRef origSpan facts withDuperStar duperInstanceNum
        return proof
    | none =>
      if !retryWithInhabitationReasoning then continue
      -- Attempting to solve this problem with inhabitation reasoning disabled leads to failed proof reconstruction
      inhabitationReasoningEnabled := true
      -- Since we are rerunning this instance, we need to adjust maxInstanceHeartbeats to make sure all the instances will be attempted
      let curHeartbeats ← IO.getNumHeartbeats
      let heartbeatsUsed := curHeartbeats - initHeartbeats
      let remainingHeartbeats := maxHeartbeats - heartbeatsUsed
      maxInstanceHeartbeats := remainingHeartbeats / (numInstances + 1 - numInstancesTried)
      -- Retry the portfolio instance that was able to find a proof when inhabitation reasoning was disabled
      IO.println "Duper determined that this problem requires inhabitation reasoning, continuing portfolio mode with it enabled"
      let (duperInstanceNum, duperInstanceFn) :=
        match getInstanceWithInhabitationReasoning duperInstanceNum with
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas)
        | none => (duperInstanceNum, duperInstanceFn) -- This case should never occur
      /- If Duper finds a contradiction and successfully performs proof reconstruction `proofOption` will be `some proof`.
         If Duper times out, then `proofOption` will be `none`.
         If Duper fails for any other reason, then an error will be thrown. -/
      let proofOption ←
        try
          let proof ← duperInstanceFn maxInstanceHeartbeats
          pure $ some proof
        catch e =>
          -- Only `e` is an error arising from the Duper instance timing out, it should be caught. Otherwise, it should be thrown.
          if (← e.toMessageData.toString).startsWith "Prover was terminated" then pure none -- Duper instance just timed out, try again with the next instance
          else
            if ← getThrowPortfolioErrorsM then
              throw e -- Error unrelated to timeout, and inhabitation reasoning is already enabled, so throw the error
            else
              pure none
      match proofOption with
      | some proof =>
        if ← getPrintPortfolioInstanceM then IO.println s!"Solved by Duper instance {duperInstanceNum}"
        match duperStxInfo with
        | none => return proof
        | some (duperStxRef, origSpan, facts, withDuperStar) =>
          mkDuperCallSuggestion duperStxRef origSpan facts withDuperStar duperInstanceNum
          return proof
      | none => continue -- Duper timed out or otherwise failed, try the next instance
  throwError "Prover failed to solve the goal in allotted time"
