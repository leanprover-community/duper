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

register_option printPortfolioInstance : Bool := {
  defValue := false
  descr := "Whether to print the portfolio instance that solved the proof"
}

def getPrintPortfolioInstance (opts : Options) : Bool :=
  printPortfolioInstance.get opts

def getPrintPortfolioInstanceM : CoreM Bool := do
  let opts ← getOptions
  return getPrintPortfolioInstance opts

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

/-- Runs duper with selFunction 1 -/
def runDuperInstance5 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  match inhabitationReasoning with
  | none => withOptions (fun o => o.set `selFunction 1) $ runDuper formulas instanceMaxHeartbeats
  | some b => withOptions (fun o => (o.set `selFunction 1).set `inhabitationReasoning b) $ runDuper formulas instanceMaxHeartbeats

/-- Default duper instance with monomorphization enabled. -/
def runDuperInstance6 (formulas : List (Expr × Expr × Array Name)) (inhabitationReasoning : Option Bool) (instanceMaxHeartbeats : Nat) : MetaM Expr := do
  let lemmas ← formulasToAutoLemmas formulas
  -- Calling Auto.unfoldConstAndPreprocessLemma is an essential step for the monomorphization procedure
  let lemmas ← lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[])
  let inhFacts ← Auto.Inhabitation.getInhFactsFromLCtx
  let prover : Array Auto.Lemma → MetaM Expr :=
    fun lemmas => do
      let monomorphizedFormulas ← autoLemmasToFormulas lemmas
      match inhabitationReasoning with
      | none => runDuper monomorphizedFormulas instanceMaxHeartbeats
      | some b => withOptions (fun o => o.set `inhabitationReasoning b) $ runDuper monomorphizedFormulas instanceMaxHeartbeats
  Auto.monoInterface lemmas inhFacts prover

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

structure ConfigurationOptions where
  portfolioMode : Bool -- True by default (unless portfolio instance is specified)
  portfolioInstance : Option Nat -- None by default (unless portfolioMode is false, in which case, some 0 is default)
  inhabitationReasoning : Option Bool -- None by default

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
  | _ => throwError "Invalid Duper instance {n}"

/-- Constructs and suggests the syntax for a duper call, for use with `duper?` -/
def mkDuperCallSuggestion (duperStxRef : Syntax) (origSpan : Syntax) (facts : Syntax.TSepArray `term ",")
  (withDuperStar : Bool) (portfolioInstance : Nat) (inhabitationReasoning : Option Bool) : MetaM Unit := do
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
  let maxHeartbeats ← getMaxHeartbeats
  let instances :=
    #[(0, runDuperInstance0 formulas),
      (1, runDuperInstance1 formulas),
      (2, runDuperInstance2 formulas),
      (3, runDuperInstance3 formulas),
      (4, runDuperInstance4 formulas),
      (5, runDuperInstance5 formulas)]
  let numInstances := instances.size
  let maxInstanceHeartbeats := maxHeartbeats / numInstances -- Allocate total heartbeats among all instances
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

       If Duper fails for any other reason, then an error will be thrown. -/
    let (proofOption, retryWithInhabitationReasoning) ←
      try
        let proof ← duperInstanceFn inhabitationReasoningEnabled maxInstanceHeartbeats
        pure $ (some proof, false)
      catch e =>
        let errorMessage ← e.toMessageData.toString
        if errorMessage.startsWith "instantiatePremises :: Failed to find instance for" || errorMessage.startsWith "Prover saturated" then
          if inhabitationReasoningEnabled then
            throw e -- Throw the error rather than try to continue because inhabitation reasoning is already enabled
          else if configOptions.inhabitationReasoning = some false then
            IO.println "Duper determined that this problem requires inhabitation reasoning"
            throw e -- Throw the error rather than try to continue because the user explicitly specified that inhabitation reasoning should be disabled
          else
            pure (none, true) -- Attempting to solve this problem with inhabitation reasoning disabled leads to failed proof reconstruction
        else if errorMessage.startsWith "Prover was terminated" then
          pure (none, false) -- No reason to retry with inhabitation reasoning, portfolio mode should just move on to the next instance in the loop
        else
          throw e -- Throw the error because it doesn't appear to pertain to inhabitation reasoning or a timeout
    match proofOption with
    | some proof =>
      if ← getPrintPortfolioInstanceM then IO.println s!"Solved by Duper instance {duperInstanceNum}"
      match duperStxInfo with
      | none => return proof
      | some (duperStxRef, origSpan, facts, withDuperStar) =>
        mkDuperCallSuggestion duperStxRef origSpan facts withDuperStar duperInstanceNum inhabitationReasoningEnabled
        return proof
    | none =>
      if !retryWithInhabitationReasoning then continue
      -- Attempting to solve this problem with inhabitation reasoning disabled leads to failed proof reconstruction
      inhabitationReasoningEnabled := true
      -- Retry the portfolio instance that was able to find a proof when inhabitation reasoning was disabled
      IO.println "Duper determined that this problem requires inhabitation reasoning, continuing portfolio mode with it enabled"
      /- If Duper finds a contradiction and successfully performs proof reconstruction `proofOption` will be `some proof`.
         If Duper times out, then `proofOption` will be `none`.
         If Duper fails for any other reason, then an error will be thrown. -/
      let proofOption ←
        try
          let proof ← duperInstanceFn inhabitationReasoningEnabled maxInstanceHeartbeats
          pure $ some proof
        catch e =>
          -- Only `e` is an error arising from the Duper instance timing out, it should be caught. Otherwise, it should be thrown.
          if (← e.toMessageData.toString).startsWith "Prover was terminated" then pure none -- Duper instance just timed out, try again with the next instance
          else throw e -- Error unrelated to timeout, and inhabitation reasoning is already enabled, so throw the error
      match proofOption with
      | some proof =>
        if ← getPrintPortfolioInstanceM then IO.println s!"Solved by Duper instance {duperInstanceNum}"
        match duperStxInfo with
        | none => return proof
        | some (duperStxRef, origSpan, facts, withDuperStar) =>
          mkDuperCallSuggestion duperStxRef origSpan facts withDuperStar duperInstanceNum inhabitationReasoningEnabled
          return proof
      | none => continue -- Duper timed out, try the next instance
  throwError "Prover ran out of time before solving the goal"
