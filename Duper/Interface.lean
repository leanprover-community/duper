import Std.Lean.CoreM
import Duper.ProofReconstruction
import Auto.Tactic

open Lean
open Lean.Meta
open Duper
open ProverM
open Lean.Parser

initialize
  registerTraceClass `duper.saturate.debug
  registerTraceClass `duper.portfolio.debug
  registerTraceClass `duper.monomorphization.debug

register_option duper.printPortfolioInstance : Bool := {
  defValue := false
  descr := "Whether to print the portfolio instance that solved the proof"
}

register_option duper.throwPortfolioErrors : Bool := {
  defValue := false
  descr := "Whether to halt portfolio mode and throw an error if a subinstance throws an error"
}

def getPrintPortfolioInstance (opts : Options) : Bool :=
  duper.printPortfolioInstance.get opts

def getThrowPortfolioErrors (opts : Options) : Bool :=
  duper.throwPortfolioErrors.get opts

def getPrintPortfolioInstanceM : CoreM Bool := do
  let opts ← getOptions
  return getPrintPortfolioInstance opts

def getThrowPortfolioErrorsM : CoreM Bool := do
  let opts ← getOptions
  return getThrowPortfolioErrors opts

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

declare_syntax_cat Duper.preprocessing_option (behavior := symbol)

syntax "full" : Duper.preprocessing_option
syntax "monomorphization" : Duper.preprocessing_option
syntax "no_preprocessing" : Duper.preprocessing_option

inductive PreprocessingOption where
  | FullPreprocessing
  | Monomorphization
  | NoPreprocessing
  deriving DecidableEq

open PreprocessingOption

def elabPreprocessingOption [Monad m] [MonadError m] (stx : TSyntax `Duper.preprocessing_option) : m PreprocessingOption :=
  withRef stx do
    match stx with
    | `(preprocessing_option| full) => return FullPreprocessing
    | `(preprocessing_option| monomorphization) => return Monomorphization
    | `(preprocessing_option| no_preprocessing) => return NoPreprocessing
    | _ => Elab.throwUnsupportedSyntax

def preprocessingOptionToStx [Monad m] [MonadQuotation m] (o : PreprocessingOption) : m (TSyntax `Duper.preprocessing_option) := do
  match o with
  | FullPreprocessing => `(preprocessing_option| full)
  | Monomorphization => `(preprocessing_option| monomorphization)
  | NoPreprocessing => `(preprocessing_option| no_preprocessing)

declare_syntax_cat Duper.configOption (behavior := symbol)

syntax (&"portfolioMode" " := " Duper.bool_lit) : Duper.configOption
syntax (&"portfolioInstance" " := " numLit) : Duper.configOption
syntax (&"inhabitationReasoning" " := " Duper.bool_lit) : Duper.configOption
syntax (&"preprocessing" " := " Duper.preprocessing_option) : Duper.configOption
syntax (&"includeExpensiveRules" " := " Duper.bool_lit) : Duper.configOption
syntax (&"selFunction" " := " numLit) : Duper.configOption

structure ConfigurationOptions where
  portfolioMode : Bool -- True by default (unless portfolio instance is specified)
  portfolioInstance : Option Nat -- None by default (unless portfolioMode is false, in which case, some 0 is default)
  inhabitationReasoning : Option Bool -- None by default
  preprocessing : Option PreprocessingOption -- None by default
  includeExpensiveRules : Option Bool -- None by default
  selFunction : Option Nat -- None by default

syntax duperStar := "*"

/--
`duper [facts] {options}` is a terminal tactic that uses an automatic theorem prover to attempt to solve the current main goal.

The `facts` supplied to `duper` are separated by commas and can include:
- Hypotheses (of type `Prop`) from the local context
- External lemmas
- The symbol `*` to indicate that `duper` should consider all proofs in the current local context

By default, `duper` will call multiple instances of itself with different option configurations in an attempt to find the
option configuration that is best suited for the current problem. This behavior can be changed by including the option
`portfolioMode := false` in the comma separated options list. Running `duper` with `portfolioMode` enabled means that
each instance of `duper` will be given less time to run. To increase the amount of time allocated to `duper`, use
`set_option maxHeartbeats <num>` (setting `<num>` to 3 times the default value will ensure that each `duper` instance is
given as much time as it would receive if run with `portfolioMode` disabled).

The variant `duper?` will call `duper` and, if a proof is found, return a `Try this` suggestion that will call `duper`
using just the option configuration that succeeded in finding a proof. If the suggestion is used, then on all subsequent
compilations, only the version of `duper` that succeeded will be called.

Additional options that can be included in the options list include:
- `portfolioInstance`: Can be set to a natural number from 0 to 24 and corresponds to an exact set of options by which
  `duper` can be called.
- `preprocessing`: Can be set to `full`, `monomorphization`, or `no_preprocessing`.
- `inhabitationReasoning`: Can be set to `true` or `false`.
- `includeExpensiveRules`: Can be set to `true` or `false`.

For a more complete referenceon `duper` (including fuller descriptions of the various options), see
[its README](https://github.com/leanprover-community/duper#readme)
-/
syntax (name := duper) "duper" (ppSpace "[" (duperStar <|> term),* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic

@[inherit_doc duper]
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
  | 17 => `(configOption| portfolioInstance := 17)
  | 18 => `(configOption| portfolioInstance := 18)
  | 19 => `(configOption| portfolioInstance := 19)
  | 20 => `(configOption| portfolioInstance := 20)
  | 21 => `(configOption| portfolioInstance := 21)
  | 22 => `(configOption| portfolioInstance := 22)
  | 23 => `(configOption| portfolioInstance := 23)
  | 24 => `(configOption| portfolioInstance := 24)
  | 25 => `(configOption| portfolioInstance := 25)
  | 26 => `(configOption| portfolioInstance := 26)
  | 27 => `(configOption| portfolioInstance := 27)
  | 28 => `(configOption| portfolioInstance := 28)
  | 29 => `(configOption| portfolioInstance := 29)
  | 30 => `(configOption| portfolioInstance := 30)
  | 31 => `(configOption| portfolioInstance := 31)
  | 32 => `(configOption| portfolioInstance := 32)
  | 33 => `(configOption| portfolioInstance := 33)
  | 34 => `(configOption| portfolioInstance := 34)
  | 35 => `(configOption| portfolioInstance := 35)
  | 36 => `(configOption| portfolioInstance := 36)
  | 37 => `(configOption| portfolioInstance := 37)
  | 38 => `(configOption| portfolioInstance := 38)
  | 39 => `(configOption| portfolioInstance := 39)
  | 40 => `(configOption| portfolioInstance := 40)
  | 41 => `(configOption| portfolioInstance := 41)
  | 42 => `(configOption| portfolioInstance := 42)
  | 43 => `(configOption| portfolioInstance := 43)
  | 44 => `(configOption| portfolioInstance := 44)
  | 45 => `(configOption| portfolioInstance := 45)
  | 46 => `(configOption| portfolioInstance := 46)
  | 47 => `(configOption| portfolioInstance := 47)
  | 48 => `(configOption| portfolioInstance := 48)
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
def mkDuperCallSuggestion (duperStxRef : Syntax) (origSpan : Syntax) (facts : Syntax.TSepArray `term ",") (withDuperStar : Bool)
  (portfolioInstance : Nat) (inhabitationReasoning : Option Bool := none) (preprocessing : Option PreprocessingOption := none)
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
    match preprocessing with
    | none => pure ()
    | some o =>
      let preprocessingStx ← preprocessingOptionToStx o
      configOptionsArr := configOptionsArr.push (mkAtom ",") -- Add separator before each additional element
      configOptionsArr := configOptionsArr.push $ ← `(configOption| preprocessing := $preprocessingStx)
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

def unfoldDefinitions (formulas : List (Expr × Expr × Array Name × Bool)) : MetaM (List (Expr × Expr × Array Name × Bool)) := do
  withTransparency .reducible do
    let mut newFormulas := formulas
    for (e, proof, paramNames, isFromGoal) in formulas do
      let update (ty lhs rhs : Expr) newFormulas (containedIn : Expr → Bool) : MetaM _ := do
        if containedIn rhs then pure newFormulas else
          newFormulas.mapM fun (f, fproof, fparamNames, fIsFromGoal) => do
            if !containedIn f then
              return (f, fproof, fparamNames, fIsFromGoal)
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
                some (← Meta.withLocalDeclD `_ ty' fun fvar => do
                  Meta.mkLambdaFVars #[fvar] $ ← Meta.mkAppM ``Eq #[abstracted.instantiate1 fvar, mkConst ``True]),
                some fproof,
                rhs',
                proof']
              return (f, ← instantiateMVars $ fproof, fparamNames, isFromGoal || fIsFromGoal)
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
  trace[duper.prover.saturate] "Final Active Set: {state.activeSet.toArray}"
  trace[duper.saturate.debug] "Final active set numbers: {state.activeSet.toArray.map (fun c => (state.allClauses.find! c).number)}"
  trace[duper.saturate.debug] "Final Active Set: {state.activeSet.toArray}"
  trace[duper.saturate.debug] "Verified Inhabited Types: {state.verifiedInhabitedTypes.map (fun x => x.expr)}"
  trace[duper.saturate.debug] "Verified Nonempty Types: {state.verifiedNonemptyTypes.map (fun x => x.1.expr)}"
  trace[duper.saturate.debug] "Potentially Uninhabited Types: {state.potentiallyUninhabitedTypes.map (fun x => x.expr)}"
  trace[duper.saturate.debug] "Potentially Vacuous Clauses: {state.potentiallyVacuousClauses.toArray}"

def formulasToMessageData : Expr × Expr × Array Name × Bool → MessageData
| (ty, term, names, isFromGoal) => .compose (.compose m!"{names} @ " m!"{term} : ") m!"{ty}"

/-- Entry point for calling a single instance of duper using the options determined by (← getOptions).

    Formulas should consist of lemmas supplied by the user (to see how to obtain formulas from duper's input syntax, see `collectAssumptions`).
    InstanceMaxHeartbeats should indicate how many heartbeats duper should run for before timing out (if instanceMaxHeartbeats is set to 0,
    then duper will run until it is timed out by the Core `maxHeartbeats` option). If Duper succeeds in deriving a contradiction and constructing
    a proof for it, then `runDuper` returns that proof as an expression. Otherwise, Duper will throw an error. -/
def runDuper (formulas : List (Expr × Expr × Array Name × Bool)) (instanceMaxHeartbeats : Nat) : MetaM Expr := do
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
    throwError "Duper saturated"
  | Result.unknown =>
    /- Note: If this error message changes, make sure to grep the current message and change any code that uses the content
       of this error message to determine whether Duper threw an error due to an actual problem or due to timeout. -/
    throwError "Duper was terminated"

/- Note for converting between Duper's formulas format and Auto's lemmas format. If `hp : p`, then Duper stores the formula
   `(p, eq_true hp, #[], isFromGoal)` whereas Auto stores the lemma `⟨hp, p, #[]⟩`. Importantly, Duper stores the proof of `p = True` and
   Auto stores the proof of `p`, so this must be accounted for in the conversion (maybe later, it will be good to refactor Duper
   to be in alignment with how Auto stores lemmas to avoid the unnecessary cost of this conversion, but for now, it suffices to
   add or remove `eq_true` as needed) -/

partial def getLeavesFromDTr (t : Auto.DTr) : Array String :=
  match t with
  | Auto.DTr.node _ subTrees => (subTrees.map getLeavesFromDTr).flatten
  | Auto.DTr.leaf s => #[s]

/-- Converts formulas/lemmas from the format used by Duper to the format used by Auto. Duper uses Auto's deriv DTr to keep
    track of `isFromGoal` information through the monomorphization procedure. -/
def formulasToAutoLemmas (formulas : List (Expr × Expr × Array Name × Bool)) : MetaM (Array Auto.Lemma) :=
  formulas.toArray.mapM
    (fun (fact, proof, params, isFromGoal) => -- For now, isFromGoal is ignored
      return {proof := ← Meta.mkAppM ``of_eq_true #[proof], type := fact, params := params, deriv := (.leaf s!"{isFromGoal}")})

/-- Converts formulas/lemmas from the format used by Auto to the format used by Duper. -/
def autoLemmasToFormulas (lemmas : Array Auto.Lemma) : MetaM (List (Expr × Expr × Array Name × Bool)) :=
  /- Currently, we don't have any means of determining which lemmas are originally from the goal, so for now, we are
     indicating that all lemmas don't come from the goal. This behavior should be updated once we get a means of tracking
     that information through the monomorphization procedure. -/
  lemmas.toList.mapM
    (fun lem => do
      let derivLeaves := getLeavesFromDTr lem.deriv
      let isFromGoal := derivLeaves.contains "true"
      trace[duper.monomorphization.debug] "deriv for {lem.type}: {lem.deriv}"
      trace[duper.monomorphization.debug] "derivLeaves for {lem.type}: {derivLeaves}"
      return (lem.type, ← Meta.mkAppM ``eq_true #[lem.proof], lem.params, isFromGoal))

/-- Given `formulas`, `instanceMaxHeartbeats`, and an instance of Duper `inst`, runs `inst` with monomorphization preprocessing. -/
def runDuperInstanceWithMonomorphization (formulas : List (Expr × Expr × Array Name × Bool)) (instanceMaxHeartbeats : Nat)
  (inst : List (Expr × Expr × Array Name × Bool) → Nat → MetaM Expr) : MetaM Expr := do
  let lemmas ← formulasToAutoLemmas formulas
  -- Calling Auto.unfoldConstAndPreprocessLemma is an essential step for the monomorphization procedure
  let lemmas ← lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[])
  let inhFacts ← Auto.Inhabitation.getInhFactsFromLCtx
  let prover : Array Auto.Lemma → MetaM Expr :=
    fun lemmas => do
      let monomorphizedFormulas ← autoLemmasToFormulas lemmas
      trace[duper.monomorphization.debug] "Original formulas: {formulas.map (fun f => (f.1, f.2.2.2))}"
      trace[duper.monomorphization.debug] "Monomorphized formulas: {monomorphizedFormulas.map (fun f => (f.1, f.2.2.2))}"
      inst monomorphizedFormulas instanceMaxHeartbeats
  Auto.monoInterface lemmas inhFacts prover

/-- Given `formulas`, `instanceMaxHeartbeats`, `declName?` and an instance of Duper `inst`, runs `inst` with all of Auto's preprocessing
    (monomorphization, skolemization, definition unfolding, exhaustive function extensionality rewrites, and BitVec simplicfication). -/
def runDuperInstanceWithFullPreprocessing (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name)
  (instanceMaxHeartbeats : Nat) (inst : List (Expr × Expr × Array Name × Bool) → Nat → MetaM Expr) : MetaM Expr := do
  let lemmas ← formulasToAutoLemmas formulas
  -- Calling Auto.unfoldConstAndPreprocessLemma is an essential step for the monomorphization procedure
  let lemmas ← lemmas.mapM (m:=MetaM) (Auto.unfoldConstAndPreprocessLemma #[])
  let inhFacts ← Auto.Inhabitation.getInhFactsFromLCtx
  let prover : Array Auto.Lemma → MetaM Expr :=
    fun lemmas => do
      let monomorphizedFormulas ← autoLemmasToFormulas lemmas
      trace[duper.monomorphization.debug] "Original formulas: {formulas.map (fun f => (f.1, f.2.2.2))}"
      trace[duper.monomorphization.debug] "Monomorphized formulas: {monomorphizedFormulas.map (fun f => (f.1, f.2.2.2))}"
      inst monomorphizedFormulas instanceMaxHeartbeats
  Auto.runNativeProverWithAuto declName? prover lemmas inhFacts

/-- `mkDuperInstance` is called by each `runDuperInstanceN` function to construct the desired Duper instance. Additionally,
    if a user invokes portfolio instance 0 (which is the special instance reserved for allowing the user to manually construct
    an instance with their own configuration options), then this function will be called directly. -/
def mkDuperInstance (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat)
  (inhabitationReasoning : Option Bool) (preprocessing : Option PreprocessingOption) (includeExpensiveRules : Option Bool)
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
  match preprocessing with
  | some FullPreprocessing =>
    addInhabitationReasoningOption ∘ addIncludeExpensiveRulesOption ∘ addSelFunctionOption $
      runDuperInstanceWithFullPreprocessing formulas declName? instanceMaxHeartbeats runDuper
  | some Monomorphization =>
    addInhabitationReasoningOption ∘ addIncludeExpensiveRulesOption ∘ addSelFunctionOption $
      runDuperInstanceWithMonomorphization formulas instanceMaxHeartbeats runDuper
  | some NoPreprocessing =>
    addInhabitationReasoningOption ∘ addIncludeExpensiveRulesOption ∘ addSelFunctionOption $
      runDuper formulas instanceMaxHeartbeats
  | none => -- Use full preprocessing by default
    addInhabitationReasoningOption ∘ addIncludeExpensiveRulesOption ∘ addSelFunctionOption $
      runDuperInstanceWithFullPreprocessing formulas declName? instanceMaxHeartbeats runDuper

/-- First instance called by portfolio mode. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance1 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 4)

/-- Same as duper instance 1 except inhabitation reasoning is enabled. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance2 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 4)

/-- Second instance called by portfolio mode. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance3 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 11)

/-- Same as duper instance 3 except inhabitation reasoning is enabled. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance4 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 11)

/-- Third instance called by portfolio mode. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance5 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 13)

/-- Same as duper instance 5 except inhabitation reasoning is enabled. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance6 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 13)

/-- Fourth instance called by portfolio mode. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance7 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 2)

/-- Same as duper instance 7 except inhabitation reasoning is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance8 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 2)

/-- Same as duper instance 1 except preprocessing is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance9 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 4)

/-- Same as duper instance 2 except preprocessing is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance10 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 4)

/-- Same as duper instance 3 except preprocessing is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance11 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 11)

/-- Same as duper instance 4 except preprocessing is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance12 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 11)

/-- Same as duper instance 5 except preprocessing is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance13 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 13)

/-- Same as duper instance 6 except preprocessing is disabled. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance14 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 13)

/-- Same as duper instance 7 except preprocessing is enabled. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance15 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 2)

/-- Same as duper instance 8 except preprocessing is enabled. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance16 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 2)

/-- Same as duper instance 1 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance17 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 4)

/-- Same as duper instance 2 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = false -/
def runDuperInstance18 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 4)

/-- Same as duper instance 3 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance19 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 11)

/-- Same as duper instance 4 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = true -/
def runDuperInstance20 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 11)

/-- Same as duper instance 5 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance21 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 13)

/-- Same as duper instance 6 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = false -/
def runDuperInstance22 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 13)

/-- Same as duper instance 7 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance23 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 2)

/-- Same as duper instance 8 except preprocessing is set to monomorphization only. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = true -/
def runDuperInstance24 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 2)

/-- Same as duper instance 1 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = true -/
def runDuperInstance25 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 4)

/-- Same as duper instance 2 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = true -/
def runDuperInstance26 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 4)

/-- Same as duper instance 3 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = false -/
def runDuperInstance27 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 11)

/-- Same as duper instance 4 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = false -/
def runDuperInstance28 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 11)

/-- Same as duper instance 5 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = true -/
def runDuperInstance29 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 13)

/-- Same as duper instance 6 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = true -/
def runDuperInstance30 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 13)

/-- Same as duper instance 7 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = false -/
def runDuperInstance31 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 2)

/-- Same as duper instance 8 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = false -/
def runDuperInstance32 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 2)

/-- Same as duper instance 9 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = true -/
def runDuperInstance33 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 4)

/-- Same as duper instance 10 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = true -/
def runDuperInstance34 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 4)

/-- Same as duper instance 11 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = false -/
def runDuperInstance35 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 11)

/-- Same as duper instance 12 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = false -/
def runDuperInstance36 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 11)

/-- Same as duper instance 13 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = true -/
def runDuperInstance37 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 13)

/-- Same as duper instance 14 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = true -/
def runDuperInstance38 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := NoPreprocessing)
    (includeExpensiveRules := true) (selFunction := some 13)

/-- Same as duper instance 15 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = false -/
def runDuperInstance39 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 2)

/-- Same as duper instance 16 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = full
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = false -/
def runDuperInstance40 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := FullPreprocessing)
    (includeExpensiveRules := false) (selFunction := some 2)

/-- Same as duper instance 17 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = false
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = true -/
def runDuperInstance41 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 4)

/-- Same as duper instance 18 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 4 (which corresponds to Zipperposition's default selection function)
    - includeExpensiveRules = true -/
def runDuperInstance42 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 4)

/-- Same as duper instance 19 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = false
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = false -/
def runDuperInstance43 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 11)

/-- Same as duper instance 20 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 11 (which corresponds to E's SelectMaxLComplexAvoidPosPred and Zipperposition's e_sel)
    - includeExpensiveRules = false -/
def runDuperInstance44 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 11)

/-- Same as duper instance 21 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = no_preprocessing
    - inhabitationReasoning = false
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = true -/
def runDuperInstance45 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 13)

/-- Same as duper instance 22 except includeExpensiveRules is set to true. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 13 (which corresponds to E's SelectComplexG and Zipperposition's e_sel3)
    - includeExpensiveRules = true -/
def runDuperInstance46 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := true) (selFunction := some 13)

/-- Same as duper instance 23 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = true
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = false -/
def runDuperInstance47 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := true) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 2)

/-- Same as duper instance 24 except includeExpensiveRules is set to false. Has the following options:
    - preprocessing = monomorphization
    - inhabitationReasoning = false
    - selFunction = 2 (NoSelection)
    - includeExpensiveRules = false -/
def runDuperInstance48 (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (instanceMaxHeartbeats : Nat) : MetaM Expr :=
  mkDuperInstance formulas declName? instanceMaxHeartbeats (inhabitationReasoning := false) (preprocessing := Monomorphization)
    (includeExpensiveRules := false) (selFunction := some 2)

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
  | 17 => return false
  | 18 => return true
  | 19 => return false
  | 20 => return true
  | 21 => return false
  | 22 => return true
  | 23 => return true
  | 24 => return false
  | 25 => return false
  | 26 => return true
  | 27 => return false
  | 28 => return true
  | 29 => return false
  | 30 => return true
  | 31 => return true
  | 32 => return false
  | 33 => return false
  | 34 => return true
  | 35 => return false
  | 36 => return true
  | 37 => return false
  | 38 => return true
  | 39 => return true
  | 40 => return false
  | 41 => return false
  | 42 => return true
  | 43 => return false
  | 44 => return true
  | 45 => return false
  | 46 => return true
  | 47 => return true
  | 48 => return false
  | _ => throwError "Invalid duper instance {n}"

/-- If the given duper instance `n` has inhabitation reasoning disabled and there is another instance `m` that is identical
    except that it has inhabitation reasoning enabled, then `getInstanceWithInhabitationReasoning` returns `some m`. Otherwise,
    `getInstanceWithInhabitationReasoning` returns `none`. -/
def getInstanceWithInhabitationReasoning (n : Nat) : Option (Nat × (List (Expr × Expr × Array Name × Bool) → Option Name → Nat → MetaM Expr)) := do
  match n with
  | 1 => some (2, runDuperInstance2)
  | 3 => some (4, runDuperInstance4)
  | 5 => some (6, runDuperInstance6)
  | 8 => some (7, runDuperInstance7)
  | 9 => some (10, runDuperInstance10)
  | 11 => some (12, runDuperInstance12)
  | 13 => some (14, runDuperInstance14)
  | 16 => some (15, runDuperInstance15)
  | 17 => some (18, runDuperInstance18)
  | 19 => some (20, runDuperInstance20)
  | 21 => some (22, runDuperInstance22)
  | 24 => some (23, runDuperInstance23)
  | 25 => some (26, runDuperInstance26)
  | 27 => some (28, runDuperInstance28)
  | 29 => some (30, runDuperInstance30)
  | 32 => some (31, runDuperInstance31)
  | 33 => some (34, runDuperInstance34)
  | 35 => some (36, runDuperInstance36)
  | 37 => some (38, runDuperInstance38)
  | 40 => some (39, runDuperInstance39)
  | 41 => some (42, runDuperInstance42)
  | 43 => some (44, runDuperInstance44)
  | 45 => some (46, runDuperInstance46)
  | 48 => some (47, runDuperInstance47)
  | _ => none

/-- If the given duper instance `n` has inhabitation reasoning enabled and there is another instance `m` that is identical
    except that it has inhabitation reasoning disabled, then `getInstanceWithoutInhabitationReasoning` returns `some m`. Otherwise,
    `getInstanceWithoutInhabitationReasoning` returns `none`. -/
def getInstanceWithoutInhabitationReasoning (n : Nat) : Option (Nat × (List (Expr × Expr × Array Name × Bool) → Option Name → Nat → MetaM Expr)) := do
  match n with
  | 2 => some (1, runDuperInstance1)
  | 4 => some (3, runDuperInstance3)
  | 6 => some (5, runDuperInstance5)
  | 7 => some (8, runDuperInstance8)
  | 10 => some (9, runDuperInstance9)
  | 12 => some (11, runDuperInstance11)
  | 14 => some (13, runDuperInstance13)
  | 15 => some (16, runDuperInstance16)
  | 18 => some (17, runDuperInstance17)
  | 20 => some (19, runDuperInstance19)
  | 22 => some (21, runDuperInstance21)
  | 23 => some (24, runDuperInstance24)
  | 26 => some (25, runDuperInstance25)
  | 28 => some (27, runDuperInstance27)
  | 30 => some (29, runDuperInstance29)
  | 31 => some (32, runDuperInstance32)
  | 34 => some (33, runDuperInstance33)
  | 36 => some (35, runDuperInstance35)
  | 38 => some (37, runDuperInstance37)
  | 39 => some (40, runDuperInstance40)
  | 42 => some (41, runDuperInstance41)
  | 44 => some (43, runDuperInstance43)
  | 46 => some (45, runDuperInstance45)
  | 47 => some (48, runDuperInstance48)
  | _ => none

/-- If the given duper instance `n` has includeExpensiveRules set to false and there is another instance `m` that is identical
    except that it has includeExpensiveRules set to true, then `getInstanceWithExpensiveRules` returns `some m`. Otherwise,
    `getInstanceWithExpensiveRules` returns `none`. -/
def getInstanceWithExpensiveRules (n : Nat) : Option (Nat × (List (Expr × Expr × Array Name × Bool) → Option Name → Nat → MetaM Expr)) := do
  match n with
  | 1 => some (25, runDuperInstance25)
  | 2 => some (26, runDuperInstance26)
  | 5 => some (29, runDuperInstance29)
  | 6 => some (30, runDuperInstance30)
  | 9 => some (33, runDuperInstance33)
  | 10 => some (34, runDuperInstance34)
  | 13 => some (37, runDuperInstance37)
  | 14 => some (38, runDuperInstance38)
  | 17 => some (41, runDuperInstance41)
  | 18 => some (42, runDuperInstance42)
  | 21 => some (45, runDuperInstance45)
  | 22 => some (46, runDuperInstance46)
  | 27 => some (3, runDuperInstance3)
  | 28 => some (4, runDuperInstance4)
  | 31 => some (7, runDuperInstance7)
  | 32 => some (8, runDuperInstance8)
  | 35 => some (11, runDuperInstance11)
  | 36 => some (12, runDuperInstance12)
  | 39 => some (15, runDuperInstance15)
  | 40 => some (16, runDuperInstance16)
  | 43 => some (19, runDuperInstance19)
  | 44 => some (20, runDuperInstance20)
  | 47 => some (23, runDuperInstance23)
  | 48 => some (24, runDuperInstance24)
  | _ => none

/-- If the given duper instance `n` has includeExpensiveRules set to true and there is another instance `m` that is identical
    except that it has includeExpensiveRules set to false, then `getInstanceWithoutExpensiveRules` returns `some m`. Otherwise,
    `getInstanceWithoutExpensiveRules` returns `none`. -/
def getInstanceWithoutExpensiveRules (n : Nat) : Option (Nat × (List (Expr × Expr × Array Name × Bool) → Option Name → Nat → MetaM Expr)) := do
  match n with
  | 25 => some (1, runDuperInstance1)
  | 26 => some (2, runDuperInstance2)
  | 29 => some (5, runDuperInstance5)
  | 30 => some (6, runDuperInstance6)
  | 33 => some (9, runDuperInstance9)
  | 34 => some (10, runDuperInstance10)
  | 37 => some (13, runDuperInstance13)
  | 38 => some (14, runDuperInstance14)
  | 41 => some (17, runDuperInstance17)
  | 42 => some (18, runDuperInstance18)
  | 45 => some (21, runDuperInstance21)
  | 46 => some (22, runDuperInstance22)
  | 3 => some (27, runDuperInstance27)
  | 4 => some (28, runDuperInstance28)----
  | 7 => some (31, runDuperInstance31)
  | 8 => some (32, runDuperInstance32)
  | 11 => some (35, runDuperInstance35)
  | 12 => some (36, runDuperInstance36)
  | 15 => some (39, runDuperInstance39)
  | 16 => some (40, runDuperInstance40)
  | 19 => some (43, runDuperInstance43)
  | 20 => some (44, runDuperInstance44)
  | 23 => some (47, runDuperInstance47)
  | 24 => some (48, runDuperInstance48)
  | _ => none

/-- Implements duper calls when portfolio mode is enabled. If `duperStxInfo` is not none and `runDuperPortfolioMode` succeeds in deriving
    a contradiction, then `Std.Tactic.TryThis.addSuggestion` will be used to give the user a more specific invocation of duper that can
    reproduce the proof (without having to run duper in portfolio mode). As with the other `runDuper` functions, `runDuperPortfolioMode`
    ultimately returns a proof if successful and throws an error if unsuccessful. -/
def runDuperPortfolioMode (formulas : List (Expr × Expr × Array Name × Bool)) (declName? : Option Name) (configOptions : ConfigurationOptions)
  (duperStxInfo : Option (Syntax × Syntax × Syntax.TSepArray `term ","  × Bool)) : MetaM Expr := do
  let initHeartbeats ← IO.getNumHeartbeats
  let maxHeartbeats ← getMaxHeartbeats
  -- Use the preprocessing option to determine the set of portfolio instances
  let instances :=
    match configOptions.preprocessing with
    | none =>
      #[(1, runDuperInstance1 formulas declName?),
        (3, runDuperInstance3 formulas declName?),
        (7, runDuperInstance7 formulas declName?)]
    | some FullPreprocessing => -- Replace instance 7 which has preprocessing disabled
      #[(1, runDuperInstance1 formulas declName?),
        (3, runDuperInstance3 formulas declName?),
        (15, runDuperInstance15 formulas declName?)]
    | some NoPreprocessing => -- Replaces instances 1 and 3 which have full preprocessing enabled
      #[(9, runDuperInstance9 formulas declName?),
        (11, runDuperInstance11 formulas declName?),
        (7, runDuperInstance7 formulas declName?)]
    | some Monomorphization => -- Replace all instances with corresponding instances that have only monomorphization enabled
      #[(17, runDuperInstance17 formulas declName?),
        (19, runDuperInstance19 formulas declName?),
        (23, runDuperInstance23 formulas declName?)]
  let numInstances := instances.size
  let mut maxInstanceHeartbeats := maxHeartbeats / numInstances -- Allocate total heartbeats among all instances
  let mut numInstancesTried := 0
  let mut inhabitationReasoningEnabled := configOptions.inhabitationReasoning
  let mut moreTimeMayHelp := false -- This variable is set to false initially, but as soon as any instance fails due to timeout, it is set to true
  for (duperInstanceNum, duperInstanceFn) in instances do
    -- If inhabitationReasoning is explicitly specified, modify the current instance to ensure that inhabitationReasoning is set appropriately
    let (duperInstanceNum, duperInstanceFn) :=
      match inhabitationReasoningEnabled with
      | none => (duperInstanceNum, duperInstanceFn)
      | some true =>
        /- If inhabitationReasoning is explicitly enabled and duperInstanceNum has inhabitation reasoning disabled, then replace the
           current duper instance with the corresponding instance that has inhabitation reasoning enabled -/
        match getInstanceWithInhabitationReasoning duperInstanceNum with
        | none => (duperInstanceNum, duperInstanceFn)
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas declName?)
      | some false =>
        /- If inhabitationReasoning is explicitly disabled and duperInstanceNum has inhabitation reasoning enabled, then replace the
           current duper instance with the corresponding instance that has inhabitation reasoning disabled -/
        match getInstanceWithoutInhabitationReasoning duperInstanceNum with
        | none => (duperInstanceNum, duperInstanceFn)
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas declName?)
    -- If includeExpensiveRules is explicitly specified, modify the current instance to ensure that includeExpensiveRules is set appropriately
    let (duperInstanceNum, duperInstanceFn) :=
      match configOptions.includeExpensiveRules with
      | none => (duperInstanceNum, duperInstanceFn)
      | some true =>
        /- If includeExpensiveRules is explicitly enabled and duperInstanceNum has includeExpensiveRules disabled, then replace the
           current duper instance with the corresponding instance that has includeExpensiveRules enabled -/
        match getInstanceWithExpensiveRules duperInstanceNum with
        | none => (duperInstanceNum, duperInstanceFn)
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas declName?)
      | some false =>
        /- If includeExpensiveRules is explicitly disabled and duperInstanceNum has includeExpensiveRules enabled, then replace the
           current duper instance with the corresponding instance that has includeExpensiveRules disabled -/
        match getInstanceWithoutExpensiveRules duperInstanceNum with
        | none => (duperInstanceNum, duperInstanceFn)
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas declName?)
    /- If Duper finds a contradiction and successfully performs proof reconstruction, `proofOption` will be `some proof` and
       `retryWithInhabitationReasoning` will be false.

       If Duper saturates or fails proof reconstruction specifically because inhabitation reasoning is disabled, `proofOption`
       will be `none` and `retryWithInhabitationReasoning` will be true.

       If Duper times out (achieving ProverM.Result.unknown and throwing the error "Duper was terminated.") then `proofOption`
       will be `none` and `retryWithInhabitationReasoning` will be false.

       If Duper fails for any other reason, then Duper will either continue to the next instance or throw an error depending on
       the `throwPortfolioErrors` option. -/
    let (proofOption, retryWithInhabitationReasoning) ←
      try
        let proof ← duperInstanceFn maxInstanceHeartbeats
        pure $ (some proof, false)
      catch e =>
        let errorMessage ← e.toMessageData.toString
        if errorMessage.startsWith "instantiatePremises :: Failed to find instance for" then
          if (inhabitationReasoningEnabled = some true) || (← instanceHasInhabitationReasoning duperInstanceNum) then
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
        else if errorMessage.startsWith "Duper was terminated" then
          moreTimeMayHelp := true
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
        | some (newDuperInstanceNum, newDuperInstanceFn) => (newDuperInstanceNum, newDuperInstanceFn formulas declName?)
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
          if (← e.toMessageData.toString).startsWith "Duper was terminated" then
            moreTimeMayHelp := true
            pure none -- Duper instance just timed out, try again with the next instance
          else if ← getThrowPortfolioErrorsM then
            throw e -- Error unrelated to timeout, and inhabitation reasoning is already enabled, so throw the error
          else -- Even though the instance threw an error, the throwPortfolioErrors option is set to false, so keep trying other instances
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
  if moreTimeMayHelp then
    throwError
      m!"Duper encountered a (deterministic) timeout. The maximum number of heartbeats {maxHeartbeats / 1000} " ++
      m!"has been reached (use 'set_option maxHeartbeats <num>' to set the limit)"
  else
    throwError
      m!"Duper failed to solve the goal and determined that it will be unable to do so with the current " ++
      m!"configuration of options and selection of premises"
