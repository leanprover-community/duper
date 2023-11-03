import Lean
import Duper.Interface

open Lean
open Lean.Meta
open Duper
open ProverM
open Lean.Parser

initialize
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

namespace Lean.Elab.Tactic

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
        let redExpr ← Core.betaReduce redExpr
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
    match expr with
    | .const exprConstName _ =>
      match (← getEnv).find? exprConstName with
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
        if let some eqns ← getEqnsFor? exprConstName (nonRec := true) then
          ret := ret.append (← eqns.mapM fun eq => do elabFactAux (← `($(mkIdent eq))))
        return ret
      | some (.axiomInfo _)  => return #[← elabFactAux stx]
      | some (.thmInfo _)    => return #[← elabFactAux stx]
      | some (.opaqueInfo _) => throwError "Opaque constants cannot be provided as facts"
      | some (.quotInfo _)   => throwError "Quotient constants cannot be provided as facts"
      | some (.inductInfo _) => throwError "Inductive types cannot be provided as facts"
      | some (.ctorInfo _)   => throwError "Constructors cannot be provided as facts"
      | none                 => throwError "Unknown constant {id}"
    | .fvar exprFVarId =>
      match (← getLCtx).find? exprFVarId with
      | some _ => return #[← elabFactAux stx]
      | none => throwError "Unknown fvar {id}"
    | _ => throwError "Unknown identifier {id}"
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

def collectAssumptions (facts : Array Term) (withAllLCtx : Bool) (goalDecls : Array LocalDecl) : TacticM (List (Expr × Expr × Array Name)) := do
  let mut formulas := []
  if withAllLCtx then -- Load all local decls
    for fVarId in (← getLCtx).getFVarIds do
      let ldecl ← Lean.FVarId.getDecl fVarId
      unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
        let ldecltype ← preprocessFact (← instantiateMVars ldecl.type)
        formulas := (ldecltype, ← mkAppM ``eq_true #[mkFVar fVarId], #[]) :: formulas
  else -- Even if withAllLCtx is false, we still need to load the goal decls
    for ldecl in goalDecls do
      unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
        let ldecltype ← preprocessFact (← instantiateMVars ldecl.type)
        formulas := (ldecltype, ← mkAppM ``eq_true #[mkFVar ldecl.fvarId], #[]) :: formulas
  -- Load user-provided facts
  for factStx in facts do
    for (fact, proof, params) in ← elabFact factStx do
      if ← isProp fact then
        let fact ← preprocessFact (← instantiateMVars fact)
        formulas := (fact, ← mkAppM ``eq_true #[proof], params) :: formulas
      else
        throwError "Invalid fact {factStx} for duper. Proposition expected"
  return formulas

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

syntax duperStar := "*"
syntax (name := duper) "duper" (ppSpace "[" (duperStar <|> term),* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic
syntax (name := duperTrace) "duper?" (ppSpace "[" (duperStar <|> term),* "]")? (ppSpace "{"Duper.configOption,*,?"}")? : tactic

macro_rules
| `(tactic| duper) => `(tactic| duper [] {}) -- Missing both facts and config options
| `(tactic| duper [$facts,*]) => `(tactic| duper [$facts,*] {}) -- Mising just config options
| `(tactic| duper {$configOptions,*}) => `(tactic| duper [] {$configOptions,*}) -- Missing just facts

macro_rules
| `(tactic| duper?) => `(tactic| duper? [] {}) -- Missing both facts and config options
| `(tactic| duper? [$facts,*]) => `(tactic| duper? [$facts,*] {}) -- Mising just config options
| `(tactic| duper? {$configOptions,*}) => `(tactic| duper? [] {$configOptions,*}) -- Missing just facts

/-- Given a Syntax.TSepArray of facts provided by the user (which may include `*` to indicate that duper should read in the
    full local context) `removeDuperStar` returns the Syntax.TSepArray with `*` removed and a boolean that indicates whether `*`
    was included in the original input. -/
def removeDuperStar (facts : Syntax.TSepArray [`Lean.Elab.Tactic.duperStar, `term] ",") : Bool × Syntax.TSepArray `term "," := Id.run do
  let factsArr := facts.elemsAndSeps -- factsArr contains both the elements of facts and separators, ordered like `#[e1, s1, e2, s2, e3]`
  let mut newFactsArr : Array Syntax := #[]
  let mut removedDuperStar := false
  let mut needToRemoveSeparator := false -- If `*` is removed, its comma also needs to be removed to preserve the elemsAndSeps ordering
  for fact in factsArr do
    match fact with
    | `(duperStar| *) =>
      removedDuperStar := true
      needToRemoveSeparator := true
    | _ =>
      if needToRemoveSeparator then needToRemoveSeparator := false -- Don't push current separator onto newFactsArr
      else newFactsArr := newFactsArr.push fact
  if removedDuperStar && needToRemoveSeparator then -- This can occur if `*` was the last or only element of facts
    return (removedDuperStar, {elemsAndSeps := newFactsArr.pop}) -- Remove the last extra separator in newFactsArr, if it exists
  else
    return (removedDuperStar, {elemsAndSeps := newFactsArr})

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
  (withDuperStar : Bool) (portfolioInstance : Nat) (inhabitationReasoning : Option Bool) : TacticM Unit := do
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
    reproduce the proof (without having to run duper in portfolio mode) -/
def runDuperPortfolioMode (formulas : List (Expr × Expr × Array Name)) (configOptions : ConfigurationOptions) (startTime : Nat)
  (duperStxInfo : Option (Syntax × Syntax × Syntax.TSepArray `term ","  × Bool)) : TacticM Unit := do
  let maxHeartbeats ← getMaxHeartbeats
  let instances :=
    #[(0, runDuperInstance0 formulas),
      (1, runDuperInstance1 formulas),
      (2, runDuperInstance2 formulas),
      (3, runDuperInstance3 formulas),
      (4, runDuperInstance4 formulas)]
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
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      if ← getPrintPortfolioInstanceM then IO.println s!"Solved by Duper instance {duperInstanceNum}"
      match duperStxInfo with
      | none => return
      | some (duperStxRef, origSpan, facts, withDuperStar) =>
        mkDuperCallSuggestion duperStxRef origSpan facts withDuperStar duperInstanceNum inhabitationReasoningEnabled
        return
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
        Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
        if ← getPrintPortfolioInstanceM then IO.println s!"Solved by Duper instance {duperInstanceNum}"
        match duperStxInfo with
        | none => return
        | some (duperStxRef, origSpan, facts, withDuperStar) =>
          mkDuperCallSuggestion duperStxRef origSpan facts withDuperStar duperInstanceNum inhabitationReasoningEnabled
          return
      | none => continue -- Duper timed out, try the next instance
  throwError "Prover ran out of time before solving the goal"

/-- When `duper` is called, the first thing the tactic does is call the tactic `intros; apply Classical.byContradiction _; intro`.
    Even when `*` is not included in the duper invocation (meaning the user does not want duper to collect all the facts in the
    local context), it is necessary to include the negated goal. This negated goal may take the form of arbitrarily many
    declarations in the local context if the `duper` is asked to solve a goal of the form `p1 → p2 → p3 → ... pn`. So to ensure
    that `duper` is able to see the whole original goal, `getGoalDecls` compares the local context before calling
    `intros; apply Classical.byContradiction _; intro` and after calling `intros; apply Classical.byContradiction _; intro`. The
    local declarations that are part of the latter lctx but not the former are considered goal decls and are to be returned so that
    Duper can know to collect them in `collectAssumptions`.-/
def getGoalDecls (lctxBeforeIntros : LocalContext) (lctxAfterIntros : LocalContext) : Array LocalDecl := Id.run do
  let mut goalDecls := #[]
  for declOpt in lctxAfterIntros.decls do
    match declOpt with
    | none => continue
    | some decl =>
      if lctxBeforeIntros.contains decl.fvarId then continue
      else goalDecls := goalDecls.push decl
  return goalDecls

@[tactic duper]
def evalDuper : Tactic
| `(tactic| duper [$facts,*] {$configOptions,*}) => withMainContext do
  let startTime ← IO.monoMsNow
  let configOptions ← parseConfigOptions configOptions
  let (factsContainsDuperStar, facts) := removeDuperStar facts
  let lctxBeforeIntros ← getLCtx
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let lctxAfterIntros ← getLCtx
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let formulas ← collectAssumptions facts factsContainsDuperStar goalDecls
    if configOptions.portfolioMode then
      runDuperPortfolioMode formulas configOptions startTime none
      IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    else
      let portfolioInstance ←
        match configOptions.portfolioInstance with
        | some portfolioInstance => pure portfolioInstance
        | none => throwError "parseConfigOptions error: portfolio mode is disabled and no portfolio instance is specified"
      let proof ←
        match portfolioInstance with
        | 0 => runDuperInstance0 formulas configOptions.inhabitationReasoning 0
        | 1 => runDuperInstance1 formulas configOptions.inhabitationReasoning 0
        | 2 => runDuperInstance2 formulas configOptions.inhabitationReasoning 0
        | 3 => runDuperInstance3 formulas configOptions.inhabitationReasoning 0
        | 4 => runDuperInstance4 formulas configOptions.inhabitationReasoning 0
        | _ => throwError "Portfolio instance {portfolioInstance} not currently defined. Please choose instance 0-4"
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
| _ => throwUnsupportedSyntax

@[tactic duperTrace]
def evalDuperTrace : Tactic
| `(tactic| duper?%$duperStxRef [$facts,*] {$configOptions,*}) => withMainContext do
  let startTime ← IO.monoMsNow
  let configOptions ← parseConfigOptions configOptions
  let (factsContainsDuperStar, facts) := removeDuperStar facts
  let lctxBeforeIntros ← getLCtx
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let lctxAfterIntros ← withMainContext getLCtx
    let goalDecls := getGoalDecls lctxBeforeIntros lctxAfterIntros
    let formulas ← collectAssumptions facts factsContainsDuperStar goalDecls
    if configOptions.portfolioMode then
      runDuperPortfolioMode formulas configOptions startTime (some (duperStxRef, ← getRef, facts, factsContainsDuperStar))
      IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    else
      let portfolioInstance ←
        match configOptions.portfolioInstance with
        | some portfolioInstance => pure portfolioInstance
        | none => throwError "parseConfigOptions error: portfolio mode is disabled and no portfolio instance is specified"
      let proof ←
        match portfolioInstance with
        | 0 => runDuperInstance0 formulas configOptions.inhabitationReasoning 0
        | 1 => runDuperInstance1 formulas configOptions.inhabitationReasoning 0
        | 2 => runDuperInstance2 formulas configOptions.inhabitationReasoning 0
        | 3 => runDuperInstance3 formulas configOptions.inhabitationReasoning 0
        | 4 => runDuperInstance4 formulas configOptions.inhabitationReasoning 0
        | _ => throwError "Portfolio instance {portfolioInstance} not currently defined. Please choose instance 0-4"
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      mkDuperCallSuggestion duperStxRef (← getRef) facts factsContainsDuperStar portfolioInstance configOptions.inhabitationReasoning
      IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
| _ => throwUnsupportedSyntax

syntax (name := duper_no_timing) "duper_no_timing" ("[" term,* "]")? : tactic

macro_rules
| `(tactic| duper_no_timing) => `(tactic| duper_no_timing [])

@[tactic duper_no_timing]
def evalDuperNoTiming : Tactic
| `(tactic| duper_no_timing [$facts,*]) => withMainContext do
  Elab.Tactic.evalTactic (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let (_, facts) := removeDuperStar facts
    let formulas ← collectAssumptions facts true  #[] -- I don't bother computing goalDecls here since I set withAllLCtx to true anyway
    let proof ← runDuper formulas 0
    Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
    IO.println s!"Constructed proof"
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
