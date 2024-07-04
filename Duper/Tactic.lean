import Lean
import Duper.Interface

open Lean
open Lean.Meta
open Duper
open ProverM
open Lean.Parser

namespace Lean.Elab.Tactic

register_option duper.printTimeInformation : Bool := {
  defValue := false
  descr := "Whether to print the total time it took for Duper to construct a proof"
}

def getPrintTimeInformation (opts : Options) : Bool :=
  duper.printTimeInformation.get opts

def getPrintTimeInformationM : CoreM Bool := do
  let opts ← getOptions
  return getPrintTimeInformation opts

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
    let inductTyArgs : Array Expr := xs[:indVal.numParams]
    return ← indVal.ctors.mapM fun ctorName => do
      let ctor ← mkAppOptM ctorName (inductTyArgs.map Option.some)
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
  for (type, proof, _) in res do
    let ty' ← Meta.inferType proof
    if !(← Meta.isDefEq ty' type) then
      throwError "addRecAsFact :: Application type mismatch"
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
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let abstres ← Duper.abstractMVars e
    let e := abstres.expr
    let paramNames := abstres.paramNames
    return (← inferType e, e, paramNames)

def collectAssumptions (facts : Array Term) (withAllLCtx : Bool) (goalDecls : Array LocalDecl) : TacticM (List (Expr × Expr × Array Name × Bool)) := do
  let mut formulas := []
  if withAllLCtx then -- Load all local decls
    for fVarId in (← getLCtx).getFVarIds do
      let ldecl ← Lean.FVarId.getDecl fVarId
      unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
        let ldecltype ← preprocessFact (← instantiateMVars ldecl.type)
        let isFromGoal := goalDecls.any (fun goalDecl => goalDecl.index = ldecl.index)
        formulas := (ldecltype, ← mkAppM ``eq_true #[mkFVar fVarId], #[], isFromGoal) :: formulas
  else -- Even if withAllLCtx is false, we still need to load the goal decls
    for ldecl in goalDecls do
      unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
        let ldecltype ← preprocessFact (← instantiateMVars ldecl.type)
        formulas := (ldecltype, ← mkAppM ``eq_true #[mkFVar ldecl.fvarId], #[], true) :: formulas
  -- Load user-provided facts
  for factStx in facts do
    for (fact, proof, params) in ← elabFact factStx do
      if ← isProp fact then
        let fact ← preprocessFact (← instantiateMVars fact)
        formulas := (fact, ← mkAppM ``eq_true #[proof], params, false) :: formulas
      else
        throwError "Invalid fact {factStx} for duper. Proposition expected"
  return formulas

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
def removeDuperStar (facts : Syntax.TSepArray [`duperStar, `term] ",") : Bool × Syntax.TSepArray `term "," := Id.run do
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
    - Sets other options to none by default

    Additionally, this function throws an error if the user attempts to explicitly enable portfolio mode and specify a portfolio instance,
    and it throws a warning if the user attempts to specify a portfolio instance (other than 0) and additional configuration options. -/
def parseConfigOptions (configOptionsStx : TSyntaxArray `Duper.configOption) : TacticM ConfigurationOptions := do
  let mut portfolioModeOpt : Option Bool := none
  let mut portfolioInstanceOpt : Option Nat := none
  let mut inhabitationReasoningOpt : Option Bool := none
  let mut preprocessingOpt : Option PreprocessingOption := none
  let mut includeExpensiveRulesOpt : Option Bool := none
  let mut selFunctionOpt : Option Nat := none
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
    | `(configOption| preprocessing := $preprocessingStx:Duper.preprocessing_option) =>
      if preprocessingOpt.isSome then
        throwError "Erroneous invocation of duper: The preprocessing option has been specified multiple times"
      let preprocessing ← elabPreprocessingOption preprocessingStx
      preprocessingOpt := some preprocessing
    | `(configOption| includeExpensiveRules := $includeExpensiveRulesStx:Duper.bool_lit) =>
      if includeExpensiveRulesOpt.isSome then
        throwError "Erroneous invocation of duper: The includeExpensiveRules option has been specified multiple times"
      let includeExpensiveRules ← elabBoolLit includeExpensiveRulesStx
      includeExpensiveRulesOpt := some includeExpensiveRules
    | `(configOption| selFunction := $selFunctionStx) =>
      if selFunctionOpt.isSome then
        throwError "Erroneous invocation of duper: The selFunction option has been specified multiple times"
      let selFunction := selFunctionStx.getNat
      selFunctionOpt := some selFunction
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
  if portfolioInstance != none && portfolioInstance != some 0 then
    if inhabitationReasoningOpt.isSome || preprocessingOpt.isSome || includeExpensiveRulesOpt.isSome then
      IO.println s!"Warning: The specified portfolio instance {portfolioInstance.get!} will override all additional configuration options"
  return {
    portfolioMode := portfolioMode,
    portfolioInstance := portfolioInstance,
    inhabitationReasoning := inhabitationReasoningOpt,
    preprocessing := preprocessingOpt,
    includeExpensiveRules := includeExpensiveRulesOpt,
    selFunction := selFunctionOpt
  }

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
    let declName? ← Elab.Term.getDeclName? -- Needed for `Auto.monoPrepInterface`
    if configOptions.portfolioMode then
      let proof ← runDuperPortfolioMode formulas declName? configOptions none
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      if ← getPrintTimeInformationM then
        IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    else
      let portfolioInstance ←
        match configOptions.portfolioInstance with
        | some portfolioInstance => pure portfolioInstance
        | none => throwError "parseConfigOptions error: portfolio mode is disabled and no portfolio instance is specified"
      let proof ←
        match portfolioInstance with
        | 0 =>
          mkDuperInstance formulas declName? 0 configOptions.inhabitationReasoning configOptions.preprocessing
            configOptions.includeExpensiveRules configOptions.selFunction
        | 1 => runDuperInstance1 formulas declName? 0
        | 2 => runDuperInstance2 formulas declName? 0
        | 3 => runDuperInstance3 formulas declName? 0
        | 4 => runDuperInstance4 formulas declName? 0
        | 5 => runDuperInstance5 formulas declName? 0
        | 6 => runDuperInstance6 formulas declName? 0
        | 7 => runDuperInstance7 formulas declName? 0
        | 8 => runDuperInstance8 formulas declName? 0
        | 9 => runDuperInstance9 formulas declName? 0
        | 10 => runDuperInstance10 formulas declName? 0
        | 11 => runDuperInstance11 formulas declName? 0
        | 12 => runDuperInstance12 formulas declName? 0
        | 13 => runDuperInstance13 formulas declName? 0
        | 14 => runDuperInstance14 formulas declName? 0
        | 15 => runDuperInstance15 formulas declName? 0
        | 16 => runDuperInstance16 formulas declName? 0
        | 17 => runDuperInstance17 formulas declName? 0
        | 18 => runDuperInstance18 formulas declName? 0
        | 19 => runDuperInstance19 formulas declName? 0
        | 20 => runDuperInstance20 formulas declName? 0
        | 21 => runDuperInstance21 formulas declName? 0
        | 22 => runDuperInstance22 formulas declName? 0
        | 23 => runDuperInstance23 formulas declName? 0
        | 24 => runDuperInstance24 formulas declName? 0
        | 25 => runDuperInstance25 formulas declName? 0
        | 26 => runDuperInstance26 formulas declName? 0
        | 27 => runDuperInstance27 formulas declName? 0
        | 28 => runDuperInstance28 formulas declName? 0
        | 29 => runDuperInstance29 formulas declName? 0
        | 30 => runDuperInstance30 formulas declName? 0
        | 31 => runDuperInstance31 formulas declName? 0
        | 32 => runDuperInstance32 formulas declName? 0
        | 33 => runDuperInstance33 formulas declName? 0
        | 34 => runDuperInstance34 formulas declName? 0
        | 35 => runDuperInstance35 formulas declName? 0
        | 36 => runDuperInstance36 formulas declName? 0
        | 37 => runDuperInstance37 formulas declName? 0
        | 38 => runDuperInstance38 formulas declName? 0
        | 39 => runDuperInstance39 formulas declName? 0
        | 40 => runDuperInstance40 formulas declName? 0
        | 41 => runDuperInstance41 formulas declName? 0
        | 42 => runDuperInstance42 formulas declName? 0
        | 43 => runDuperInstance43 formulas declName? 0
        | 44 => runDuperInstance44 formulas declName? 0
        | 45 => runDuperInstance45 formulas declName? 0
        | 46 => runDuperInstance46 formulas declName? 0
        | 47 => runDuperInstance47 formulas declName? 0
        | 48 => runDuperInstance48 formulas declName? 0
        | _ => throwError "Portfolio instance {portfolioInstance} not currently defined"
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      if ← getPrintTimeInformationM then
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
    let declName? ← Elab.Term.getDeclName? -- Needed for `Auto.monoPrepInterface`
    if configOptions.portfolioMode then
      let proof ← runDuperPortfolioMode formulas declName? configOptions (some (duperStxRef, ← getRef, facts, factsContainsDuperStar))
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      if ← getPrintTimeInformationM then
        IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    else
      let portfolioInstance ←
        match configOptions.portfolioInstance with
        | some portfolioInstance => pure portfolioInstance
        | none => throwError "parseConfigOptions error: portfolio mode is disabled and no portfolio instance is specified"
      let proof ←
        match portfolioInstance with
        | 0 =>
          mkDuperInstance formulas declName? 0 configOptions.inhabitationReasoning configOptions.preprocessing
            configOptions.includeExpensiveRules configOptions.selFunction
        | 1 => runDuperInstance1 formulas declName? 0
        | 2 => runDuperInstance2 formulas declName? 0
        | 3 => runDuperInstance3 formulas declName? 0
        | 4 => runDuperInstance4 formulas declName? 0
        | 5 => runDuperInstance5 formulas declName? 0
        | 6 => runDuperInstance6 formulas declName? 0
        | 7 => runDuperInstance7 formulas declName? 0
        | 8 => runDuperInstance8 formulas declName? 0
        | 9 => runDuperInstance9 formulas declName? 0
        | 10 => runDuperInstance10 formulas declName? 0
        | 11 => runDuperInstance11 formulas declName? 0
        | 12 => runDuperInstance12 formulas declName? 0
        | 13 => runDuperInstance13 formulas declName? 0
        | 14 => runDuperInstance14 formulas declName? 0
        | 15 => runDuperInstance15 formulas declName? 0
        | 16 => runDuperInstance16 formulas declName? 0
        | 17 => runDuperInstance17 formulas declName? 0
        | 18 => runDuperInstance18 formulas declName? 0
        | 19 => runDuperInstance19 formulas declName? 0
        | 20 => runDuperInstance20 formulas declName? 0
        | 21 => runDuperInstance21 formulas declName? 0
        | 22 => runDuperInstance22 formulas declName? 0
        | 23 => runDuperInstance23 formulas declName? 0
        | 24 => runDuperInstance24 formulas declName? 0
        | 25 => runDuperInstance25 formulas declName? 0
        | 26 => runDuperInstance26 formulas declName? 0
        | 27 => runDuperInstance27 formulas declName? 0
        | 28 => runDuperInstance28 formulas declName? 0
        | 29 => runDuperInstance29 formulas declName? 0
        | 30 => runDuperInstance30 formulas declName? 0
        | 31 => runDuperInstance31 formulas declName? 0
        | 32 => runDuperInstance32 formulas declName? 0
        | 33 => runDuperInstance33 formulas declName? 0
        | 34 => runDuperInstance34 formulas declName? 0
        | 35 => runDuperInstance35 formulas declName? 0
        | 36 => runDuperInstance36 formulas declName? 0
        | 37 => runDuperInstance37 formulas declName? 0
        | 38 => runDuperInstance38 formulas declName? 0
        | 39 => runDuperInstance39 formulas declName? 0
        | 40 => runDuperInstance40 formulas declName? 0
        | 41 => runDuperInstance41 formulas declName? 0
        | 42 => runDuperInstance42 formulas declName? 0
        | 43 => runDuperInstance43 formulas declName? 0
        | 44 => runDuperInstance44 formulas declName? 0
        | 45 => runDuperInstance45 formulas declName? 0
        | 46 => runDuperInstance46 formulas declName? 0
        | 47 => runDuperInstance47 formulas declName? 0
        | 48 => runDuperInstance48 formulas declName? 0
        | _ => throwError "Portfolio instance {portfolioInstance} not currently defined"
      Lean.MVarId.assign (← getMainGoal) proof -- Apply the discovered proof to the main goal
      mkDuperCallSuggestion duperStxRef (← getRef) facts factsContainsDuperStar portfolioInstance configOptions.inhabitationReasoning
        configOptions.preprocessing configOptions.includeExpensiveRules configOptions.selFunction
      if ← getPrintTimeInformationM then
        IO.println s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
| _ => throwUnsupportedSyntax

/-- Note: This tactic exists primarily for internal github testing and is not intended for external use. -/
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
