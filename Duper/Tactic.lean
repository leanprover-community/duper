import Lean
import Duper.Saturate
import Duper.Unif

open Lean
open Lean.Meta
open Duper
open ProverM
open Lean.Parser

initialize 
  registerTraceClass `TPTP_Testing
  registerTraceClass `Print_Proof
  registerTraceClass `Saturate.debug
  registerTraceClass `Unary_first.debug

namespace Lean.Elab.Tactic

partial def printProof (state : ProverM.State) : TacticM Unit := do
  Core.checkMaxHeartbeats "printProof"
  let rec go c (hm : Array (Nat × Clause) := {}) : TacticM (Array (Nat × Clause)) := do
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
  getClauseInfo! (c : Clause) : TacticM ClauseInfo := do
    let some ci := state.allClauses.find? c
      | throwError "clause info not found: {c}"
    return ci

def getClauseInfo! (state : ProverM.State) (c : Clause) : TacticM ClauseInfo := do
  let some ci := state.allClauses.find? c
    | throwError "clause info not found: {c}"
  return ci

partial def collectClauses (state : ProverM.State) (c : Clause) (acc : (Array Nat × ClauseHeap)) : TacticM (Array Nat × ClauseHeap) := do
  Core.checkMaxHeartbeats "collectClauses"
  let info ← getClauseInfo! state c
  if acc.1.contains info.number then return acc -- No need to recall collectClauses on c because we've already collected c
  let mut acc := acc
  -- recursive calls
  acc := (acc.1.push info.number, acc.2.insert (info.number, c))
  for proofParent in info.proof.parents do
    acc ← collectClauses state proofParent.clause acc
  return acc

partial def mkProof (state : ProverM.State) : List Clause → TacticM Expr
| [] => panic! "empty clause list"
| c :: cs => do
  Core.checkMaxHeartbeats "mkProof"
  let info ← getClauseInfo! state c
  let newTarget := c.toForallExpr
  let mut parents := []
  for parent in info.proof.parents do
    let number := (← getClauseInfo! state parent.clause).number
    parents := ((← getLCtx).findFromUserName? (Name.mkNum `clause number)).get!.toExpr :: parents
  parents := parents.reverse
  -- Now `parents[i] : info.proof.parents[i].toForallExpr`, for all `i`
  let mut lctx ← getLCtx
  let mut skdefs : List Expr := []
  for (fvarId, mkSkProof) in info.proof.introducedSkolems do
    trace[Print_Proof] "Reconstructing skolem, fvar = {mkFVar fvarId}"
    let ty := (state.lctx.get! fvarId).type
    trace[Meta.debug] "Reconstructing skolem, type = {ty}"
    let userName := (state.lctx.get! fvarId).userName
    trace[Print_Proof] "Reconstructed skloem, userName = {userName}"
    let skdef ← mkSkProof parents.toArray
    trace[Meta.debug] "Reconstructed skolem definition: {skdef}"
    trace[Meta.debug] "Reconstructed skolem definition, toString: {toString skdef}"
    skdefs := skdef :: skdefs
    lctx := lctx.mkLetDecl fvarId userName ty skdef
  let proof ← withLCtx lctx (← getLocalInstances) do
    trace[Meta.debug] "Reconstructing proof for #{info.number}: {c}, Rule Name: {info.proof.ruleName}"
    let newProof ← info.proof.mkProof parents info.proof.parents c
    trace[Meta.debug] "#{info.number}'s newProof: {newProof}"
    if cs == [] then return newProof
    let proof ←
      withLetDecl (Name.mkNum `clause info.number) newTarget newProof fun g => do
        let remainingProof ← mkProof state cs
        let mut remainingProof ← mkLambdaFVars (usedLetOnly := false) #[g] remainingProof
        for (fvarId, _) in info.proof.introducedSkolems do
          remainingProof ← mkLambdaFVars (usedLetOnly := false) #[mkFVar fvarId] remainingProof
        return remainingProof
    return proof
  return proof

def applyProof (state : ProverM.State) : TacticM Unit := do
  let l := (← collectClauses state Clause.empty (#[], Std.BinomialHeap.empty)).2.toList.eraseDups.map Prod.snd
  trace[Meta.debug] "{l}"
  let proof ← mkProof state l
  trace[Print_Proof] "Proof: {proof}"
  Lean.MVarId.assign (← getMainGoal) proof -- TODO: List.last?

def collectAssumptions (facts : Array Expr) : TacticM (List (Expr × Expr)) := do
  let mut formulas := []
  -- Load all local decls:
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← Lean.FVarId.getDecl fVarId
    unless ldecl.isAuxDecl ∨ not (← instantiateMVars (← inferType ldecl.type)).isProp do
      formulas := (← instantiateMVars ldecl.type, ← mkAppM ``eq_true #[mkFVar fVarId]) :: formulas
  -- load user-provided facts
  for fact in facts do
    let type ← inferType fact
    if ← isProp type then
      formulas := (type, ← mkAppM ``eq_true #[fact]) :: formulas
    else
      unless fact.isConst do
        throwError "invalid fact for duper, proposition expected{indentExpr type}"
      let declName := fact.constName!
      let unfoldEq? ← getUnfoldEqnFor? declName (nonRec := true)
      -- TODO: For definitions using "match", the equations are currently not usable
      match unfoldEq? with
      | some unfoldEq => do
        formulas := (← inferType (mkConst unfoldEq), ← mkAppM ``eq_true #[mkConst unfoldEq]) :: formulas
      | _ => throwError "Could not generate equation for {fact}"
  return formulas

/-- Returns the arity of e -/
partial def getArity (e : Expr) : Nat :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => 1 + getArity b
  | _ => 0

/-- Updates symbolFreqArityMap to increase the count of all symbols that appear in f (and if a symbol in f appears n
    times, then updates f's result in symbolFreqMap to be n greater than it was originally). Note that as with Expr.weight,
    this function may require revision to be more similar to Zipperposition's implementation once we actually start working
    on higher order things. -/
partial def updateSymbolFreqArityMap (f : Expr) (symbolFreqArityMap : HashMap Symbol (Nat × Nat)) :
  TacticM (HashMap Symbol (Nat × Nat)) := do
  match f with
  | Expr.fvar fVarId =>
    let fSymbol := Symbol.FVarId fVarId
    match symbolFreqArityMap.find? fSymbol with
    | some (fFreq, fArity) => return symbolFreqArityMap.insert fSymbol (fFreq + 1, fArity)
    | none =>
      match (← getLCtx).fvarIdToDecl.find? fVarId with
      | some fDecl =>
        let fType := LocalDecl.type fDecl
        return symbolFreqArityMap.insert fSymbol (1, getArity fType)
      | none => throwError s!"Unable to find {fVarId.name} in local context"
  | Expr.const name _ =>
    let fSymbol := Symbol.Const name
    match symbolFreqArityMap.find? fSymbol with
    | some (fFreq, fArity) => return symbolFreqArityMap.insert fSymbol (fFreq + 1, fArity)
    | none =>
      let fType ← inferType f
      return symbolFreqArityMap.insert fSymbol (1, getArity fType)
  | Expr.app f1 f2 =>
    let symbolFreqMap' ← updateSymbolFreqArityMap f1 symbolFreqArityMap
    updateSymbolFreqArityMap f2 symbolFreqMap'
  | Expr.lam _ t b _ =>
    let symbolFreqArityMap' ← updateSymbolFreqArityMap t symbolFreqArityMap
    updateSymbolFreqArityMap b symbolFreqArityMap'
  | Expr.forallE _ t b _ =>
    let symbolFreqArityMap' ← updateSymbolFreqArityMap t symbolFreqArityMap
    updateSymbolFreqArityMap b symbolFreqArityMap'
  | Expr.letE _ _ v b _ =>
    let symbolFreqMap' ← updateSymbolFreqArityMap v symbolFreqArityMap
    updateSymbolFreqArityMap b symbolFreqMap'
  | Expr.proj _ _ b => updateSymbolFreqArityMap b symbolFreqArityMap
  | Expr.mdata _ b => updateSymbolFreqArityMap b symbolFreqArityMap
  | Expr.sort .. => return symbolFreqArityMap
  | Expr.mvar .. => return symbolFreqArityMap
  | Expr.bvar .. => return symbolFreqArityMap
  | Expr.lit .. => return symbolFreqArityMap

/-- Builds a HashMap that maps each symbol to a tuple containing:
    - The number of times they appear in formulas
    - Its arity -/
partial def buildSymbolFreqArityMap (formulas : List Expr) : TacticM (HashMap Symbol (Nat × Nat)) := do
  let mut symbolFreqArityMap := HashMap.empty
  for f in formulas do
    symbolFreqArityMap ← updateSymbolFreqArityMap f symbolFreqArityMap
  trace[Unary_first.debug] "symbolFreqArityMap: {symbolFreqArityMap.toArray}"
  return symbolFreqArityMap

/-- Builds the symbolPrecMap from the input assumptions. Note that lower numbers in the symbol prec
    map correspond to higher precedences (so that symbol s is maximal iff s maps to 0) -/
def buildSymbolPrecMap (formulas : List Expr) : TacticM SymbolPrecMap := do
  let symbolFreqArityMap ← buildSymbolFreqArityMap formulas
  let mut symbolPrecArr : Array (Symbol × Nat × Nat) := #[]
  let lctx ← getLCtx
  -- unaryFirstGt sorts implements the greater-than test for the unary_first precedence generation scheme
  let unaryFirstGt : (Symbol × Nat × Nat) → (Symbol × Nat × Nat) → Bool :=
    fun (s1, s1Freq, s1Arity) (s2, s2Freq, s2Arity) =>
      if s1Arity == 1 && s2Arity != 1 then true
      else if s2Arity == 1 && s1Arity != 1 then false
      else if s1Arity > s2Arity then true
      else if s2Arity > s1Arity then false
      else -- s1Arity == s2Arity, so use frequency as a tie breaker (rarer symbols have greater precedence)
        if s1Freq < s2Freq then true
        else if s2Freq < s1Freq then false
        else -- Array.binInsert requires the lt define a total (rather than merely partial) ordering, so tiebreak by symbol
          match s1, s2 with
          | Symbol.FVarId _, Symbol.Const _ => true
          | Symbol.Const _, Symbol.FVarId _ => false
          | Symbol.Const c1, Symbol.Const c2 => c1.toString < c2.toString
          | Symbol.FVarId fVarId1, Symbol.FVarId fVarId2 =>
              -- Tiebreaking fVarId1 and fVarId2 by name would cause duper's behavior to depend on the environment in unexpected ways,
              -- so we instead tiebreak based on whether fVarId1 or fVarId2 appears first in the local context
              match lctx.fvarIdToDecl.toList.find? (fun (fVarId, _) => fVarId == fVarId1 || fVarId == fVarId2) with
              | some (firstFVarId, _) =>
                if firstFVarId == fVarId1 then true
                else false
              | none => false -- This case isn't possible because fVarId1 and fVarId2 must both appear in the local context
  for (s, sFreq, sArity) in symbolFreqArityMap.toArray do
    -- We use unaryFirstGt as the lt argument for binInsert so that symbols with higher precedence come first in symbolPrecArray
    symbolPrecArr := symbolPrecArr.binInsert unaryFirstGt (s, sFreq, sArity)
  trace[Unary_first.debug] "symbolPrecArr: {symbolPrecArr}"
  let mut symbolPrecMap := HashMap.empty
  let mut counter := 0
  for (s, _, _) in symbolPrecArr do
    symbolPrecMap := symbolPrecMap.insert s counter -- Map s to its index in symbolPrecArr
    counter := counter + 1
  trace[Unary_first.debug] "symbolPrecMap: {symbolPrecMap.toArray}"
  return symbolPrecMap

syntax (name := duper) "duper" (colGt ident)? ("[" term,* "]")? : tactic

macro_rules
| `(tactic| duper) => `(tactic| duper [])

@[tactic duper]
def evalDuper : Tactic
| `(tactic| duper [$facts,*]) => withMainContext do
  let startTime ← IO.monoMsNow
  Elab.Tactic.evalTactic
    (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let formulas ← collectAssumptions (← facts.getElems.mapM (elabTerm . none))
    trace[Meta.debug] "Formulas from collectAssumptions: {formulas}"
    let symbolPrecMap ← buildSymbolPrecMap (formulas.map (fun (formula, _) => formula))
    let (_, state) ←
      ProverM.runWithExprs (s := {symbolPrecMap := symbolPrecMap, lctx := ← getLCtx, mctx := ← getMCtx}) ProverM.saturate formulas
    match state.result with
    | Result.contradiction => do
        logInfo s!"Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
        trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
        printProof state
        applyProof state
        logInfo s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    | Result.saturated => 
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      trace[Saturate.debug] "Final set of all clauses: {Array.map (fun x => x.1) state.allClauses.toArray}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| `(tactic| duper $ident:ident [$facts,*]) => withMainContext do
  Elab.Tactic.evalTactic
    (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let formulas ← collectAssumptions (← facts.getElems.mapM (elabTerm . none))
    let symbolPrecMap ← buildSymbolPrecMap (formulas.map (fun (formula, _) => formula))
    let (_, state) ←
      ProverM.runWithExprs (s := {symbolPrecMap := symbolPrecMap, lctx := ← getLCtx, mctx := ← getMCtx}) ProverM.saturate formulas
    match state.result with
    | Result.contradiction => do 
      logInfo s!"{ident} test succeeded in finding a contradiction"
      trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
      printProof state
      applyProof state
    | Result.saturated =>
      logInfo s!"{ident} test resulted in prover saturation"
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      trace[Saturate.debug] "Final set of all clauses: {Array.map (fun x => x.1) state.allClauses.toArray}"
      Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

syntax (name := duper_no_timing) "duper_no_timing" : tactic

@[tactic duper_no_timing]
def evalDuperNoTiming : Tactic
| `(tactic| duper_no_timing) => withMainContext do
  Elab.Tactic.evalTactic
    (← `(tactic| intros; apply Classical.byContradiction _; intro))
  withMainContext do
    let formulas ← collectAssumptions #[]
    trace[Meta.debug] "Formulas from collectAssumptions: {formulas}"
    let symbolPrecMap ← buildSymbolPrecMap (formulas.map (fun (formula, _) => formula))
    let (_, state) ←
      ProverM.runWithExprs (s := {symbolPrecMap := symbolPrecMap, lctx := ← getLCtx, mctx := ← getMCtx}) ProverM.saturate formulas
    match state.result with
    | Result.contradiction => do
        logInfo s!"Contradiction found"
        trace[TPTP_Testing] "Final Active Set: {state.activeSet.toArray}"
        printProof state
        applyProof state
        logInfo s!"Constructed proof"
    | Result.saturated =>
      trace[Saturate.debug] "Final Active Set: {state.activeSet.toArray}"
      trace[Saturate.debug] "Final set of all clauses: {Array.map (fun x => x.1) state.allClauses.toArray}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic

