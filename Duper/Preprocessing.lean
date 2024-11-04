import Lean
import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Simp
import Duper.Rules.Clausification

namespace Duper
namespace ProverM
open Lean
open Meta
open ProverM
open RuleM
open SimpResult

initialize
  registerTraceClass `duper.unaryFirst.debug
  registerTraceClass `duper.collectDatatypes.debug

/-- Naively applies clausificationStep.toSimpRule to everything in the passive set (and everything produced by
    clausifying clauses in the passive set) without removing anything from the passive set. This preprocessing
    clausification is not necessary (and might be removed later if it turns out to use more time than it saves),
    but it may be useful to make the KBO precedence and weight generation heuristics more accurate (e.g. preprocessing
    clausification will ensure that ¬ is not selected as the unary symbol with highest precedence) -/
partial def preprocessingClausification : ProverM Unit := do
  Core.withCurrHeartbeats do
    let mut clausified : Array Clause := #[] -- An array for storing the clauses that have been fully clausified
    try
      Core.checkMaxHeartbeats "preprocessingClausification"
      let mut moreToClausify := true
      while moreToClausify do
        match ← chooseGivenClause with
        | some givenClause =>
          let rec clausifyToFixedPoint (c : Clause) : ProverM (Option Clause) := do
            match ← clausificationStep.toSimpRule c with
            | Applied c' => clausifyToFixedPoint c'
            | Removed => return none
            | Unapplicable => return some c
          match ← clausifyToFixedPoint givenClause with
          | none => continue
          | some clausifiedGivenClause => clausified := clausified.push clausifiedGivenClause
        | none => moreToClausify := false
      -- Return everything in clausified back to the passive set
      trace[duper.preprocessing.debug] "Clausified after preprocessing: {clausified}"
      for c in clausified do
        addClausifiedToPassive c
    catch
    | e =>
      trace[duper.timeout.debug] "Timed out during preprocessingClausification"
      trace[duper.timeout.debug] "Passive set: {(← getPassiveSet).toArray}"
      trace[duper.timeout.debug] "Clausified: {clausified}"
      throw e

/-- Updates symbolFreqArityMap to increase the count of all symbols that appear in f (and if a symbol in f appears n
    times, then updates f's result in symbolFreqMap to be n greater than it was originally). Note that as with Expr.weight,
    this function may require revision to be more similar to Zipperposition's implementation once we actually start working
    on higher order things. -/
partial def updateSymbolFreqArityMap (f : Expr) (symbolFreqArityMap : Std.HashMap Symbol (Nat × Nat)) :
  ProverM (Std.HashMap Symbol (Nat × Nat)) := do
  match f with
  | Expr.fvar fVarId =>
    let fSymbol := Symbol.FVarId fVarId
    match symbolFreqArityMap.get? fSymbol with
    | some (fFreq, fArity) => return symbolFreqArityMap.insert fSymbol (fFreq + 1, fArity)
    | none =>
      match (← getLCtx).fvarIdToDecl.find? fVarId with
      | some fDecl =>
        let fType := LocalDecl.type fDecl
        return symbolFreqArityMap.insert fSymbol (1, getArity fType)
      | none => throwError s!"Unable to find {fVarId.name} in local context"
  | Expr.const name _ =>
    let fSymbol := Symbol.Const name
    match symbolFreqArityMap.get? fSymbol with
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

/-- Checks whether the type `t` is an inductive datatype that is neither a type class nor a Prop -/
def isInductiveAndNonPropAndNotTypeClass (t : Expr) : ProverM Bool := do
  let isInductiveDatatype ← matchConstInduct t.getAppFn' (fun _ => pure false) (fun _ _ => pure true)
  let isClass := Option.isSome $ ← isClass? t
  let isProp := (← inferType t).isProp
  return isInductiveDatatype && !isClass && !isProp

/-- Updates symbolFreqArityMap to increase the count of all symbols that appear in f (and if a symbol in f appears n
    times, then updates f's result in symbolFreqMap to be n greater than it was originally). Note that as with Expr.weight,
    this function may require revision to be more similar to Zipperposition's implementation once we actually start working
    on higher order things. Additionally, updates datatypeList to make sure that all inductive datatypes that appear
    in the problem are contained in the datatypeList. The format in which inductive datatypes are recorded as elements of
    type `Expr × Array Name` is described in the comment above `buildSymbolFreqArityMapAndDatatypeList` -/
partial def updateSymbolFreqArityMapAndDatatypeList (f : Expr) (symbolFreqArityMap : Std.HashMap Symbol (Nat × Nat))
  (datatypeList : List (Expr × Array Name)) (paramNames : Array Name) :
  ProverM (Std.HashMap Symbol (Nat × Nat) × List (Expr × Array Name)) := do
  match f with
  | Expr.fvar fVarId =>
    let fSymbol := Symbol.FVarId fVarId
    match symbolFreqArityMap.get? fSymbol with
    | some (fFreq, fArity) => return (symbolFreqArityMap.insert fSymbol (fFreq + 1, fArity), datatypeList)
    | none =>
      match (← getLCtx).fvarIdToDecl.find? fVarId with
      | some fDecl =>
        let fType := fDecl.type
        let fTypeIsInductive ← isInductiveAndNonPropAndNotTypeClass fType
        if fTypeIsInductive && !datatypeList.any (fun (t, _) => t == fType) then
          return (symbolFreqArityMap.insert fSymbol (1, getArity fType), (fType, paramNames) :: datatypeList)
        else
          return (symbolFreqArityMap.insert fSymbol (1, getArity fType), datatypeList)
      | none => throwError s!"Unable to find {fVarId.name} in local context"
  | Expr.const name _ =>
    let fSymbol := Symbol.Const name
    match symbolFreqArityMap.get? fSymbol with
    | some (fFreq, fArity) => -- fSymbol has already been seen so datatypeList does not need to be updated
      return (symbolFreqArityMap.insert fSymbol (fFreq + 1, fArity), datatypeList)
    | none =>
      let fType ← inferType f
      let fTypeIsInductive ← isInductiveAndNonPropAndNotTypeClass fType
      if fTypeIsInductive && !datatypeList.any (fun (t, _) => t == fType) then
        return (symbolFreqArityMap.insert fSymbol (1, getArity fType), (fType, paramNames) :: datatypeList)
      else
        return (symbolFreqArityMap.insert fSymbol (1, getArity fType), datatypeList)
  | Expr.app f1 f2 =>
    let fType ← inferType f
    let fTypeIsInductive ← isInductiveAndNonPropAndNotTypeClass fType
    let datatypeList :=
      if fTypeIsInductive && !datatypeList.any (fun (t, _) => t == fType) then (fType, paramNames) :: datatypeList
      else datatypeList
    let (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList f1 symbolFreqArityMap datatypeList paramNames
    updateSymbolFreqArityMapAndDatatypeList f2 symbolFreqArityMap datatypeList paramNames
  | Expr.lam _ t b _ =>
    let tIsInductive ← isInductiveAndNonPropAndNotTypeClass t
    let datatypeList :=
      if tIsInductive && !datatypeList.any (fun (t', _) => t' == t) then (t, paramNames) :: datatypeList
      else datatypeList
    let (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList t symbolFreqArityMap datatypeList paramNames
    -- Modify `b` to not contain loose bvars
    let freshMVar ← mkFreshExprMVar t
    let freshMVarId := freshMVar.mvarId!
    let b' := b.instantiate1 freshMVar
    let (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList b' symbolFreqArityMap datatypeList paramNames
    let mut datatypeArr := #[]
    -- Remove freshMVar from all acquired datatypes
    for (datatype, datatypeParams) in datatypeList do
      if datatype.hasAnyMVar (fun mvarid => mvarid == freshMVarId) then
        let datatype ← mkForallFVars #[freshMVar] datatype
        datatypeArr := datatypeArr.push (datatype, datatypeParams)
      else
        datatypeArr := datatypeArr.push (datatype, datatypeParams)
    pure (symbolFreqArityMap, datatypeArr.toList)
  | Expr.forallE _ t b _ =>
    let tIsInductive ← isInductiveAndNonPropAndNotTypeClass t
    let datatypeList :=
      if tIsInductive && !datatypeList.any (fun (t', _) => t' == t) then (t, paramNames) :: datatypeList
      else datatypeList
    let (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList t symbolFreqArityMap datatypeList paramNames
    -- Modify `b` to not contain loose bvars
    let freshMVar ← mkFreshExprMVar t
    let freshMVarId := freshMVar.mvarId!
    let b' := b.instantiate1 freshMVar
    let (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList b' symbolFreqArityMap datatypeList paramNames
    let mut datatypeArr := #[]
    -- Remove freshMVar from all acquired datatypes
    for (datatype, datatypeParams) in datatypeList do
      if datatype.hasAnyMVar (fun mvarid => mvarid == freshMVarId) then
        let datatype ← mkForallFVars #[freshMVar] datatype
        datatypeArr := datatypeArr.push (datatype, datatypeParams)
      else
        datatypeArr := datatypeArr.push (datatype, datatypeParams)
    pure (symbolFreqArityMap, datatypeArr.toList)
  | Expr.letE _ _ v b _ =>
    let (symbolFreqArityMap', datatypeList') ← updateSymbolFreqArityMapAndDatatypeList v symbolFreqArityMap datatypeList paramNames
    updateSymbolFreqArityMapAndDatatypeList b symbolFreqArityMap' datatypeList' paramNames
  | Expr.proj _ _ b =>
    let fType ← inferType f
    let fTypeIsInductive ← isInductiveAndNonPropAndNotTypeClass fType
    if fTypeIsInductive && !datatypeList.any (fun (t, _) => t == fType) then
      updateSymbolFreqArityMapAndDatatypeList b symbolFreqArityMap ((fType, paramNames) :: datatypeList) paramNames
    else
      updateSymbolFreqArityMapAndDatatypeList b symbolFreqArityMap datatypeList paramNames
  | Expr.mdata _ b => updateSymbolFreqArityMapAndDatatypeList b symbolFreqArityMap datatypeList paramNames
  | Expr.sort .. => return (symbolFreqArityMap, datatypeList)
  | Expr.mvar .. =>
    let fType ← inferType f
    let fTypeIsInductive ← isInductiveAndNonPropAndNotTypeClass fType
    if fTypeIsInductive && !datatypeList.any (fun (t, _) => t == fType) then
      return (symbolFreqArityMap, (fType, paramNames) :: datatypeList)
    else
      return (symbolFreqArityMap, datatypeList)
  | Expr.bvar .. => return (symbolFreqArityMap, datatypeList)
  | Expr.lit .. =>
    let fType ← inferType f
    let fTypeIsInductive ← isInductiveAndNonPropAndNotTypeClass fType
    if fTypeIsInductive && !datatypeList.any (fun (t, _) => t == fType) then
      return (symbolFreqArityMap, (fType, paramNames) :: datatypeList)
    else
      return (symbolFreqArityMap, datatypeList)

/-- Builds a HashMap that maps each symbol to a tuple containing:
    - The number of times they appear in formulas
    - Its arity -/
partial def buildSymbolFreqArityMap (clauses : List Clause) : ProverM (Std.HashMap Symbol (Nat × Nat)) := do
  let mut symbolFreqArityMap := Std.HashMap.empty
  for c in clauses do
    for l in c.lits do
      symbolFreqArityMap ← updateSymbolFreqArityMap l.lhs symbolFreqArityMap
      symbolFreqArityMap ← updateSymbolFreqArityMap l.rhs symbolFreqArityMap
  trace[duper.unaryFirst.debug] "symbolFreqArityMap: {symbolFreqArityMap.toArray}"
  return symbolFreqArityMap

/-- Builds:
    - A HashMap that maps each symbol to a tuple containing:
      - The number of times they appear in formulas
      - Its arity
    - A list containing every inductive datatype that appears in any clause. Polymorphic inductive datatypes are represented as universally
    quantified types paired with an array of parameters that can appear in the inductive datatype. For example, the polymorphic list datatype
    `List α` of where `α : Type u` is represented via `((∀ (α : Type u), List α), #[u])` -/
partial def buildSymbolFreqArityMapAndDatatypeList (clauses : List Clause) : ProverM (Std.HashMap Symbol (Nat × Nat) × List (Expr × Array Name)) := do
  let mut symbolFreqArityMap := Std.HashMap.empty
  let mut datatypeList := []
  for c in clauses do
    trace[duper.collectDatatypes.debug] "Loaded clause c: {c.lits}"
    for l in c.lits do
      (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList l.lhs symbolFreqArityMap datatypeList c.paramNames
      (symbolFreqArityMap, datatypeList) ← updateSymbolFreqArityMapAndDatatypeList l.rhs symbolFreqArityMap datatypeList c.paramNames
  trace[duper.unaryFirst.debug] "symbolFreqArityMap: {symbolFreqArityMap.toArray}"
  trace[duper.collectDatatypes.debug] "datatypeList collected by buildSymbolFreqArityMapAndDatatypeList: {datatypeList}"
  return (symbolFreqArityMap, datatypeList)

/-- Builds the symbolPrecMap from the input assumptions. Note that lower numbers in the symbol prec
    map correspond to higher precedences (so that symbol s is maximal iff s maps to 0).

    In addition to returning the symbolPrecMap itself, we also return a boolean that indicates whether
    the highest precedence symbol has arity zero (i.e. is a first-order constant). This is necessary
    because if it is, then the firstmaximal0 weight generation scheme cannot be used. -/
def buildSymbolPrecMap (clauses : List Clause) : ProverM (SymbolPrecMap × Bool) := do
  let symbolFreqArityMap ← buildSymbolFreqArityMap clauses
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
              let firstFVarIdInDecls :=
                lctx.decls.findSome?
                  (fun declOpt =>
                    match declOpt with
                    | some decl =>
                        if decl.fvarId == fVarId1 || decl.fvarId == fVarId2 then some decl.fvarId
                        else none
                    | none => none)
              match firstFVarIdInDecls with
              | some firstFVarId =>
                if firstFVarId == fVarId1 then true
                else false
              | none => false -- This case isn't possible because fVarId1 and fVarId2 must both appear in the local context
  for (s, sFreq, sArity) in symbolFreqArityMap.toArray do
    -- We use unaryFirstGt as the lt argument for binInsert so that symbols with higher precedence come first in symbolPrecArray
    symbolPrecArr := symbolPrecArr.binInsert unaryFirstGt (s, sFreq, sArity)
  trace[duper.unaryFirst.debug] "symbolPrecArr: {symbolPrecArr}"
  let mut symbolPrecMap := Std.HashMap.empty
  let mut counter := 0
  let mut highesetPrecSymbolHasArityZero := false
  for (s, _, sArity) in symbolPrecArr do
    if counter == 0 && sArity == 0 then highesetPrecSymbolHasArityZero := true
    symbolPrecMap := symbolPrecMap.insert s counter -- Map s to its index in symbolPrecArr
    counter := counter + 1
  trace[duper.unaryFirst.debug] "symbolPrecMap: {symbolPrecMap.toArray}"
  return (symbolPrecMap, highesetPrecSymbolHasArityZero)

/-- Like `buildSymbolPrecMap` but it also returns a list of all inductive datatypes that appear in any clause.
    Polymorphic inductive datatypes are represented as universally quantified types paired with an array of parameters
    that can appear in the inductive datatype. For example, the polymorphic list datatype `List α` of where `α : Type u`
    is represented via `((∀ (α : Type u), List α), #[u])` -/
def buildSymbolPrecMapAndDatatypeList (clauses : List Clause) : ProverM (SymbolPrecMap × Bool × List (Expr × Array Name)) := do
  let (symbolFreqArityMap, datatypeList) ← buildSymbolFreqArityMapAndDatatypeList clauses
  trace[duper.collectDatatypes.debug] "datatypeList collected by buildSymbolPrecMap: {datatypeList}"
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
              let firstFVarIdInDecls :=
                lctx.decls.findSome?
                  (fun declOpt =>
                    match declOpt with
                    | some decl =>
                        if decl.fvarId == fVarId1 || decl.fvarId == fVarId2 then some decl.fvarId
                        else none
                    | none => none)
              match firstFVarIdInDecls with
              | some firstFVarId =>
                if firstFVarId == fVarId1 then true
                else false
              | none => false -- This case isn't possible because fVarId1 and fVarId2 must both appear in the local context
  for (s, sFreq, sArity) in symbolFreqArityMap.toArray do
    -- We use unaryFirstGt as the lt argument for binInsert so that symbols with higher precedence come first in symbolPrecArray
    symbolPrecArr := symbolPrecArr.binInsert unaryFirstGt (s, sFreq, sArity)
  trace[duper.unaryFirst.debug] "symbolPrecArr: {symbolPrecArr}"
  let mut symbolPrecMap := Std.HashMap.empty
  let mut counter := 0
  let mut highesetPrecSymbolHasArityZero := false
  for (s, _, sArity) in symbolPrecArr do
    if counter == 0 && sArity == 0 then highesetPrecSymbolHasArityZero := true
    symbolPrecMap := symbolPrecMap.insert s counter -- Map s to its index in symbolPrecArr
    counter := counter + 1
  trace[duper.unaryFirst.debug] "symbolPrecMap: {symbolPrecMap.toArray}"
  return (symbolPrecMap, highesetPrecSymbolHasArityZero, datatypeList)
