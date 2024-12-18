import Duper.MClause
import Duper.RuleM
import Duper.Util.Misc

namespace Duper
open RuleM
open Lean

/- Reference for E selection functions was found at https://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD/V_2.5/eprover.pdf
   Reference for Zipperposition selection functions was found at https://github.com/sneeuwballen/zipperposition/blob/wip-2.2/src/prover/selection.ml
   and https://github.com/sneeuwballen/zipperposition/blob/master/src/prover/selection.mli -/

/-- Determines whether given lit `l` is negative. If inclusive is true, then this includies literals of the form `e = False` and
    `False = e`. If inclusive is false, then this only includes literals whose sign is negative. -/
def isNegative (l : Lit) (inclusive := true) := !l.sign || (inclusive && (l.rhs == mkConst ``False || l.lhs == mkConst ``False))

/-- Selection function that returns the first negative literal (including lits of the form `e = False`) -/
def selectFirstNegLit (c : MClause) : CoreM (List Nat) := do
  for i in [:c.lits.size] do
    if isNegative c.lits[i]! then
      return [i]
  return []

/-- Selection function that returns the first negative literal (excluding lits of the form `e = False`) -/
def selectFirstNegLitExclusive (c : MClause) : CoreM (List Nat) := do
  for i in [:c.lits.size] do
    if isNegative c.lits[i]! false then
      return [i]
  return []

def isPureVarLit (l : Lit) : Bool :=
  match l.lhs, l.rhs with
  | Expr.mvar .., Expr.mvar .. => true
  | _, _ => false

/-- Based on E's SelectPureVarNegLiterals: Select the first negative literal of the form `x ≠ y` -/
def selectFirstPureVarNegLit (c : MClause) : CoreM (List Nat) := do
  for i in [:c.lits.size] do
    if isNegative c.lits[i]! && isPureVarLit c.lits[i]! then
      return [i]
  return []

/-- Based on E's SelectLargestNegLit: Select the first maximal negative literal

    Note: This coincides with Zipperposition's max_goal selection function (with strict set to true)
    which is Zipperposition's default selection function (outside of portfolio mode) -/
def selectFirstMaximalNegLit (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let maxLits ← c.getMaximalLits (← getOrder) alreadyReduced isNegative
  if maxLits.isEmpty then return []
  else return [maxLits[0]!]

/-- Based on Zipperposition's max_goal selection function with strict set to false:
    Select the first maximal negative literal and all positive literals -/
def selectFirstMaximalNegLitAndAllPosLits (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let maxLits ← c.getMaximalLits (← getOrder) alreadyReduced isNegative
  let mut posLits : List Nat := []
  for i in [:c.lits.size] do
    if !(isNegative c.lits[i]!) then
      posLits := i :: posLits
  if maxLits.isEmpty then return posLits
  else return maxLits[0]! :: posLits

/-- Based on E's SelectSmallestNegLit: Select the first minimal negative literal -/
def selectFirstMinimalNegLit (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let minLits ← c.getMinimalLits (← getOrder) alreadyReduced isNegative
  if minLits.isEmpty then return []
  else return [minLits[0]!]

/-- Based on E's SelectDiffNegLit: Select the first negative literal for which the size
    difference between both terms is maximal -/
def selectFirstMaxDiffNegLit (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let filter_fn : Lit → Nat → Bool := fun l _ => isNegative l
  let maxDiffLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn
  if maxDiffLits.isEmpty then return []
  else return [maxDiffLits[0]!]

def isGround (l : Lit) : Bool := !l.lhs.hasExprMVar && !l.rhs.hasExprMVar

/-- Based on E's SelectGroundNegLit: Select the first negative ground literal for which the size
    difference between both terms is maximal -/
def selectFirstGroundNegLit (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let filter_fn : Lit → Nat → Bool := fun l _ => isNegative l && isGround l
  let maxDiffLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn
  if maxDiffLits.isEmpty then return []
  else return [maxDiffLits[0]!]

/-- Based on E's SelectOptimalLit: If there is a negative ground literal, select as in selectFirstGroundNegLit.
    Otherwise, select as in selectFirstMaxDiffNegLit -/
def selectFirstGroundNegLitIfPossible (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let filter_fn1 : Lit → Nat → Bool := fun l _ => isNegative l && isGround l
  let filter_fn2 : Lit → Nat → Bool := fun l _ => isNegative l
  if c.lits.any (fun l => filter_fn1 l 0) then -- Can use 0 as index for each lit because filter_fn1 doesn't actually care about the index
    let maxDiffLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn1
    if maxDiffLits.isEmpty then return []
    else return [maxDiffLits[0]!]
  else
    let maxDiffLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn2
    if maxDiffLits.isEmpty then return []
    else return [maxDiffLits[0]!]

/-- Based on E's SelectMaxLComplex: Select a maximal negative literal. If there are no maximal negative
    literals, select nothing. If there is just one maximal negative literal, select that. If there are
    multiple maximal negative literals, try to find one that satisfies any of the following properties
    (listed in order of precedence):
    - Is a pure variable literal (i.e. of the form `x ≠ y`)
    - Is a ground literal with the largest size difference
    - Is a non-ground literal with the largest size difference -/
def selectMaxLitComplex (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let maxLitIndices ← c.getMaximalLits (← getOrder) alreadyReduced isNegative
  if maxLitIndices.isEmpty then return []
  else if maxLitIndices.size = 1 then return [maxLitIndices[0]!]
  else
    let maxLits := maxLitIndices.map (fun idx => (idx, c.lits[idx]!))
    let pureVarMaxLits := maxLits.filter (fun (_, l) => isPureVarLit l)
    if pureVarMaxLits.size > 0 then -- Select a maximal negative pure variable literal
      return [pureVarMaxLits[0]!.1]
    else
      let groundMaxLits := maxLits.filter (fun (_, l) => isGround l)
      if groundMaxLits.size > 0 then -- Select a maximal negative ground literal with maximal size difference
        -- filter_fn2 filters so that we only choose among maximal negative literals that are also ground
        let filter_fn2 : Lit → Nat → Bool := fun l idx => maxLitIndices.contains idx && isGround l
        let maxDiffGroundLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn2
        return [maxDiffGroundLits[0]!] -- maxDiffGroundLits.size must be greater than 0 since groundMaxLits.size is greater than 0
      else
        -- filter_fn3 filters so that we only choose among maximal negative literals
        let filter_fn3 : Lit → Nat → Bool := fun _ idx => maxLitIndices.contains idx
        let maxDiffLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn3
        return [maxDiffLits[0]!] -- maxDiffLits.size must be greater than 0 since maxLits.size > 0

/-- Based on E's SelectMaxLComplexAvoidPosPred (which coincides with Zipperposition's e_sel): It does the same as
    selectMaxLitComplex but uses the number of positive literals with a shared predicate symbol as a tiebreaker (preferring
    to select literals that share a predicate symbol with as few positive literals as possible). For this, specification, I
    am defining a predicate symbol as the top symbol for the lhs of a literal of the form `e = True` or `e = False`.

    Note: According to "Extending a Brainiac Prover to Lambda-Free Higher-Order Logic", SelectMaxLComplexAvoidPosPred
    (aka SelectMLCAPP) should be have very similarly to E's SelectMLCAPPPreferAppVar and SelectMLCAPPAvoidAppVar. So
    it should be unnecessary to separately implement those two selection functions. -/
def selectMaxLitComplexAvoidPosPred (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let maxLitIndices ← c.getMaximalLits (← getOrder) alreadyReduced isNegative
  if maxLitIndices.isEmpty then return []
  else if maxLitIndices.size = 1 then return [maxLitIndices[0]!]
  else
    let maxLits := maxLitIndices.map (fun idx => (idx, c.lits[idx]!))
    let pureVarMaxLits := maxLits.filter (fun (_, l) => isPureVarLit l)
    if pureVarMaxLits.size > 0 then -- Select a maximal negative pure variable literal
      return [pureVarMaxLits[0]!.1] -- If the lit is a pure variable literal, then it necessarily does not have predicate symbols
    else
      let groundMaxLits := maxLits.filter (fun (_, l) => isGround l)
      if groundMaxLits.size > 0 then -- Select a maximal negative ground literal with maximal size difference
        -- filter_fn2 filters so that we only choose among maximal negative literals that are also ground
        let filter_fn2 : Lit → Nat → Bool := fun l idx => maxLitIndices.contains idx && isGround l
        let maxDiffGroundLitIndices ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn2
        if maxDiffGroundLitIndices.isEmpty then
          -- maxDiffGroundLitIndices.size must be greater than 0 since groundMaxLits.size is greater than 0
          throwError "Error in selectMaxLitComplexAvoidPosPred"
        else if maxDiffGroundLitIndices.size = 1 then
          return [maxDiffGroundLitIndices[0]!]
        else -- Use the property of not sharing predicate symbols with positive literals as a tiebreaker
          let posLitsWithPredSymbols := c.lits.filter (fun l => l.sign && l.rhs == mkConst ``True)
          let predSymbols := posLitsWithPredSymbols.map (fun l => l.lhs.getTopSymbol)
          let maxDiffGroundLits := maxDiffGroundLitIndices.map (fun idx => (idx, c.lits[idx]!))
          let maxDiffGroundLitIndicesWithPredCount := maxDiffGroundLits.map
            (fun (idx, l) =>
              let lPredSymbol := l.lhs.getTopSymbol
              let numMatchingPredSymbols := (predSymbols.filter (fun p => p == lPredSymbol)).size
              (idx, numMatchingPredSymbols)
            )
          let maxDiffGroundLitIndicesWithPredCountSorted :=
            maxDiffGroundLitIndicesWithPredCount.qsort
              (fun (idx1, numMatchingPredSymbols1) (idx2, numMatchingPredSymbols2) =>
                numMatchingPredSymbols1 < numMatchingPredSymbols2 || (numMatchingPredSymbols1 == numMatchingPredSymbols2 && idx1 < idx2)
              )
          -- maxDiffGroundLitIndicesWithPredCountSorted.size must be greater than 0 since maxDiffGroundLitIndices.size is greater than 0
          return [maxDiffGroundLitIndicesWithPredCountSorted[0]!.1]
      else
        -- filter_fn3 filters so that we only choose among maximal negative literals
        let filter_fn3 : Lit → Nat → Bool := fun _ idx => maxLitIndices.contains idx
        let maxDiffLitIndices ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn3
        if maxDiffLitIndices.isEmpty then
          -- maxDiffLits.size must be greater than 0 since maxLitIndices.size is greater than 0
          throwError "Error in selectMaxLitComplexAvoidPosPred"
        else if maxDiffLitIndices.size = 1 then
          return [maxDiffLitIndices[0]!]
        else -- Use the property of not sharing predicate symbols with positive literals as a tiebreaker
          let posLitsWithPredSymbols := c.lits.filter (fun l => l.sign && l.rhs == mkConst ``True)
          let predSymbols := posLitsWithPredSymbols.map (fun l => l.lhs.getTopSymbol)
          let maxDiffLits := maxDiffLitIndices.map (fun idx => (idx, c.lits[idx]!))
          let maxDiffLitIndicesWithPredCount := maxDiffLits.map
            (fun (idx, l) =>
              let lPredSymbol := l.lhs.getTopSymbol
              let numMatchingPredSymbols := (predSymbols.filter (fun p => p == lPredSymbol)).size
              (idx, numMatchingPredSymbols)
            )
          let maxDiffLitIndicesWithPredCountSorted :=
            maxDiffLitIndicesWithPredCount.qsort
              (fun (idx1, numMatchingPredSymbols1) (idx2, numMatchingPredSymbols2) =>
                numMatchingPredSymbols1 < numMatchingPredSymbols2 || (numMatchingPredSymbols1 == numMatchingPredSymbols2 && idx1 < idx2)
              )
          -- maxDiffLitIndicesWithPredCountSorted.size must be greater than 0 since maxDiffLitIndices.size is greater than 0
          return [maxDiffLitIndicesWithPredCountSorted[0]!.1]

/-- Based on E's SelectCQIPrecWNTNp (which coincides with Zipperposition's e_sel2): Selects the negative literal with the
    highest-precedence predicate (as in selectMaxLitComplexAvoidPosPred, I define predicates as the top symbol for the lhs of a
    literal of the form `e = True` or `e = False`). If there are multiple negative literals with the same largest predicate, then
    the size difference between the lit's lhs and rhs will be the tiebreaker (with larger size differences being preferred). -/
def selectCQIPrecWNTNp (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let idxLitPairs := c.lits.mapIdx (fun idx l => (idx, l))
  let idxPredPairs := idxLitPairs.filterMap
    (fun (idx, l) =>
      -- Since we only select negative literals, and since we need a predicate, the only form we allow `l` to have is `e = False`
      if l.rhs == mkConst ``False then
        match l.lhs.getTopSymbol with
        | Expr.fvar fVarId => some (idx, some (Symbol.FVarId fVarId))
        | Expr.const name _ => some (idx, some (Symbol.Const name))
        | _ => some (idx, none)
      else none
    )
  let symbolPrecMap ← getSymbolPrecMap -- Recall that low values in symbolPrecMap correspond to high precedence
  let idxPredPairsSorted := idxPredPairs.qsort -- Sorting so that highest precedence symbols will be first in idxPredPairsSorted
    (fun (_idx1, pred1Opt) (_idx2, pred2Opt) =>
      match pred1Opt, pred2Opt with
      | some pred1, some pred2 =>
        match symbolPrecMap.get? pred1, symbolPrecMap.get? pred2 with
        | none, _ => false -- Never sort symbol not found in symbolPrecMap before anything else
        | some _, none => true -- Symbols found in symbolPrecMap are sorted before symbols found in symbolPrecMap
        | some prec1, some prec2 => prec1 < prec2 -- Low values in symbolPrecMap correspond to higher precedence
      | none, _ => false -- Never sort a head that isn't even a symbol (fvar or const) before anything else
      | some _, none => true -- Symbols (regardless of whether they are found in symbolPrecMap) are sorted before non-symbol heads
    )
  if idxPredPairsSorted.isEmpty then return [] -- There are no literals of the form `e = False`
  else if idxPredPairsSorted.size = 1 then return [idxPredPairsSorted[0]!.1]
  else
    -- Check if there are multiple negative literals with the same largest predicate
    let largestPred := idxPredPairsSorted[0]!.2
    let idxPredPairsWithLargestPred := idxPredPairsSorted.filter (fun (_, pred) => largestPred == pred)
    if idxPredPairsWithLargestPred.isEmpty then
      throwError "Error in selectCQIPrecWNTNp" -- Not possible since at least idxPredPairsSorted[0]! is in idxPredPairsWithLargestPred
    else if idxPredPairsWithLargestPred.size = 1 then
      return [idxPredPairsWithLargestPred[0]!.1]
    else -- There are multiple literals with the same largest predicate. Use the size difference between the lit lhs and rhs as the tiebreaker
      -- filter_fn only passes negative lits that have the largest predicate symbol
      let filter_fn : Lit → Nat → Bool := fun _ idx => idxPredPairsWithLargestPred.any (fun (n, _) => n == idx)
      let maxDiffLargestPredLits ← c.getMaxDiffLits (← getGetNetWeight) alreadyReduced filter_fn
      if maxDiffLargestPredLits.isEmpty then
        throwError "Error in selectCQIPrecWNTNp" -- Not possible since idxPredPairsWithLargestPred.size > 0
      else
        return [maxDiffLargestPredLits[0]!]

/-- Based on E's SelectComplexG (which coincides with Zipperposition's e_sel3): Attempts to select a negative pure variable literal
    (if there are multiple, selects the first arbitrarily). If that fails and there is at least one negative ground literal, selects the
    smallest negative ground literal. If that also fails, it selects the negative literal with the largest size difference. -/
def selectComplexG (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let firstPureVarNegLitSelection ← selectFirstPureVarNegLit c
  if firstPureVarNegLitSelection != [] then return firstPureVarNegLitSelection
  else
    let isNegAndGround : Lit → Bool := fun l => isNegative l && isGround l
    let negGroundLits ← c.getMinimalLits (← getOrder) alreadyReduced isNegAndGround
    if negGroundLits.size > 0 then return [negGroundLits[0]!]
    else selectFirstMaxDiffNegLit c alreadyReduced

def getSelections (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  match ← getSelFunctionM with
  | 0 => selectFirstNegLit c
  | 1 => selectFirstNegLitExclusive c
  | 2 => return [] -- NoSelection
  | 3 => selectFirstPureVarNegLit c
  | 4 => selectFirstMaximalNegLit c alreadyReduced -- This corresponds to Zipperposition's default selection function
  | 5 => selectFirstMaximalNegLitAndAllPosLits c alreadyReduced
  | 6 => selectFirstMinimalNegLit c alreadyReduced
  | 7 => selectFirstMaxDiffNegLit c alreadyReduced
  | 8 => selectFirstGroundNegLit c alreadyReduced
  | 9 => selectFirstGroundNegLitIfPossible c alreadyReduced
  | 10 => selectMaxLitComplex c alreadyReduced
  | 11 => selectMaxLitComplexAvoidPosPred c alreadyReduced -- This corresponds to Zipperposition's e_sel
  | 12 => selectCQIPrecWNTNp c alreadyReduced -- This corresponds to Zipperposition's e_sel2
  | 13 => selectComplexG c alreadyReduced -- This corresponds to Zipperposition's e_sel3
  | _ => throwError "Invalid selFunction option"

def litSelectedOrNothingSelected (c : MClause) (i : Nat) (alreadyReduced : Bool) : RuleM Bool := do
  let sel ← getSelections c alreadyReduced
  if sel == []
  then return true
  else return sel.contains i

def litSelected (c : MClause) (i : Nat) (alreadyReduced : Bool) : RuleM Bool := do
  let sel ← getSelections c alreadyReduced
  return sel.contains i

/-- Data type to capture whether a literal in a clause is eligible.
If it is not eligible, we distinguish the cases where there might
be substitutions that make the literal eligble (`potentiallyEligible`)
or not (`notEligible`).-/
inductive Eligibility
  | eligible
  | potentiallyEligible
  | notEligible
deriving Inhabited, BEq, Repr, Hashable

def Eligibility.format : Eligibility → MessageData
  | eligible => m!"eligibile"
  | notEligible => m!"notEligibile"
  | potentiallyEligible => m!"potentiallyEligibile"

instance : ToMessageData (Eligibility) := ⟨Eligibility.format⟩

/-- Checks whether a literal is eligible in rules without unification.

A literal L is (strictly) eligible in C if it is selected in C or there are no selected literals
in C and L is (strictly) maximal in C. -/
def eligibilityNoUnificationCheck (c : MClause) (alreadyReduced := true) (i : Nat) (strict := false) : RuleM Bool := do
  match ← getSelections c alreadyReduced with
  | [] => c.isMaximalLit (← getOrder) alreadyReduced i strict
  | sel => return sel.contains i

/-- Checks whether a literal might be eligible before attempting to run the unification algorithm.

    A literal L is (strictly) eligible w.r.t. a substitution σ in C if it is selected in C or there are no selected literals
    in C and Lσ is (strictly) maximal in Cσ.

    The alreadyReduced variable indicates whether c has been betaEta reduced as well as whether its mvars have been instantiated
    (alreadyReduced is only set to true if both of these things are true) -/
def eligibilityPreUnificationCheck (c : MClause) (alreadyReduced := true) (i : Nat) : RuleM Eligibility := do
  let sel ← getSelections c alreadyReduced
  if (sel.contains i) then
    return Eligibility.eligible -- literal is eligible and the post unification check is not necessary
  else if (sel == []) then do
    if (← c.canNeverBeMaximal (← getOrder) alreadyReduced i) then
      return Eligibility.notEligible
    else
      return Eligibility.potentiallyEligible -- literal may be eligible but the post unification check is needed to confirm maximality
  else
    return Eligibility.notEligible

/-- Checks whether a literal might be eligible based on the result of `eligibilityPreUnificationCheck`.

    A literal L is (strictly) eligible w.r.t. a substitution σ in C if it is selected in C or there are no selected literals
    in C and Lσ is (strictly) maximal in Cσ.

    The alreadyReduced variable indicates whether c has been betaEta reduced as well as whether its mvars have been instantiated
    (alreadyReduced is only set to true if both of these things are true) -/
def eligibilityPostUnificationCheck (c : MClause) (alreadyReduced := false) (i : Nat) (preUnificationResult : Eligibility) (strict := false) : RuleM Bool := do
  if preUnificationResult == Eligibility.eligible then return true
  else if preUnificationResult == Eligibility.notEligible then return false
  else c.isMaximalLit (← getOrder) alreadyReduced i (strict := strict)

end Duper
