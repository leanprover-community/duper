import Duper.MClause
import Duper.RuleM
import Duper.Util.Misc

namespace Duper
open RuleM
open Lean

/- Reference for E selection functions was found at https://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD/V_2.5/eprover.pdf
   Reference for Zipperposition selection functions was found at https://github.com/sneeuwballen/zipperposition/blob/wip-2.2/src/prover/selection.ml
   and https://github.com/sneeuwballen/zipperposition/blob/master/src/prover/selection.mli -/

/-- Selection function that returns the first negative literal (including lits of the form `e = False`) -/
def selectFirstNegLitInclusive (c : MClause) : CoreM (List Nat) := do
  let isSelectable : MClause → Nat → Bool := fun c i =>
    c.lits[i]!.sign == false || c.lits[i]!.rhs == mkConst ``False || c.lits[i]!.lhs == mkConst ``False
  for i in [:c.lits.size] do
    if isSelectable c i then
      return [i]
  return []

/-- Selection function that returns the first negative literal -/
def selectFirstNegLit (c : MClause) : CoreM (List Nat) := do
  let isSelectable : MClause → Nat → Bool := fun c i =>
    c.lits[i]!.sign == false
  for i in [:c.lits.size] do
    if isSelectable c i then
      return [i]
  return []

/-- Based on E's SelectPureVarNegLiterals: Select the first negative literal of the form x ≠ y -/
def selectFirstPureVarNegLit (c : MClause) : CoreM (List Nat) := do
  let isSelectable : MClause → Nat → Bool := fun c i =>
    match c.lits[i]!.sign, c.lits[i]!.lhs, c.lits[i]!.rhs with
    | false, Expr.mvar .., Expr.mvar .. => true
    | _, _, _ => false
  for i in [:c.lits.size] do
    if isSelectable c i then
      return [i]
  return []

/-- Based on E's SelectLargestNegLit: Select the first maximal negative literal

    Note: This coincides with Zipperposition's max_goal selection function (with strict set to true). -/
def selectFirstMaximalNegLit (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let filter_fn : Lit → Bool := fun l => !l.sign -- filter_fn l returns true iff l is negative
  let maxLits ← c.getMaximalLits (← getOrder) alreadyReduced filter_fn
  if maxLits.isEmpty then return []
  else return [maxLits[0]!]

/-- Based on Zipperposition's max_goal selection function with strict set to false:
    Select the first maximal negative literal and all positive literals -/
def selectFirstMaximalNegLitAndAllPosLits (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let filter_fn : Lit → Bool := fun l => !l.sign -- filter_fn l returns true iff l is negative
  let maxLits ← c.getMaximalLits (← getOrder) alreadyReduced filter_fn
  let mut posLits : List Nat := []
  for i in [:c.lits.size] do
    if c.lits[i]!.sign then
      posLits := i :: posLits
  if maxLits.isEmpty then return posLits
  else return maxLits[0]! :: posLits

/-- Based on E's SelectSmallestNegLit: Select the first minimal negative literal -/
def selectFirstMinimalNegLit (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  let filter_fn : Lit → Bool := fun l => !l.sign -- filter_fn l returns true iff l is negative
  let minLits ← c.getMinimalLits (← getOrder) alreadyReduced filter_fn
  if minLits.isEmpty then return []
  else return [minLits[0]!]

/-- Based on E's SelectDiffNegLit: Select the first negative literal for which the size
    difference between both terms is maximal -/
def selectFirstDiffNegLit (c : MClause) : RuleM (List Nat) := do
  sorry

/-- Based on E's SelectGroundNegLit: Select the first negative ground literal for which the size
    difference between both terms is maximal -/
def selectFirstGroundNegLit (c : MClause) : RuleM (List Nat) := do
  sorry

/-- Based on E's SelectOptimalLit: If there is a negative ground literal, select as in selectFirstGroundNegLit.
    Otherwise, select as in selectFirstDiffNegLit -/
def selectFirstGroundNegLitIfPossible (c : MClause) : RuleM (List Nat) := do
  sorry

def getSelections (c : MClause) (alreadyReduced : Bool) : RuleM (List Nat) := do
  match ← getSelFunctionM with
  | 0 => selectFirstNegLitInclusive c
  | 1 => selectFirstNegLit c
  | 2 => return [] -- NoSelection
  | 3 => selectFirstPureVarNegLit c
  | 4 => selectFirstMaximalNegLit c alreadyReduced
  | 5 => selectFirstMaximalNegLitAndAllPosLits c alreadyReduced
  | 6 => selectFirstMinimalNegLit c alreadyReduced
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