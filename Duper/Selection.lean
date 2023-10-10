import Duper.MClause
import Duper.RuleM
import Duper.Util.Misc

namespace Duper
open RuleM
open Lean

-- Sel function 0
def isSelectableLit0 (c : MClause) (i : Nat) :=
  c.lits[i]!.sign == false || c.lits[i]!.rhs == mkConst ``False || c.lits[i]!.lhs == mkConst ``False

-- Sel function 1
def isSelectableLit1 (c : MClause) (i : Nat) :=
  c.lits[i]!.sign == false

-- Sel function 2
def isSelectableLit2 (c : MClause) (i : Nat) := false

-- Selection function that always just selects the first selectable literal
def getSelections (c : MClause) : CoreM (List Nat) := do
  -- simply select first selectable literal:
  let selFunction ←
    match ← getSelFunctionM with
    | 0 => pure isSelectableLit0
    | 1 => pure isSelectableLit1
    | 2 => pure isSelectableLit2
    | _ => throwError "Invalid selFunction option"
  for i in [:c.lits.size] do
    if selFunction c i then
      return [i]
  return []

-- Selection function that never actually selects anything
-- def getSelections (_ : MClause) : List Nat := []

def litSelectedOrNothingSelected (c : MClause) (i : Nat) : CoreM Bool := do
  let sel ← getSelections c
  if sel == []
  then return true
  else return sel.contains i

def litSelected (c : MClause) (i : Nat) : CoreM Bool := do
  let sel ← getSelections c
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
  match ← getSelections c with
  | [] => c.isMaximalLit (← getOrder) alreadyReduced i strict
  | sel => do
    let isSelectableLit ←
      match ← getSelFunctionM with
      | 0 => pure isSelectableLit0
      | 1 => pure isSelectableLit1
      | 2 => pure isSelectableLit2
      | _ => throwError "Invalid selFunction option"
    let isSelected := sel.contains i
    if isSelected ∧ ¬ isSelectableLit c i then
      throwError "Literal {i} in clause {c.lits} may not be selected"
    return isSelected

/-- Checks whether a literal might be eligible before attempting to run the unification algorithm.

    A literal L is (strictly) eligible w.r.t. a substitution σ in C if it is selected in C or there are no selected literals
    in C and Lσ is (strictly) maximal in Cσ.

    The alreadyReduced variable indicates whether c has been betaEta reduced as well as whether its mvars have been instantiated
    (alreadyReduced is only set to true if both of these things are true) -/
def eligibilityPreUnificationCheck (c : MClause) (alreadyReduced := true) (i : Nat) : RuleM Eligibility := do
  let sel ← getSelections c
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