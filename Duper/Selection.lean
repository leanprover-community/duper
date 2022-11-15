import Duper.MClause
import Duper.RuleM
import Duper.Util.Misc

namespace Duper
open RuleM
open Lean

def isSelectableLit (c : MClause) (i : Nat) :=
  c.lits[i]!.sign == false || c.lits[i]!.rhs == mkConst ``False || c.lits[i]!.lhs == mkConst ``False

-- Selection function that always just selects the first negative literal
def getSelections (c : MClause) : List Nat := Id.run do
  -- simply select first negative literal:
  for i in [:c.lits.size] do
    if isSelectableLit c i then
      return [i]
  return []

-- Selection function that never actually selects anything
-- def getSelections (_ : MClause) : List Nat := []

def litSelectedOrNothingSelected (c : MClause) (i : Nat) :=
  let sel := getSelections c
  if sel == []
  then true
  else sel.contains i

def litSelected (c : MClause) (i : Nat) :=
  let sel := getSelections c
  sel.contains i

/--
A literal L is (strictly) eligible w.r.t. a substitution σ
in C if it is selected in C or there are no selected literals
in C and Lσ is (strictly) maximal in Cσ. -/
def eligible (c : MClause) (i : Nat) (strict := false) : RuleM Bool := do
  match getSelections c with
  | [] => runMetaAsRuleM $ c.isMaximalLit (← getOrder) i strict
  | sel => do
    let selected := sel.contains i
    if selected ∧ ¬ isSelectableLit c i then
      throwError "Literal {i} in clause {c.lits} may not be selected"
    return selected

end Duper