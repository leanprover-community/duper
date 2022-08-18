import Duper.MClause
import Duper.RuleM
import Duper.Util.Misc

namespace Duper
open RuleM
open Lean

def getSelections (c : MClause) : List Nat := Id.run do
  -- simply select first negative literal:
  for i in [:c.lits.size] do
    if c.lits[i]!.sign == false || c.lits[i]!.rhs == mkConst ``False || c.lits[i]!.lhs == mkConst ``False then
      return [i]
  return []

def litSelectedOrNothingSelected (c : MClause) (i : Nat) :=
  let sel := getSelections c
  if sel == []
  then true
  else sel.contains i

def litSelected (c : MClause) (i : Nat) :=
  let sel := getSelections c
  sel.contains i

/-- A literal l (with index i) from clause c is eligible for paramodulation if:
  1. l is a positive literal (l.sign = true)
  2. The set of selections for clasue c is empty
  3. l is maximal in c
-/
def eligibleForParamodulation (c : MClause) (i : Nat) : RuleM Bool := do
  let constraint1 := c.lits[i]!.sign
  let constraint2 := getSelections c == List.nil
  let constraint3 := ← runMetaAsRuleM $ c.isMaximalLit (← getOrder) i
  return constraint1 && constraint2 && constraint3

/-- A literal l (with index i) from clause c is eligible for resolution if either of the following hold:
  1. getSelections c yields the empty list and l is maximal in c by the ground reduction ordering
  2. getSelections c yields the nonempty list sel and either:
      - l is a positive literal and is a maximal positive literal in sel
      - l is a negative literal and is a maximal negative literal in sel
-/
def eligibleForResolution (c : MClause) (i : Nat) : RuleM Bool := do
  match getSelections c with
  | [] => runMetaAsRuleM $ c.isMaximalLit (← getOrder) i
  | sel =>
    if c.lits[i]!.sign then
      let sel_pos := List.filter (λ j => c.lits[j]!.sign) sel
      runMetaAsRuleM $ c.isMaximalInSubClause (← getOrder) sel_pos i
    else
      let sel_neg := List.filter (λ j => not c.lits[j]!.sign) sel
      runMetaAsRuleM $ c.isMaximalInSubClause (← getOrder) sel_neg i

end Duper