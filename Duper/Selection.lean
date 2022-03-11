import Duper.MClause

namespace Duper
open Lean

-- TODO: Add simplification to always put True/False on right-hand side?
def getSelections (c : MClause) : List Nat := Id.run do
  -- simply select first negative literal:
  for i in [:c.lits.size] do
    if c.lits[i].sign == false ∨ c.lits[i].rhs == mkConst ``False then
      return [i]
  return []

def litSelectedOrNothingSelected (c : MClause) (i : Nat) :=
  let sel := getSelections c
  if sel == []
  then true
  else sel.contains i

end Duper