import Duper.MClause

namespace Duper

def getSelections (c : MClause) : List Nat := Id.run do
  -- simply select first negative literal:
  for i in [:c.lits.size] do
    if c.lits[i].sign == false then
      return [i]
  return []

def litSelectedOrNothingSelected (c : MClause) (i : Nat) :=
  let sel := getSelections c
  if sel == []
  then true
  else sel.contains i

end Duper