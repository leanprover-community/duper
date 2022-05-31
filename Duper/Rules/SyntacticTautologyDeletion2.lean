import Duper.Simp

namespace Duper
open Std
open RuleM
open SimpResult

-- This implements the rule syntactic tautology deletion 2 (TD2)
def syntacticTautologyDeletion2 : MSimpRule := fun c => do
  --trace[Simp.debug] "Calling syntacticTautologyDeletion2 on clause {c.lits}"
  let mut eq_pairs : HashSet (Lean.Expr × Lean.Expr) := mkHashSet; -- A HashSet that stores pairs of Lean expressions that are equated in the clause
  let mut ne_pairs : HashSet (Lean.Expr × Lean.Expr) := mkHashSet; -- A HashSet that stores pairs of Lean expressions that are stated to not be equal in the clause
  for lit in c.lits do
    let lhs := lit.lhs
    let rhs := lit.rhs
    if lit.sign then {
      if(ne_pairs.contains (lhs, rhs) || ne_pairs.contains (rhs, lhs)) then
        trace[Simp.debug] "syntacticTautologyDeletion2 returning Removed due to literals {lhs} and {rhs} from the clause {c.lits}"
        return Removed -- The literal lhs = rhs and the literal lhs ≠ rhs are both in the clause, so the clause can be removed
      else
        eq_pairs := eq_pairs.insert (lhs, rhs)
    }
    else {
      if(eq_pairs.contains (lhs, rhs) || eq_pairs.contains (rhs, lhs)) then
        trace[Simp.debug] "syntacticTautologyDeletion2 returning Removed due to literals {lhs} and {rhs} from the clause {c.lits}"
        return Removed -- The literal lhs ≠ rhs and the literal lhs = rhs are both in the clause, so the clause can be removed
      else
        ne_pairs := ne_pairs.insert (lhs, rhs)
    }
  return Unapplicable

end Duper