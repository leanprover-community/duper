import Duper.Simp

namespace Duper
open RuleM
open SimpResult

-- TODO: Do this on Clause instead of MClause?
-- This implements the rule syntactic tautology deletion 1 (TD1)
def syntacticTautologyDeletion1 : MSimpRule := fun c => do
  for lit in c.lits do
    if lit.sign ∧ lit.lhs == lit.rhs then
      return Removed
  return Unapplicable

end Duper