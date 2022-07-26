import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open SimpResult
open Lean

/-- Determines whether a literal has exactly the form `false = true` or `true = false`-/
def isFalseLiteral (lit : Lit) : Bool :=
  lit.sign &&
    ((exprIsTrue lit.lhs && exprIsFalse lit.rhs) ||
    (exprIsFalse lit.lhs && exprIsTrue lit.rhs))

/-- Eliminate literals that are exactly of the form `false = true`, `False = True`, `True = False` or `true = false`. 
    This is a special case of the falseElim inference rule in which σ is the identity -/
def identFalseElim : MSimpRule := fun c => do
  let mut newLits : Array Lit := #[]
  -- If c.lits[i] is `false = true` or `true = false`, then refs[i] = none
  -- If c.lits[i] isn't `false = true` or `true = false`,then refs[i] = some j where newLits[j] = c.lits[i]
  let mut refs : Array (Option Nat) := #[]
  for lit in c.lits do
    if (isFalseLiteral lit) then
      refs := refs.push none
    else
      refs := refs.push (some newLits.size)
      newLits := newLits.push lit
  if (newLits.size = c.lits.size) then
    return Unapplicable
  else
    return Applied [(MClause.mk newLits, none)]

end Duper