import Duper.Simp

namespace Duper
open Lean
open Std
open RuleM
open SimpResult

/-- Syntactic tautology deletion 3 doesn't refer to a specific rule in the literature, but is a response to the observation that
    duper often gets cluttered with clauses of the form "x = True ∨ x = False". Neither syntacticTautologyDeletion1 nor
    syntacticTautologyDeletion2 remove clauses of this form, so that is what syntacticTautologyDeletion3 targets. -/
def syntacticTautologyDeletion3 : MSimpRule := fun c => do
  let mut eqTrueSet : Std.HashSet Lean.Expr := Std.HashSet.emptyWithCapacity -- Stores Lean expressions equated to True in c
  let mut eqFalseSet : Std.HashSet Lean.Expr := Std.HashSet.emptyWithCapacity -- Stores Lean expressions equated to False in c
  for lit in c.lits do
    if lit.sign then
      if lit.rhs == mkConst ``True then
        if eqFalseSet.contains lit.lhs then return some #[]
        else eqTrueSet := eqTrueSet.insert lit.lhs
      else if lit.rhs == mkConst ``False then
        if eqTrueSet.contains lit.lhs then return some #[]
        else eqFalseSet := eqFalseSet.insert lit.lhs
      else if lit.lhs == mkConst ``True then
        if eqFalseSet.contains lit.rhs then return some #[]
        else eqTrueSet := eqTrueSet.insert lit.rhs
      else if lit.lhs == mkConst ``False then
        if eqTrueSet.contains lit.rhs then return some #[]
        else eqFalseSet := eqFalseSet.insert lit.rhs
    else -- We can view "x ≠ True" as the same as "x = False"
      if lit.rhs == mkConst ``True then
        if eqTrueSet.contains lit.lhs then return some #[]
        else eqFalseSet := eqFalseSet.insert lit.lhs
      else if lit.rhs == mkConst ``False then
        if eqFalseSet.contains lit.lhs then return some #[]
        else eqTrueSet := eqTrueSet.insert lit.lhs
      else if lit.lhs == mkConst ``True then
        if eqTrueSet.contains lit.rhs then return some #[]
        else eqFalseSet := eqFalseSet.insert lit.rhs
      else if lit.lhs == mkConst ``False then
        if eqFalseSet.contains lit.rhs then return some #[]
        else eqTrueSet := eqTrueSet.insert lit.rhs
  return none

end Duper
