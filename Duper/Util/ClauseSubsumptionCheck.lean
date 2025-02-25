import Duper.RuleM

set_option linter.unusedVariables false

namespace Duper

open Lean
open Meta
open RuleM

/-- Determines whether there is any σ such that σ(l1.lhs) = l2.lhs and σ(l1.rhs) = l2.rhs. Returns true and applies σ if so,
    returns false (without applying any substitution) otherwise -/
def checkDirectMatch (l1 : Lit) (l2 : Lit) (protectedMVarIds : Array MVarId) : RuleM Bool :=
  performMatch #[(l2.lhs, l1.lhs), (l2.rhs, l1.rhs)] protectedMVarIds -- l2 is first argument in each pair so only l1's mvars can receive assignments

/-- Determines whether there is any σ such that σ(l1.rhs) = l2.lhs and σ(l1.lhs) = l2.rhs. Returns true and applies σ if so,
    returns false (without applying any substitution) otherwise -/
def checkCrossMatch (l1 : Lit) (l2 : Lit) (protectedMVarIds : Array MVarId) : RuleM Bool :=
  performMatch #[(l2.lhs, l1.rhs), (l2.rhs, l1.lhs)] protectedMVarIds -- l2 is first argument in each pair so only l1's mvars can receive assignments

/-- Determines whether σ(l1) = l2 for any substitution σ. Importantly, litsMatch can return true if l1.sign = l2.sign and either:
    - σ(l1.lhs) = l2.lhs and σ(l1.rhs) = l2.rhs
    - σ(l1.rhs) = l2.lhs and σ(l1.lhs) = l2.rhs
    In the former case, `litsMatch` returns `some false`, in the latter case, `litsMatch` returns `some true`, and if no match can be found, then it returns `none` -/
def litsMatch (l1 : Lit) (l2 : Lit) (protectedMVarIds : Array MVarId) : RuleM (Option Bool) := do
  if l1.sign != l2.sign then return none
  else if ← checkDirectMatch l1 l2 protectedMVarIds then return some false -- isFlipped is false
  else if ← checkCrossMatch l1 l2 protectedMVarIds then return some true -- isFlipped is true
  else return none

/-- Determines whether, for any substitution σ, σ(l) is in c at startIdx or after startIdx. If it is, then metavariables are assigned so that σ is
    applied and the index of σ(l) in c is returned (as well as whether a flip was necessary to perform the match). If there are multiple indices in c
    that l can match, then litInClause returns the first one. If there is no substitution σ such that σ(l) is in c at or after startIdx, the MetavarContext
    is left unchanged and none is returned.

    Additionally, litInClause is not allowed to return any Nat that is part of the exclude set. This is to prevent instances in which multiple
    literals in the subsumingClause all map onto the same literal in the subsumedClause. -/
def litInClause (l : Lit) (c : MClause) (cMVarIds : Array MVarId) (exclude : Std.HashSet Nat) (startIdx : Nat) : RuleM (Option (Nat × Bool)) := do
  for i in [startIdx:c.lits.size] do
    if exclude.contains i then
      continue
    else
      let cLit := c.lits[i]!
      match ← litsMatch l cLit cMVarIds with
      | some true => return some (i, true)
      | some false => return some (i, false)
      | none => continue
  return none

/-- Attempts to find an injective mapping f from subsumingClauseLits to subsumedClauseLits and a substitution σ such that
    for every literal l ∈ subsumingClauseLits, σ(l) = f(l). If subsumptionCheckHelper fails to find such a mapping and substitution,
    then subsumptionCheckHelper returns none without modifying the state's MetavarContext.

    If subsumptionCheckHelper succeeds, then it assigns MVars to apply σ and returns a list `assignment` such that:
    - `∀ i ∈ [0, subsumingClauseLits.length], σ(subsumingClauseLits.get! i) = subsumedClauseLits[(assignment.reverse.get! i).1]` if
      `(assignment.reverse.get! i).2` is false
    - `∀ i ∈ [0, subsumingClauseLits.length], σ(subsumingClauseLits.get! i) = subsumedClauseLits[(assignment.reverse.get! i).1]` with swapped lhs/rhs if
      `(assignment.reverse.get! i).2` is true
    - Note that `assignment` is reversed in the above lines. This is so that when we add additional nats to the assignment list, we can
      cons them onto the front of the list in constant time rather than concat them onto the back of the list in linear time

    The argument exclude contains a set of Nats that cannot be mapped to (so that injectivity is preserved). The argument fstStart is provided
    to facilitate backtracking. The argument assignment is used to build the final result described above, and the argument assignmentIsFlipped
    is used to indicate whether the match indicated by assignment needed to be flipped or not.

    subsumptionCheckHelper is defined as a partialDef, but should always terminate because every recursive call either makes subsumingClauseLits
    smaller or makes fstStart bigger (and once fstStart exceeds the size of subsumedClauseLits.lits, litInClause is certain to fail) -/
partial def subsumptionCheckHelper (subsumingClauseLits : List Lit) (subsumedClauseLits : MClause) (subsumedClauseMVarIds : Array MVarId)
  (exclude : Std.HashSet Nat) (assignment : List (Nat × Bool)) (fstStart := 0) : RuleM (Option (List (Nat × Bool))) := do
  match subsumingClauseLits with
  | List.nil => return some assignment
  | l :: restSubsumingClauseLits =>
    match ← litInClause l subsumedClauseLits subsumedClauseMVarIds exclude fstStart with
    | none => return none
    | some (idx, idxMatchIsFlipped) =>
      let tryWithIdx ←
        conditionallyModifyingMCtx do -- Only modify the MCtx if the recursive call succeeds
          let exclude := exclude.insert idx
          let assignment := (idx, idxMatchIsFlipped) :: assignment
          match ← subsumptionCheckHelper restSubsumingClauseLits subsumedClauseLits subsumedClauseMVarIds exclude assignment with
          | some assignment => return (true, some assignment)
          | none => return (false, none)
      /- tryWithIdx indicates whether it is possible to find an injective mapping from subsumingClauseLits to subsumedClauseLits that satisfies
         the constraints of subsumption where the first literal in subsumingClauseLits is mapped to the first possible literal in subsumingClauseLits
         after fstStart. If tryWithIdx succeeded, then we can simply return that success and have no need to backtrack. But if tryWithIdx failed,
         then matching l with the first lit possible after fstStart in subsumedClauseLits doesn't work. Therefore, we should simulate backtracking
         to that decision by recursing with fstStart one above idx -/
      match tryWithIdx with
      | some assignment => return assignment
      | none => subsumptionCheckHelper subsumingClauseLits subsumedClauseLits subsumedClauseMVarIds exclude assignment (idx + 1)

/-- Returns true if `subsumedClause` is indeed subsumed by `subsumingClause` and returns false otherwise. If the check succeeds (meaning
    true is returned) then any changes to the MCtx are preserved (meaning any mvar substitutions are applied) and if the check fails,
    then the MCtx is left unchanged. -/
def subsumptionCheck (subsumingClause : MClause) (subsumedClause : MClause) (subsumedClauseMVarIds : Array MVarId) : RuleM Bool :=
  conditionallyModifyingMCtx do -- Only modify the MCtx if the subsumption check succeeds (so failed checks don't impact future checks)
    if subsumingClause.lits.size > subsumedClause.lits.size then return (false, false)
    match ← subsumptionCheckHelper (subsumingClause.lits).toList subsumedClause subsumedClauseMVarIds {} [] with
    | some _ => return (true, true)
    | none => return (false, false)

/-- Same as `subsumptionCheck`, but if the subsumption check succeeds, it additionally returns lists `assignment` and `assignmentIsFlipped` such that:
    - `∀ i ∈ [0, subsumingClauseLits.length], σ(subsumingClauseLits.get! i) = subsumedClauseLits[(assignment.reverse.get! i).1]` if
      `(assignment.reverse.get! i).2` is false
    - `∀ i ∈ [0, subsumingClauseLits.length], σ(subsumingClauseLits.get! i) = subsumedClauseLits[(assignment.reverse.get! i).1]` with swapped lhs/rhs if
      `(assignment.reverse.get! i).2` is true
    - Note that `assignment` is not reversed in the above lines because this function reverses the output of `subsumptionCheckHelper` -/
def subsumptionCheck' (subsumingClause : MClause) (subsumedClause : MClause) (subsumedClauseMVarIds : Array MVarId) : RuleM (Option (List (Nat × Bool))) :=
  conditionallyModifyingMCtx do -- Only modify the MCtx if the subsumption check succeeds (so failed checks don't impact future checks)
    if subsumingClause.lits.size > subsumedClause.lits.size then return (false, none)
    match ← subsumptionCheckHelper (subsumingClause.lits).toList subsumedClause subsumedClauseMVarIds {} [] with
    | some assignment => return (true, some assignment.reverse)
    | none => return (false, none)
