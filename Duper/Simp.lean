import Duper.ProverM
import Duper.RuleM
import Duper.MClause

namespace Duper
open Lean Meta RuleM ProverM

inductive SimpResult (α : Type)
| Applied (c : α) : SimpResult α
| Unapplicable : SimpResult α
| Removed : SimpResult α
deriving Inhabited

namespace SimpResult

def mapM [Monad m] (f : α → m β) : SimpResult α → m (SimpResult β)
| Applied c    => return Applied (← f c)
| Unapplicable => return Unapplicable
| Removed      => return Removed

def forM {m : Type u → Type v} [Monad m] {α : Type} (r : SimpResult α) (f : α → m PUnit) : m PUnit :=
match r with
| Applied c    => f c
| Unapplicable => return PUnit.unit
| Removed      => return PUnit.unit

end SimpResult

open SimpResult

abbrev MSimpRule := Clause → RuleM (Option (Array (Clause × Proof)))
-- Returns true iff simplification rule was applied.
-- - The clause will be replaced by all clauses introduced via `yieldClause`.
-- - If `yieldClause` was not called, the clause will be removed.
-- Note: Here the `Option` cannot be concatenated with `Array`, refer to
--   `MSimpRule.toSimpRule`

abbrev SimpRule := Clause → ProverM (SimpResult Clause)

abbrev BackwardMSimpRule := Clause → RuleM (Array (Clause × Option (Clause × Proof)))
/-
  The `List Clause` are clauses to be removed
  The `List (Clause × Proof)` are the result clauses
  - Clauses that are to be removed will be replaced by clauses introduced via `yieldClause`
  - An important invariant is that the i-th clause produced via `yieldClause` must have been produced by the i-th clause in the result list.
    This invariant ensures that we can figure out the correct set of generatingAncestors for each new clause.
-/

abbrev BackwardSimpRule := Clause → ProverM Unit

def MSimpRule.toSimpRule (rule : MSimpRule) : SimpRule := fun givenClause => do
  let res ← runRuleM (rule givenClause)
  match res with
  | none =>
    return Unapplicable
  | some cs => do
    trace[duper.simplification.debug] "About to remove {givenClause} because it was simplified away to produce {cs.map (fun x => x.1)}"
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated clauses
    match cs.toList with
    | List.nil => return Removed
    | (c, proof) :: restCs =>
      match (← getAllClauses).get? givenClause with
      | some givenClauseInfo =>
        -- For forward simplification rules, each result clause has the same set of generating ancestors as givenClause
        let generatingAncestors := givenClauseInfo.generatingAncestors
        -- For forward simplification rules, each result clause has the same generation number as givenClause
        let generationNumber := givenClauseInfo.generationNumber
        /- Here, we define goalDistance as the same as the given clause's goal distance (since simplification rules don't add distance). Zipperposition
           does something slightly different, taking the goal distance of the parent closest to the goal (meaning if res was created by demodulation and
           the side clause was closer to the goal than the main clause, res's goal distance would be the same as the side clause's rather than the main
           clause). It might make sense to modify this code in the future to match that strategy, but for now, it's significantly more convenient to just
           use the given clause's distance to the goal. -/
        let goalDistance := givenClauseInfo.goalDistance
        -- Register and return first result clause without adding it to the active or passive set. Add other result clauses to passive set
        let ci ← addNewClause c proof goalDistance generationNumber generatingAncestors
        for (c, proof) in restCs do
          addNewToPassive c proof goalDistance generationNumber generatingAncestors
        if ci.wasSimplified then return Removed -- No need to continue working on c because we've already seen previously that it will be simplified away
        return Applied c
      | none => throwError "givenClause {givenClause} was not found"

def BackwardMSimpRule.toBackwardSimpRule (rule : BackwardMSimpRule) : BackwardSimpRule :=
  fun givenClause => do
  let backwardSimpRes ← runRuleM do
    withoutModifyingMCtx do
      rule givenClause
  -- acc is used to store the goalDistance, generationNumber, and generatingAncestors of each clause in backwardSimpRes
  let mut acc : Array (Nat × Nat × Array Clause) := #[]
  -- It is important that we remove each clause in clausesToRemove before reading the newly generated clauses
  for (c, _) in backwardSimpRes do
    trace[duper.simplification.debug] "About to remove {c} because it was simplified away"
    removeClause c [givenClause] -- givenClause must be protected when we remove c and its descendants because givenClause was used to eliminate c
    match (← getAllClauses).get? c with
    | some ci =>
      /- To match the strategy used for forward simplification, we use `ci.goalDistance` to ensure that the new clause is given the same goal distance as
         its main parent `c`. But if, in the future, we adopt Zipperposition's approach of giving the new clause the minimum goal distance of all its parents
         (i.e. `c` and `givenClause`), then we would replace `ci.goalDistance` below with the minimum of and ci.goalDistance givenClause.goalDistance. -/
      acc := acc.push (ci.goalDistance, ci.generationNumber, ci.generatingAncestors)
    | none => throwError "Could not find {c} in all clauses"
  for ((goalDistance, generationNumber, generatingAncestors), _, ocp) in acc.zip backwardSimpRes do
    if let some (c, proof) := ocp then
      addNewToPassive c proof goalDistance generationNumber generatingAncestors

end Duper
