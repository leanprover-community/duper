import Duper.ProverM
import Duper.RuleM
import Duper.MClause

namespace Duper
open RuleM
open ProverM

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
  let res ← runSimpRule (rule givenClause)
  match res with
  | none => 
    return Unapplicable
  | some cs => do
    trace[RemoveClause.debug] "About to remove {givenClause} because it was simplified away to produce {cs.map (fun x => x.1)}"
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated clauses
    match cs.data with
    | List.nil => return Removed
    | (c, proof) :: restCs =>
      match (← getAllClauses).find? givenClause with
      | some givenClauseInfo =>
        -- For forward simplification rules, each result clause has the same set of generating ancestors as givenClause
        let generatingAncestors := givenClauseInfo.generatingAncestors
        -- Register and return first result clause without adding it to the active or passive set. Add other result clauses to passive set
        let ci ← addNewClause c proof generatingAncestors
        for (c, proof) in restCs do
          addNewToPassive c proof generatingAncestors
        if ci.wasSimplified then return Removed -- No need to continue working on c because we've already seen previously that it will be simplified away
        return Applied c
      | none => throwError "givenClause {givenClause} was not found"

def BackwardMSimpRule.toBackwardSimpRule (rule : BackwardMSimpRule) : BackwardSimpRule :=
  fun givenClause => do
  let backwardSimpRes ← runSimpRule do
    withoutModifyingMCtx do
      rule givenClause
  let mut generatingAncestorsArray : Array (List Clause) := #[]
  -- It is important that we remove each clause in clausesToRemove before reading the newly generated clauses
  for (c, _) in backwardSimpRes do
    trace[RemoveClause.debug] "About to remove {c} because it was simplified away"
    removeClause c [givenClause] -- givenClause must be protected when we remove c and its descendants because givenClause was used to eliminate c
    match (← getAllClauses).find? c with
    | some ci => generatingAncestorsArray := generatingAncestorsArray.push ci.generatingAncestors
    | none => throwError "Could not find {c} in all clauses"
  for (generatingAncestors, _, ocp) in generatingAncestorsArray.zip backwardSimpRes do
    if let some (c, proof) := ocp then
      addNewToPassive c proof generatingAncestors

end Duper
