import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Util.Iterate

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

abbrev MSimpRule := Clause → RuleM Bool
-- Returns true iff simplification rule was applied.
-- - The clause will be replaced by all clauses introduced via `yieldClause`.
-- - If `yieldClause` was not called, the clause will be removed.

abbrev SimpRule := Clause → ProverM (SimpResult Clause)

abbrev BackwardMSimpRule := Clause → RuleM (List Clause)
/-
Returns the list of clauses that are to be removed by simplification
  - Clauses that are to be removed will be replaced by clauses introduced via `yieldClause`
  - An important invariant is that the i-th clause produced via `yieldClause` must have been produced by the i-th clause in the result list.
    This invariant ensures that we can figure out the correct set of generatingAncestors for each new clause.
-/

abbrev BackwardSimpRule := Clause → ProverM Unit

def MSimpRule.toSimpRule (rule : MSimpRule) : SimpRule := fun givenClause => do
  let (res, cs) ← runSimpRule (rule givenClause)
  match res with
  | false => 
    if ¬ cs.isEmpty then throwError "Simp rule returned failure, but produced clauses {cs.map Prod.fst}"
    return Unapplicable
  | true => do
    trace[RemoveClause.debug] "About to remove {givenClause} because it was simplified away to produce {cs.map (fun x => x.1)}"
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated clauses
    match cs with
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
  let (clausesToRemove, cs) ← runSimpRule do
    withoutModifyingMCtx do
      rule givenClause
  /-
    We have as an invariant that the i-th clause we remove has the generating ancestors of the i-th clause that we add via `yieldClause`.
    So to figure out what the generatingAncestors should be when we call `addNewToPassive`, we can look at the corresponding generating
    ancestors from clausesToRemove.
  -/
  let mut generatingAncestorsList : List (List Clause) := []
  -- It is important that we remove each clause in clausesToRemove before readding the newly generated clauses
  for c in clausesToRemove do
    trace[RemoveClause.debug] "About to remove {c} because it was simplified away to produce {cs.map (fun x => x.1)}"
    removeClause c [givenClause] -- givenClause must be protected when we remove c and its descendants because givenClause was used to eliminate c
    match (← getAllClauses).find? c with
    | some ci => generatingAncestorsList := ci.generatingAncestors :: generatingAncestorsList
    | none => throwError "Could not find {c} in all clauses"
  generatingAncestorsList := generatingAncestorsList.reverse -- Putting generatingAncestorsList in the right order for the next loop
  for (c, proof) in cs do
    match generatingAncestorsList with
    | generatingAncestors :: restGeneratingAncestorsList =>
      addNewToPassive c proof generatingAncestors -- Add each yielded clause to the passive set
      generatingAncestorsList := restGeneratingAncestorsList
    | List.nil => throwError "Number of removed clauses in {clausesToRemove} did not match with number of clauses generated"

end Duper
