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

inductive BackwardSimpResult
| Removed (removedClauses : List MClause) : BackwardSimpResult
| Applied (transformedClauses : List (MClause × (MClause × Option ProofReconstructor))) : BackwardSimpResult
| Unapplicable : BackwardSimpResult
deriving Inhabited

open SimpResult

abbrev MSimpRule := Clause → RuleM Bool
-- Returns true iff simplification rule was applied.
-- - The clause will be replaced by all clauses introduced via `yieldClause`.
-- - If `yieldClause` was not called, the clause will be removed.

abbrev SimpRule := Clause → ProverM (SimpResult Clause)

abbrev BackwardMSimpRule := Clause → RuleM BackwardSimpResult
abbrev BackwardSimpRule := Clause → ProverM Bool -- Returns true iff any backward simplification was done (meaning backwardSimpLoop needs to loop)

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
      -- Register and return first result clause without adding it to the active or passive set. Add other result clauses to passive set
      let ci ← addNewClause c proof
      for (c, proof) in restCs do
        addNewToPassive c proof
      if ci.wasSimplified then return Removed -- No need to continue working on c because we've already seen previously that it will be simplified away
      return Applied c

def BackwardMSimpRule.toBackwardSimpRule (rule : BackwardMSimpRule) (ruleName : String) : BackwardSimpRule :=
  fun givenClause => do
  let (clausesToRemove, cs) ← runSimpRule do
    withoutModifyingMCtx do
      match ← rule givenClause with
      | BackwardSimpResult.Removed removedClauses =>
        let mut clausesToRemove : List Clause := []
        for c in removedClauses do
          clausesToRemove := (← neutralizeMClause c) :: clausesToRemove
        return clausesToRemove
      | BackwardSimpResult.Applied transformedClauses =>
        let mut clausesToRemove : List Clause := []
        for (oldClause, c, mkProof) in transformedClauses do
          yieldClause c ruleName mkProof
          clausesToRemove := (← neutralizeMClause oldClause) :: clausesToRemove
        return clausesToRemove
      | BackwardSimpResult.Unapplicable => return []
  -- It is important that we remove each clause in clausesToRemove before readding the newly generated clauses
  for c in clausesToRemove do
    trace[RemoveClause.debug] "About to remove {c} because it was simplified away to produce {cs.map (fun x => x.1)}"
    removeClause c [givenClause] -- givenClause must be protected when we remove c and its descendants because givenClause was used to eliminate c
  for (c, proof) in cs do addNewToPassive c proof -- Add each yielded clause to the passive set
  return not clausesToRemove.isEmpty -- If clausesToRemove is nonempty, then some simplification was performed, so return true. Otherwise, return false

end Duper
