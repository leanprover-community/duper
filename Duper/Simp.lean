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
  /-
    The way I currently handle generating ancestors is a temporary measure until I restructure backwards simplification.

    The plan is to, as we remove each clause, note that the i-th clause we remove has the generating ancestors of the i-th clause
    that we add. So to figure out what the generatingAncestors should be when we call addNewToPassive, we can look at the
    corresponding generating ancestors from clausesToRemove. This is extremely hacky and I fully intend to do away with it once
    I restructure backwards simplification.
  -/
  let mut generatingAncestorsList : List (List Clause) := []
  -- It is important that we remove each clause in clausesToRemove before readding the newly generated clauses
  for c in clausesToRemove do
    trace[RemoveClause.debug] "About to remove {c} because it was simplified away to produce {cs.map (fun x => x.1)}"
    removeClause c [givenClause] -- givenClause must be protected when we remove c and its descendants because givenClause was used to eliminate c
    match (← getAllClauses).find? c with
    | some ci => generatingAncestorsList := ci.generatingAncestors :: generatingAncestorsList
    | none =>
      /-
        Note: Currently, there is a bug that sometimes causes c to not actually be the original clause that we want to remove, but a modification
        of said clause with some of its original metavariables instantiated. Once I fix this bug, the line below should throw an error (rather than
        just pretend like there are no generating clauses). But I'm using this as a stop-gap measure for now in recognition of the fact that I intend
        to restructure backward simplification soon anyway.
      -/
      generatingAncestorsList := [] :: generatingAncestorsList
      -- throwError "Could not find {c} in all clauses"
  generatingAncestorsList := generatingAncestorsList.reverse -- Putting generatingAncestorsList in the right order for the next loop
  for (c, proof) in cs do
    match generatingAncestorsList with
    | generatingAncestors :: restGeneratingAncestorsList =>
      addNewToPassive c proof generatingAncestors -- Add each yielded clause to the passive set
      generatingAncestorsList := restGeneratingAncestorsList
    | List.nil => throwError "Number of removed clauses in {clausesToRemove} did not match with number of clauses generated"
  return not clausesToRemove.isEmpty -- If clausesToRemove is nonempty, then some simplification was performed, so return true. Otherwise, return false

end Duper
