import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Std
open ProverM
open RuleM
open SimpResult
open Lean
open Meta

initialize
  Lean.registerTraceClass `Rule.removeInhabitedConstraint
  Lean.registerTraceClass `Rule.resolveInhabitedConstraint

def getNonemptyType (givenSideClause : MClause) : Option Expr :=
  if givenSideClause.lits.size != 1 then none
  else
    let lit := givenSideClause.lits[0]!
    match lit.lhs, lit.rhs with
    | .app (.const ``Nonempty _) t, .const ``True _ => some t
    | .const ``True _, .app (.const ``Nonempty _) t => some t
    | _, _ => none

/-- If `givenSideClause` is of the form `Nonempty t = True` or `True = Nonempty t`, then look through the set of
    potentially vacuous clauses and for each clause that has a vanished var of type `t`, simplify that clause away
    to produce a clause that does not have that vanished var -/
def removeInhabitedConstraint (potentiallyVacuousClauses : ClauseSet) : BackwardMSimpRule := fun givenSideClause => do
  let givenSideClause ← loadClause givenSideClause
  match getNonemptyType givenSideClause with
  | none => return #[]
  | some t =>
    trace[Rule.removeInhabitedConstraint] "Calling removeInhabitedConstraint with type {t} from {givenSideClause.lits}"
    let mut result := #[]
    for c in potentiallyVacuousClauses do
      let res ←
        withoutModifyingLoadedClauses do
          withoutModifyingMCtx do
            let (mvars, c) ← loadClauseCore c
            let cExpr := c.toExpr
            let fold_fn := fun (res : Option (Clause × Proof)) (mvar : Expr) => do
              match res with
              | some _ => return res
              | none =>
                -- TODO: Rather than (← inferType mvar) == t, I should try to match t onto (← inferType mvar)
                -- This way, if I derived `Nonempty (Option ?m) = True`, I can use that for any `Option` type
                -- inhabitation constraints
                if cExpr.abstract #[mvar] == cExpr && (← inferType mvar) == t then
                  -- TODO: Proof reconstruction
                  some <$> yieldClause c "removeInhabitedConstraint" none (mvarIdsToRemove := #[mvar.mvarId!])
                else return none
            mvars.foldlM fold_fn none
      if let some cp := res then
        result := result.push (c, some cp)
    trace[Rule.removeInhabitedConstraint] "Result: {result.map (fun x => x.2.get!.1)}"
    return result

-- TODO: resolveInhabitedConstraint (the inference rule version of removeInhabitedConstraint)