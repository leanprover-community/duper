import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Lean
open RuleM
open SimpResult

initialize Lean.registerTraceClass `Rule.boolHoist

theorem bool_hoist_proof (f : Prop → Prop) (e : Prop) (H : f e) : f True ∨ e = False :=
  @Classical.byCases e _
    (fun p => have h : e = True := by simp [p];
              Or.inl (h ▸ H))
    (fun np => by simp [np])

theorem loob_hoist_proof (f : Prop → Prop) (e : Prop) (H : f e) : f False ∨ e = True :=
  @Classical.byCases e _
    (fun p => by simp [p])
    (fun np => have h : e = False := by simp [np];
               Or.inl (h ▸ H))

def boolHoistAtExpr (e : Expr) (pos : ClausePos) (c : MClause) : RuleM Unit :=
  withoutModifyingMCtx do
    if c.lits[pos.lit]!.sign && pos.pos == #[] then -- e cannot be at the top level of a positive literal
      return ()
    if (e.getTopSymbol).isMVar then -- e cannot be variable headed
      return ()
    if (e.isFullyAppliedLogicalSymbol) then -- e cannot be a fully applied logical symbol
      return ()
    let eligibility ← eligibilityPreUnificationCheck c pos.lit
    if eligibility == Eligibility.notEligible then
      return ()
    let eType ← inferType e
    if not $ ← unify #[(eType, .sort levelZero)] then
      return () -- Unification failed, so boolHoist cannot occur
    if not $ ← eligibilityPostUnificationCheck c pos.lit eligibility (strict := c.lits[pos.lit]!.sign) then
      return ()
    let lit := c.lits[pos.lit]!.makeLhs pos.side
    let lhs ← RuleM.instantiateMVars lit.lhs
    let rhs ← RuleM.instantiateMVars lit.rhs
    let cmp ← compare lhs rhs
    if cmp == Comparison.LessThan || cmp == Comparison.Equal then -- If lhs ≤ rhs then e is not in an eligible position
      return ()
    -- All side conditions have been met. Yield the appropriate clause
    sorry

def boolHoist (c : MClause) (cNum : Nat) : RuleM Unit := do
  let fold_fn := fun () e pos => boolHoistAtExpr e pos c
  c.foldGreenM fold_fn ()