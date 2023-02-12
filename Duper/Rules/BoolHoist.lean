import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction
import Duper.Rules.IdentBoolHoist

namespace Duper
open Lean
open RuleM
open SimpResult

initialize Lean.registerTraceClass `Rule.boolHoist

def boolHoistAtExpr (e : Expr) (pos : ClausePos) (c : MClause) : RuleM Unit :=
  withoutModifyingMCtx do
    if c.lits[pos.lit]!.sign && pos.pos == #[] then -- e cannot be at the top level of a positive literal
      return
    if (e.getTopSymbol).isMVar then -- e cannot be variable headed
      return
    if (e.isFullyAppliedLogicalSymbol) then -- e cannot be a fully applied logical symbol
      return
    if not (← eligibilityNoUnificationCheck c pos.lit) then
      -- No unificaiton check rather than PreUnification check because condition 3 talks about the position being eligible in
      -- the original clause (as opposed to being eligible in the clause with respect to the substitution σ)
      return
    let eType ← inferType e
    if not $ ← unify #[(eType, .sort levelZero)] then
      return -- Unification failed, so boolHoist cannot occur
    let lit := c.lits[pos.lit]!
    let eSide ← RuleM.instantiateMVars $ lit.getSide pos.side
    let otherSide ← RuleM.instantiateMVars $ lit.getOtherSide pos.side
    let cmp ← compare eSide otherSide
    if cmp == Comparison.LessThan || cmp == Comparison.Equal then -- If eSide ≤ otherSide then e is not in an eligible position
      return
    -- All side conditions have been met. Yield the appropriate clause
    let cErased := c.eraseLit pos.lit
    let newClause := cErased.appendLits #[← lit.replaceAtPos! ⟨pos.side, pos.pos⟩ (mkConst ``False), Lit.fromSingleExpr e true]
    trace[Rule.boolHoist] "Created {newClause.lits} from {c.lits}"
    yieldClause newClause "boolHoist" $ some (mkBoolHoistProof pos false)

def boolHoist (c : MClause) (cNum : Nat) : RuleM Unit := do
  let fold_fn := fun () e pos => boolHoistAtExpr e pos c
  c.foldGreenM fold_fn ()