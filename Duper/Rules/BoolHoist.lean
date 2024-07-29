import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction
import Duper.Rules.IdentBoolHoist

namespace Duper
open Lean
open RuleM
open Meta
open SimpResult

initialize Lean.registerTraceClass `duper.rule.boolHoist

def boolHoistAtExpr (e : Expr) (pos : ClausePos) (given : Clause) (c : MClause) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx do
    if c.lits[pos.lit]!.sign && pos.pos == #[] then -- e cannot be at the top level of a positive literal
      return #[]
    if (e.getTopSymbol).isMVar' then -- e cannot be variable headed
      return #[]
    if (e.isFullyAppliedLogicalSymbol) then -- e cannot be a fully applied logical symbol
      return #[]
    if not (← eligibilityNoUnificationCheck c (alreadyReduced := true) pos.lit) then
      -- No unificaiton check rather than PreUnification check because condition 3 talks about the position being eligible in
      -- the original clause (as opposed to being eligible in the clause with respect to the substitution σ)
      return #[]
    let eType ← inferType e
    let loaded ← getLoadedClauses
    let ug ← unifierGenerator #[(eType, .sort levelZero)]
    let yC := do
      setLoadedClauses loaded
      let lit := c.lits[pos.lit]!
      let eSide := lit.getSide pos.side
      let otherSide := lit.getOtherSide pos.side
      let cmp ← compare eSide otherSide false
      if cmp == Comparison.LessThan || cmp == Comparison.Equal then -- If eSide ≤ otherSide then e is not in an eligible position
        return none
      -- All side conditions have been met. Yield the appropriate clause
      let cErased := c.eraseLit pos.lit
      let some newLit ← lit.replaceAtPosUpdateType? ⟨pos.side, pos.pos⟩ (mkConst ``False)
        | return none -- If `lit` can't be safely changed at position `p`, then don't apply `boolHoist` at `p`
      let newClause := cErased.appendLits #[newLit, Lit.fromSingleExpr e true]
      trace[duper.rule.boolHoist] "Created {newClause.lits} from {c.lits}"
      yieldClause newClause "boolHoist" $ some (mkBoolHoistProof pos false)
    return #[ClauseStream.mk ug given yC "boolHoist"]

def boolHoist (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[duper.rule.boolHoist] "Running BoolHoist on {c.lits}"
  let fold_fn := fun streams e pos => do
    let str ← boolHoistAtExpr e pos given c
    return streams.append str
  c.foldGreenM fold_fn #[]
