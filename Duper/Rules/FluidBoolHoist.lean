import Duper.RuleM
import Duper.Selection
import Duper.Util.Misc
import Duper.Util.ProofReconstruction
import Duper.Rules.FluidSup

namespace Duper
open RuleM
open Lean
open Meta

initialize
  registerTraceClass `duper.rule.fluidBoolHoist
  registerTraceClass `duper.rule.fluidLoobHoist

theorem fluid_bool_hoist_proof {α} (f : α → Prop) (x : Prop) (z : Prop → α) (H : f (z x)) : f (z False) ∨ x = True := by
  by_cases hx : x
  . exact Or.inr $ eq_true hx
  . rw [eq_false hx] at H
    exact Or.inl H

theorem fluid_loob_hoist_proof {α} (f : α → Prop) (x : Prop) (z : Prop → α) (H : f (z x)) : f (z True) ∨ x = False := by
  by_cases hx : x
  . rw [eq_true hx] at H
    exact Or.inl H
  . exact Or.inr $ eq_false hx

def mkFluidBoolHoistProof (pos : ClausePos) (isFluidLoobHoist : Bool) (premises : List Expr)
  (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let #[freshFunctionOutputType, freshFunction, freshPropVar] := transferExprs
      | throwError "mkFluidBoolHoistProof :: Wrong number of transferExprs"

    let i := pos.lit
    let lp := pos.toLitPos

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        let f ← Meta.withLocalDeclD `h freshFunctionOutputType fun h => do
          let lit' ← lit.replaceAtPos! lp h
          let f := lit'.toExpr
          Meta.mkLambdaFVars #[h] f
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let mut pr := h
          if isFluidLoobHoist then
            pr ← Meta.mkAppM ``fluid_loob_hoist_proof #[f, freshPropVar, freshFunction, h]
          else
            pr ← Meta.mkAppM ``fluid_bool_hoist_proof #[f, freshPropVar, freshFunction, h]
          Meta.mkLambdaFVars #[h] $ ← orSubclause (cLits.map Lit.toExpr) 2 pr
        caseProofs := caseProofs.push pr
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofs := caseProofs.push pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def fluidBoolHoistAtExpr (e : Expr) (pos : ClausePos) (given : Clause) (c : MClause) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx do
    if not (Order.isFluid e) then return #[]

    let litEligibility ← eligibilityPreUnificationCheck c true pos.lit
    let lit := c.lits[pos.lit]!.makeLhs pos.side
    let sideComparison ← RuleM.compare lit.lhs lit.rhs true
    if litEligibility == Eligibility.notEligible || sideComparison == Comparison.LessThan then return #[]

    let freshFunctionOutputType ← inferType e
    let freshFunction ← mkFreshFunction (mkSort levelZero) freshFunctionOutputType -- mkFreshFunction defined in FluidSup.lean
    let freshPropVar ← mkFreshExprMVar (mkSort levelZero)
    let freshFunctionApp ← Meta.whnf (.app freshFunction freshPropVar)

    let loaded ← getLoadedClauses
    let ug ← unifierGenerator #[(e, freshFunctionApp)]

    let boolHoistYC := do
      setLoadedClauses loaded
      let finalEligibility ← eligibilityPostUnificationCheck c false pos.lit litEligibility
      let finalSideComparison ← RuleM.compare lit.lhs lit.rhs false
      if finalSideComparison == Comparison.LessThan || finalSideComparison == Comparison.Equal || not finalEligibility then
        return none

      -- Check condition 5
      let freshPropVar ← betaEtaReduceInstMVars freshPropVar
      if (freshPropVar == mkConst ``True || freshPropVar == mkConst ``False) then return none

      -- Check condition 4 (boolhoist)
      let freshFunctionApp ← betaEtaReduceInstMVars freshFunctionApp
      let freshFunctionGivenFalse := ← betaEtaReduceInstMVars (.app freshFunction (mkConst ``False))
      if (freshFunctionGivenFalse == freshFunctionApp) then return none

      -- All side conditions for fluidBoolHoist have been met
      let cErased := c.eraseLit pos.lit
      let litOriginal := c.lits[pos.lit]! -- No lhs/rhs swap
      let some newLit ← litOriginal.replaceAtPosUpdateType? ⟨pos.side, pos.pos⟩ freshFunctionGivenFalse
        | return none -- If `litOriginal` can't be safely changed at position `pos`, then don't apply fluidBoolHoist at `pos`
      let newClause := cErased.appendLits #[newLit, Lit.fromSingleExpr freshPropVar true]
      trace[duper.rule.fluidBoolHoist] "Created {newClause.lits} from {c.lits}"
      let mkProof := mkFluidBoolHoistProof pos false -- Is fluidBoolHoist not fluidLoobHoist
      yieldClause newClause "fluidBoolHoist" mkProof (transferExprs := #[freshFunctionOutputType, freshFunction, freshPropVar])

    let loobHoistYC := do
      setLoadedClauses loaded
      let finalEligibility ← eligibilityPostUnificationCheck c false pos.lit litEligibility
      let finalSideComparison ← RuleM.compare lit.lhs lit.rhs false
      if finalSideComparison == Comparison.LessThan || finalSideComparison == Comparison.Equal || not finalEligibility then
        return none

      -- Check condition 5
      let freshPropVar ← betaEtaReduceInstMVars freshPropVar
      if (freshPropVar == mkConst ``True || freshPropVar == mkConst ``False) then return none

      -- Check condition 4 (loobHoist)
      let freshFunctionApp ← betaEtaReduceInstMVars freshFunctionApp
      let freshFunctionGivenTrue := ← betaEtaReduceInstMVars (.app freshFunction (mkConst ``True))
      if (freshFunctionGivenTrue == freshFunctionApp) then return none

      -- All side conditions for fluidLoobHoist have been met
      let cErased := c.eraseLit pos.lit
      let litOriginal := c.lits[pos.lit]! -- No lhs/rhs swap
      let some newLit ← litOriginal.replaceAtPosUpdateType? ⟨pos.side, pos.pos⟩ freshFunctionGivenTrue
        | return none -- If `litOriginal` can't be safely changed at position `pos`, then don't apply fluidBoolHoist at `pos`
      let newClause := cErased.appendLits #[newLit, Lit.fromSingleExpr freshPropVar false]
      trace[duper.rule.fluidLoobHoist] "Created {newClause.lits} from {c.lits}"
      let mkProof := mkFluidBoolHoistProof pos true -- True because this is fluidLoobHoist
      yieldClause newClause "fluidLoobHoist" mkProof (transferExprs := #[freshFunctionOutputType, freshFunction, freshPropVar])

    return #[ClauseStream.mk ug given boolHoistYC "fluidBoolHoist", ClauseStream.mk ug given loobHoistYC "fluidLoobHoist"]

def fluidBoolHoist (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  let fold_fn := fun streams e pos => do
    let str ← fluidBoolHoistAtExpr e pos given c
    return streams.append str
  c.foldGreenM fold_fn #[]
