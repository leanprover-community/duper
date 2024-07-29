import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Lean
open Meta
open RuleM
open SimpResult

initialize Lean.registerTraceClass `duper.rule.neHoist

theorem ne_hoist_proof (x y : α) (f : Prop → Prop) (h : f (x ≠ y)) : f True ∨ x = y := by
  by_cases x_eq_y : x = y
  . exact Or.inr x_eq_y
  . rename ¬x = y => x_ne_y
    have x_ne_y_true := eq_true x_ne_y
    exact Or.inl $ x_ne_y_true ▸ h

def mkNeHoistProof (pos : ClausePos) (premises : List Expr)
  (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let #[freshVar1, freshVar2] := transferExprs
      | throwError "mkNeHoistProof :: Wrong number of transferExprs"

    let mut caseProofs := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
        if i == pos.lit then
          let substLitPos : LitPos := ⟨pos.side, pos.pos⟩
          let abstrLit ← (lit.abstractAtPos! substLitPos)
          let abstrExp := abstrLit.toExpr
          let abstrLam := mkLambda `x BinderInfo.default (mkSort levelZero) abstrExp
          let lastTwoClausesProof ← Meta.mkAppM ``ne_hoist_proof #[freshVar1, freshVar2, abstrLam, h]
          Meta.mkLambdaFVars #[h] $ ← orSubclause (cLits.map Lit.toExpr) 2 lastTwoClausesProof
        else
          let idx := if i ≥ pos.lit then i - 1 else i
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
      caseProofs := caseProofs.push pr
    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def neHoistAtExpr (e : Expr) (pos : ClausePos) (given : Clause) (c : MClause) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx do
    let lit := c.lits[pos.lit]!
    if e.getTopSymbol.isMVar' then -- Check condition 4
      -- If the head of e is a variable then it must be applied and the affected literal must be either
      -- e = True, e = False, or e = e' where e' is another variable headed term
      if not e.isApp then -- e is a non-applied variable and so we cannot apply neHoist
        return #[]
      if pos.pos != #[] then
        return #[] -- e is not at the top level so the affected literal cannot have the form e = ...
      if not lit.sign then
        return #[] -- The affected literal is not positive and so it cannot have the form e = ...
      let otherSide := lit.getOtherSide pos.side
      if otherSide != (mkConst ``True) && otherSide != (mkConst ``False) && not otherSide.getTopSymbol.isMVar' then
        return #[] -- The other side is not True, False, or variable headed, so the affected literal cannot have the required form
    -- Check conditions 1 and 3 (condition 2 is guaranteed by construction)
    let eligibility ← eligibilityPreUnificationCheck c (alreadyReduced := true) pos.lit
    if eligibility == Eligibility.notEligible then
      return #[]
    -- Make freshVars, freshVarInequality, and freshVarEquality
    let freshVar1 ← mkFreshExprMVar none
    let freshVarTy ← inferType freshVar1
    let freshVar2 ← mkFreshExprMVar freshVarTy
    let freshVarInequality ← mkAppM ``Ne #[freshVar1, freshVar2]
    let freshVarEquality ← mkAppM ``Eq #[freshVar1, freshVar2]
    -- Perform unification
    let ug ← unifierGenerator #[(e, freshVarInequality)]
    let loaded ← getLoadedClauses
    let yC := do
      setLoadedClauses loaded
      if not $ ← eligibilityPostUnificationCheck c (alreadyReduced := false) pos.lit eligibility (strict := lit.sign) then
        return none
      let eSide := lit.getSide pos.side
      let otherSide := lit.getOtherSide pos.side
      let cmp ← compare eSide otherSide false
      if cmp == Comparison.LessThan || cmp == Comparison.Equal then -- If eSide ≤ otherSide then e is not in an eligible position
        return none
      -- All side conditions have been met. Yield the appropriate clause
      let cErased := c.eraseLit pos.lit
      let some newLit ← lit.replaceAtPosUpdateType? ⟨pos.side, pos.pos⟩ (mkConst ``True)
        | return none -- If `lit` can't be safely changed at position `pos`, then don't apply `neHoist` at `pos`
      let newClause := cErased.appendLits #[newLit, Lit.fromExpr freshVarEquality]
      trace[duper.rule.neHoist] "Created {newClause.lits} from {c.lits}"
      let mkProof := mkNeHoistProof pos
      yieldClause newClause "neHoist" mkProof (transferExprs := #[freshVar1, freshVar2])
    return #[ClauseStream.mk ug given yC "neHoist"]

def neHoist (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[duper.rule.neHoist] "Running NeHoist on {c.lits}"
  let fold_fn := fun streams e pos => do
    let str ← neHoistAtExpr e.consumeMData pos given c
    return streams.append str
  c.foldGreenM fold_fn #[]
