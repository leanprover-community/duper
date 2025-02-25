import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction

set_option linter.unusedVariables false

-- LoobHoist          BoolHoist
--             C<u>
-- -----------------------------
-- C<⊤> ∨ u = ⊥     C<⊥> ∨ u = ⊤
--
-- where u is of type Prop, but neither ⊥ nor ⊤, and u is not at the top level of a positive literal.

namespace Duper
open Lean
open RuleM
open Meta
open SimpResult

initialize Lean.registerTraceClass `duper.rule.identBoolHoist

theorem loob_hoist_proof (f : Prop → Prop) (e : Prop) (H : f e) : f True ∨ e = False :=
  @Classical.byCases e _
    (fun p => have h : e = True := by simp [p];
              Or.inl (h ▸ H))
    (fun np => by simp [np])

theorem bool_hoist_proof (f : Prop → Prop) (e : Prop) (H : f e) : f False ∨ e = True :=
  @Classical.byCases e _
    (fun p => by simp [p])
    (fun np => have h : e = False := by simp [np];
               Or.inl (h ▸ H))

def mkBoolHoistProof (pos : ClausePos) (sgn : Bool) (premises : List Expr)
  (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let i := pos.lit
    let ⟨s, p⟩ := pos.toLitPos

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        let lp : LitPos := ⟨s, p⟩
        let f ← Meta.withLocalDeclD `h (.sort .zero) fun h => do
          let lit' ← lit.replaceAtPos! lp h
          let f := lit'.toExpr
          Meta.mkLambdaFVars #[h] f
        let e ← lit.getAtPos! lp
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let mut pr := h
          if sgn then
            pr ← Meta.mkAppM ``loob_hoist_proof #[f, e, h]
          else
            pr ← Meta.mkAppM ``bool_hoist_proof #[f, e, h]
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

def identBoolHoistAtExpr (e : Expr) (pos : ClausePos) (c : MClause) : RuleM (Option (Array (Clause × Proof))) :=
  withoutModifyingMCtx do
    let ty ← inferType e
    if ty == .sort .zero then
      let l := pos.lit
      let ⟨s, p⟩ := pos.toLitPos
      trace[duper.rule.identBoolHoist] m!"Inspecting position {pos} in clause {c.lits.map Lit.toExpr}"
      let is_true := e == (mkConst ``True)
      let is_false := e == (mkConst ``False)
      let is_top_positive := p.size == 0 ∧ c.lits[l]!.sign
      if is_true ∨ is_false ∨ is_top_positive then
        return none
      else
        trace[duper.rule.identBoolHoist] m!"BoolHoist at literal {l}, side {s}, position {p} in clause {c.lits.map Lit.toExpr}"
        let litl := c.lits[l]!
        let some litl1 ← litl.replaceAtPosUpdateType? ⟨s, p⟩ (mkConst ``True)
          | return none -- If `litl` can't be safely changed at position `p`, then don't apply `identBoolHoist` at `p`
        let some litl2 ← litl.replaceAtPosUpdateType? ⟨s, p⟩ (mkConst ``False)
          | return none -- If `litl` can't be safely changed at position `p`, then don't apply `identBoolHoist` at `p`
        let c_erased := c.eraseLit l
        let nc := c_erased.appendLits #[litl1, Lit.fromSingleExpr e false]
        trace[duper.rule.identBoolHoist] s!"New Clause: {nc.lits.map Lit.toExpr}"
        let cp1 ← yieldClause nc "identity loobHoist" (some (mkBoolHoistProof pos true))
        let nc := c_erased.appendLits #[litl2, Lit.fromSingleExpr e true]
        trace[duper.rule.identBoolHoist] s!"New Clause: {nc.lits.map Lit.toExpr}"
        let cp2 ← yieldClause nc "identity boolHoist" (some (mkBoolHoistProof pos false))
        return some #[cp1, cp2]
    else
      return none

def identBoolHoist : MSimpRule := fun c => do
  let c ← loadClause c
  let fold_fn := fun acc e pos => do
    match acc with
    | some res => return some res
    | none => identBoolHoistAtExpr e pos c
  c.foldGreenM fold_fn none
