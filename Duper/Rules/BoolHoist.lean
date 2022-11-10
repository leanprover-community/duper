import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction

-- BoolHoist          LoobHoist
--             C<u>
-- -----------------------------
-- C<⊤> ∨ u = ⊥     C<⊥> ∨ u = ⊤
--
-- where u is of type Prop, but neither ⊥ nor ⊤, and u is not at the top level of a positive literal.

namespace Duper
open Lean
open RuleM
open SimpResult

initialize Lean.registerTraceClass `Rule.BoolHoist

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

def mkBoolHoistProof (pos : ClausePos) (sgn : Bool) (premises : List Expr)
  (parents : List ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let ⟨i, s, p⟩ := pos

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        let lp : LitPos := ⟨s, p⟩
        let f ← Meta.withLocalDeclD `h (.sort .zero) fun h => do
          let lit' ← lit.replaceAtPos! lp h
          let f := lit'.toExpr
          Meta.mkLambdaFVars #[h] f
        let e := lit.getAtPos! lp
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let mut pr := h
          if sgn then
            pr ← Meta.mkAppM ``bool_hoist_proof #[f, e, h]
          else
            pr ← Meta.mkAppM ``loob_hoist_proof #[f, e, h]
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

def boolHoistAtExpr (e : Expr) (pos : ClausePos) (c : MClause) : RuleM Bool :=
  withoutModifyingMCtx do
    let ty ← inferType e
    if ← unify #[(ty, .sort .zero)] then
      let ⟨l, s, p⟩ := pos
      let is_true ← withNewMCtxDepth (isDefEq e (mkConst ``True))
      let is_false ← withNewMCtxDepth (isDefEq e (mkConst ``False))
      trace[Rule.BoolHoist] m!"Inspecting position {pos} in clause {c.lits.map Lit.toExpr}"
      if is_true ∨ is_false ∨ p.size = 0 then
        return false
      else
        trace[Rule.BoolHoist] m!"BoolHoist at literal {l}, side {s}, position {p} in clause {c.lits.map Lit.toExpr}"
        let litl := c.lits[l]!
        let c_erased := c.eraseLit l
        let nc := c_erased.appendLits
          #[← litl.replaceAtPos! ⟨s, p⟩ (mkConst ``True), Lit.fromExpr e false]
        trace[Rule.BoolHoist] s!"New Clause: {nc.lits.map Lit.toExpr}"
        yieldClause nc "boolean hoist C<u> → C<⊤>"
          (some (mkBoolHoistProof pos true))
        let nc := c_erased.appendLits
          #[← litl.replaceAtPos! ⟨s, p⟩ (mkConst ``False), Lit.fromExpr e true]
        trace[Rule.BoolHoist] s!"New Clause: {nc.lits.map Lit.toExpr}"
        yieldClause nc "boolean hoist C<u> → C<⊥>"
          (some (mkBoolHoistProof pos false))
        return true
    else
      return false

def boolHoist : MSimpRule := fun c => do
  let c ← loadClause c
  let fold_fn := fun acc e pos => do
    match acc with
    | false => boolHoistAtExpr e pos c
    | true => return true
  c.foldGreenM fold_fn false