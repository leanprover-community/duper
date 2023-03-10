import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction
import Duper.Util.Misc
import Duper.Util.AbstractMVars

namespace Duper
open Lean
open RuleM
open Meta
open SimpResult

initialize Lean.registerTraceClass `Rule.clausification

--TODO: move?
theorem not_of_eq_false (h: p = False) : ¬ p := 
  fun hp => h ▸ hp

--TODO: move?
theorem of_not_eq_false (h: (¬ p) = False) : p := 
  Classical.byContradiction fun hn => h ▸ hn

--TODO: move?
theorem eq_true_of_not_eq_false (h : (¬ p) = False) : p = True := 
  eq_true (of_not_eq_false h)

--TODO: move?
theorem eq_false_of_not_eq_true (h : (¬ p) = True) : p = False := 
  eq_false (of_eq_true h)

--TODO: move?
theorem clausify_and_left (h : (p ∧ q) = True) : p = True := 
  eq_true (of_eq_true h).left

--TODO: move?
theorem clausify_and_right (h : (p ∧ q) = True) : q = True := 
  eq_true (of_eq_true h).right

--TODO: move?
theorem clausify_and_false (h : (p ∧ q) = False) : p = False ∨ q = False := by
  apply @Classical.byCases p
  · intro hp 
    apply @Classical.byCases q
    · intro hq
      exact False.elim $ not_of_eq_false h ⟨hp, hq⟩
    · intro hq
      exact Or.intro_right _ (eq_false hq)
  · intro hp
    exact Or.intro_left _ (eq_false hp)

--TODO: move?
theorem clausify_or (h : (p ∨ q) = True) : p = True ∨ q = True := 
  (of_eq_true h).elim 
    (fun h => Or.intro_left _ (eq_true h))
    (fun h => Or.intro_right _ (eq_true h))

--TODO: move?
theorem clausify_or_false_left (h : (p ∨ q) = False) : p = False := 
  eq_false fun hp => not_of_eq_false h (Or.intro_left _ hp)

--TODO: move?
theorem clausify_or_false_right (h : (p ∨ q) = False) : q = False := 
  eq_false fun hp => not_of_eq_false h (Or.intro_right _ hp)

--TODO: move?
theorem clausify_not (h : (¬ p) = True) : p = False := 
eq_false fun hp => of_eq_true h hp

--TODO: move?
theorem clausify_not_false (h : (¬ p) = False) : p = True := 
eq_true (Classical.byContradiction fun hp => not_of_eq_false h hp)

--TODO: move?
theorem clausify_imp (h : (p → q) = True) : p = False ∨ q = True := by
  cases Classical.propComplete q with
  | inl q_eq_true => exact Or.intro_right _ q_eq_true
  | inr q_eq_false =>
    cases Classical.propComplete p with
    | inl p_eq_true =>
      rw [p_eq_true, q_eq_false] at h
      have t : True := ⟨⟩
      rw [← h] at t
      exact False.elim (t ⟨⟩)
    | inr p_eq_false => exact Or.intro_left _ p_eq_false

--TODO: move?
theorem clausify_imp_false_left (h : (p → q) = False) : p = True := 
  Classical.byContradiction fun hnp => 
    not_of_eq_false h fun hp => 
      False.elim (hnp $ eq_true hp)

--TODO: move?
theorem clausify_imp_false_right (h : (p → q) = False) : q = False := 
  eq_false fun hq => not_of_eq_false h fun _ => hq

--TODO: move?
theorem clausify_forall {p : α → Prop} (x : α) (h : (∀ x, p x) = True) : p x = True := 
  eq_true (of_eq_true h x)

--TODO: move?
theorem clausify_exists {p : α → Prop} (h : (∃ x, p x) = True) :
  p (Classical.choose (of_eq_true h)) = True := 
eq_true $ Classical.choose_spec _

--TODO: move?
theorem clausify_exists_false {p : α → Prop} (x : α) (h : (∃ x, p x) = False) : p x = False := 
  eq_false (fun hp => not_of_eq_false h ⟨x, hp⟩)

--TODO: move
noncomputable def Skolem.some (p : α → Prop) (x : α) :=
  let _ : Decidable (∃ a, p a) := Classical.propDecidable _
  if hp: ∃ a, p a then Classical.choose hp else x

--TODO: move
theorem Skolem.spec {p : α → Prop} (x : α) (hp : ∃ a, p a) : 
  p (Skolem.some p x) := by
  simp only [Skolem.some, hp]
  exact Classical.choose_spec _

theorem exists_of_forall_eq_false {p : α → Prop} (h : (∀ x, p x) = False) : ∃ x, ¬ p x := by
  apply Classical.byContradiction
  intro hnex
  apply not_of_eq_false h
  intro x
  apply Classical.byContradiction
  intro hp
  apply hnex
  exact Exists.intro x hp

theorem false_neq_true : False ≠ True := fun h => of_eq_true h

theorem true_neq_false : True ≠ False := fun h => of_eq_true h.symm

theorem clausify_iff (h : (p ↔ q) = True) : p = q := by
  apply propext
  rw [h]
  exact True.intro

theorem clausify_iff1 (h : (p ↔ q) = True) : p = True ∨ q = False := by
  cases Classical.propComplete p with
  | inl p_eq_true => exact Or.inl p_eq_true
  | inr p_eq_false =>
    rw [← clausify_iff h]
    exact Or.inr p_eq_false

theorem clausify_iff2 (h : (p ↔ q) = True) : p = False ∨ q = True := by
  cases Classical.propComplete p with
  | inl p_eq_true =>
    rw [← clausify_iff h]
    exact Or.inr p_eq_true
  | inr p_eq_false => exact Or.inl p_eq_false

theorem clausify_not_iff (h : (p ↔ q) = False) : p ≠ q := by
  intro p_eq_q
  rw [← h, p_eq_q]

theorem clausify_not_iff1 (h : (p ↔ q) = False) : p = False ∨ q = False := by
  cases Classical.propComplete p with
  | inl p_eq_true =>
    cases Classical.propComplete q with
    | inl q_eq_true =>
      rw [p_eq_true, q_eq_true] at h
      exact False.elim $ (clausify_not_iff h) rfl
    | inr q_eq_false => exact Or.intro_right _ q_eq_false
  | inr p_eq_false => exact Or.intro_left _ p_eq_false

theorem clausify_not_iff2 (h : (p ↔ q) = False) : p = True ∨ q = True := by
  cases Classical.propComplete p with
  | inl p_eq_true => exact Or.intro_left _ p_eq_true
  | inr p_eq_false =>
    cases Classical.propComplete q with
    | inl q_eq_true => exact Or.intro_right _ q_eq_true
    | inr q_eq_false =>
      rw [p_eq_false, q_eq_false] at h
      exact False.elim $ (clausify_not_iff h) rfl

theorem clausify_prop_inequality1 {p : Prop} {q : Prop} (h : p ≠ q) : p = False ∨ q = False := by
  cases Classical.propComplete p with
  | inl p_eq_true =>
    cases Classical.propComplete q with
    | inl q_eq_true =>
      rw [p_eq_true, q_eq_true] at h
      exact False.elim $ h rfl
    | inr q_eq_false => exact Or.intro_right _ q_eq_false
  | inr p_eq_false => exact Or.intro_left _ p_eq_false

theorem clausify_prop_inequality2 {p : Prop} {q : Prop} (h : p ≠ q) : p = True ∨ q = True := by
  cases Classical.propComplete p with
  | inl p_eq_true => exact Or.intro_left _ p_eq_true
  | inr p_eq_false =>
    cases Classical.propComplete q with
    | inl q_eq_true => exact Or.intro_right _ q_eq_true
    | inr q_eq_false =>
      rw [p_eq_false, q_eq_false] at h
      exact False.elim $ h rfl

structure ClausificationResult where
  resultLits        : Array Lit
  -- The `Array Expr` is the `freshVars`
  proof             : Expr → Array Expr → MetaM Expr
  transferExprs     : Array Expr

def clausificationStepE (e : Expr) (sign : Bool) : RuleM (Array ClausificationResult) :=
  match sign, e with
  | false, Expr.const ``True _ =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``true_neq_false #[premise]
    return #[⟨#[], pr, #[]⟩]
  | true, Expr.const ``False _ =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``false_neq_true #[premise]
    return #[⟨#[], pr, #[]⟩]
  | true, Expr.app (Expr.const ``Not _) e =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_not #[premise]
    return #[⟨#[Lit.fromSingleExpr e false], pr, #[]⟩]
  | false, Expr.app (Expr.const ``Not _) e => 
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_not_false #[premise]
    return #[⟨#[Lit.fromSingleExpr e true], pr, #[]⟩]
  | true, Expr.app (Expr.app (Expr.const ``And _) e₁) e₂ =>
    let pr₁ : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_and_left #[premise]
    let pr₂ : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_and_right #[premise]
    /- e₂ and pr₂ are placed first in the list because "∧" is right-associative. So if we decompose "a ∧ b ∧ c ∧ d... = True" we want
       "b ∧ c ∧ d... = True" to be the first clause (which will return to Saturate's simpLoop to receive further clausification) -/
    return #[⟨#[Lit.fromSingleExpr e₂], pr₂, #[]⟩, ⟨#[Lit.fromSingleExpr e₁], pr₁, #[]⟩]
  | true, Expr.app (Expr.app (Expr.const ``Or _) e₁) e₂ =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_or #[premise]
    return #[⟨#[Lit.fromSingleExpr e₁, Lit.fromSingleExpr e₂], pr, #[]⟩]
  | true, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp && !b.hasLooseBVars then
      let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_imp #[premise]
      return #[⟨#[Lit.fromSingleExpr ty false, Lit.fromSingleExpr b], pr, #[]⟩]
    else
      let pr : Expr → Array Expr → MetaM Expr := fun premise trs => do
        let #[tr] := trs
          | throwError "clausificationStepE :: Wrong number of transferExprs"
        Meta.mkAppM ``clausify_forall #[tr, premise]
      let mvar ← mkFreshExprMVar ty
      return #[⟨#[Lit.fromSingleExpr $ b.instantiate1 mvar], pr, #[mvar]⟩]
  | true, Expr.app (Expr.app (Expr.const ``Exists _) ty) (Expr.lam _ _ b _) => do
    let (skTerm, newmvar) ← makeSkTerm ty b
    let pr : Expr → Array Expr → MetaM Expr := fun premise trs => do
      let #[tr] := trs
          | throwError "clausificationStepE :: Wrong number of transferExprs"
      return ← Meta.mkAppM ``eq_true
        #[← Meta.mkAppM ``Skolem.spec #[tr, ← Meta.mkAppM ``of_eq_true #[premise]]]
    return #[⟨#[Lit.fromSingleExpr $ b.instantiate1 skTerm], pr, #[newmvar]⟩]
  | false, Expr.app (Expr.app (Expr.const ``And _) e₁) e₂  => 
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_and_false #[premise]
    return #[⟨#[Lit.fromSingleExpr e₁ false, Lit.fromSingleExpr e₂ false], pr, #[]⟩]
  | false, Expr.app (Expr.app (Expr.const ``Or _) e₁) e₂ =>
    let pr₁ : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_or_false_left #[premise]
    let pr₂ : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_or_false_right #[premise]
    /- e₂ and pr₂ are placed first in the list because "∨" is right-associative. So if we decompose "a ∨ b ∨ c ∨ d... = False" we want
       "b ∨ c ∨ d... = False" to be the first clause (which will return to Saturate's simpLoop to receive further clausification) -/
    return #[⟨#[Lit.fromSingleExpr e₂ false], pr₂, #[]⟩, ⟨#[Lit.fromSingleExpr e₁ false], pr₁, #[]⟩]
  | false, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp && !b.hasLooseBVars then
      let pr₁ : Expr → Array Expr → MetaM Expr := fun premise _ =>
        Meta.mkAppM ``clausify_imp_false_left #[premise]
      let pr₂ : Expr → Array Expr → MetaM Expr := fun premise _ =>
        Meta.mkAppM ``clausify_imp_false_right #[premise]
      return #[⟨#[Lit.fromSingleExpr ty], pr₁, #[]⟩, ⟨#[Lit.fromSingleExpr b false], pr₂, #[]⟩]
    else
      let (skTerm, newmvar) ← makeSkTerm ty (mkNot b)
      let pr : Expr → Array Expr → MetaM Expr := fun premise trs => do
        let #[tr] := trs
          | throwError "clausificationStepE :: Wrong number of transferExprs"
        Meta.mkAppM ``eq_true #[← Meta.mkAppM ``Skolem.spec #[tr, ← Meta.mkAppM ``exists_of_forall_eq_false #[premise]]]
      return #[⟨#[Lit.fromSingleExpr $ (mkNot b).instantiate1 skTerm], pr, #[newmvar]⟩]
  | false, Expr.app (Expr.app (Expr.const ``Exists _) ty) (Expr.lam _ _ b _) => do
    let pr : Expr → Array Expr → MetaM Expr := fun premise trs => do
      let #[tr] := trs
        | throwError "clausificationStepE :: Wrong number of transferExprs"
      Meta.mkAppM ``clausify_exists_false #[tr, premise]
    let mvar ← mkFreshExprMVar ty
    return #[⟨#[Lit.fromSingleExpr (b.instantiate1 mvar) false], pr, #[mvar]⟩]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl]) ty) e₁) e₂  =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``of_eq_true #[premise]
    return #[⟨#[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], pr, #[]⟩]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl]) ty) e₁) e₂  =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``not_of_eq_false #[premise] 
    return #[⟨#[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], pr, #[]⟩]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl]) ty) e₁) e₂  =>
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``of_eq_true #[premise]
    return #[⟨#[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], pr, #[]⟩]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl]) ty) e₁) e₂  =>
    --This case is saying if the clause is (e_1 ≠ e_2) = False, then we can turn that into e_1 = e_2
    let pr : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``of_not_eq_false #[premise]
    return #[⟨#[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], pr, #[]⟩]
  | true, Expr.app (Expr.app (Expr.const ``Iff _) e₁) e₂ =>
    let pr1 : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_iff1 #[premise]
    let pr2 : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_iff2 #[premise]
    return #[
        ⟨#[Lit.fromSingleExpr e₁ true, Lit.fromSingleExpr e₂ false], pr1, #[]⟩,
        ⟨#[Lit.fromSingleExpr e₁ false, Lit.fromSingleExpr e₂ true], pr2, #[]⟩
      ]
  | false, Expr.app (Expr.app (Expr.const ``Iff _) e₁) e₂ =>
    let pr1 : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_not_iff1 #[premise]
    let pr2 : Expr → Array Expr → MetaM Expr := fun premise _ => Meta.mkAppM ``clausify_not_iff2 #[premise]
    return #[
        ⟨#[Lit.fromSingleExpr e₁ false, Lit.fromSingleExpr e₂ false], pr1, #[]⟩,
        ⟨#[Lit.fromSingleExpr e₁ true, Lit.fromSingleExpr e₂ true], pr2, #[]⟩
      ]
  | _, _ => do
    trace[Simp.debug] "### clausificationStepE is unapplicable with e = {e} and sign = {sign}"
    return #[]
where
  -- h : (∃ x : ty, p x)
  -- sk : (∃ x : ty, p x) → ty
  --     No! May contain metavariables
  -- sk : ∀ [metavars], ty → ty :=
  --   fun [metavars] => Skolem.some (fun x : ty => p x)
  -- sk_spec : ∀ [metavars] (x : ty), (∃ x : ty, p x) → p (sk [metavars] x) :=
  --   fun [metavars] (x : ty) (h : ∃ x, p x) => Skolem.spec x h
  -- We don't need to construct `sk_spec` explicitly. We
  --   can directly use `Skolem.spec` and leave the job of unification
  --   to Lean
  -- Note: Proof reconstruction of skolems is independent of proof reconstruction of clauses.
  makeSkTerm ty b : RuleM (Expr × Expr) := do
    let skMap ← getSkolemMap
    let cnt := skMap.size
    let p := mkLambda `x BinderInfo.default ty b
    let prf_pre ← mkAppM ``Skolem.some #[p]
    let (prf, mids, lnames, lvls) ← Duper.abstractMVarsLambdaWithIds prf_pre
    let isk : SkolemInfo := {expr := prf, params := lnames}
    setSkolemMap (skMap.insert cnt isk)
    let skTy ← inferType prf
    let skLvl := (← inferType skTy).sortLevel!
    let skolemSorryName ← getSkolemSorryName
    let wrapped ← wrapSortIntoOpaqueNat lnames
    let skExpr := Expr.app (.app (.app (.const skolemSorryName [skLvl]) wrapped) (.lit (.natVal cnt))) skTy
    let skExpr := skExpr.instantiateLevelParamsArray lnames lvls
    let newmvar ← mkFreshExprMVar ty
    return (mkApp (mkAppN skExpr mids) newmvar, newmvar)

-- Important: We return `Array ClausificationResult` instead of
--   `Option (Array ClausificationResult)` because whenever a literal
--   can be clausified, the result is always a non-empty list.
-- So, to check whether clausification succeeded, we only need
--   to check whether the returned list is empty.
def clausificationStepLit (c : MClause) (i : Nat) : RuleM (Array ClausificationResult) := do
  let l := c.lits[i]!
  if not l.ty.isProp then return #[]
  if l.sign then
    -- Clausify " = False" and "= True":
    match l.rhs with
    | Expr.const ``True _ => clausificationStepE l.lhs true
    | Expr.const ``False _ => clausificationStepE l.lhs false
    | _ =>
      -- Clausify "True = ..." and "False = ...":
      match l.lhs with
      | Expr.const ``True _ =>
        let clausifiedResList ← clausificationStepE l.rhs true
        let map_fn : ClausificationResult → ClausificationResult :=
          fun ⟨c, pr, tr⟩ => -- If pr is a proof that "A = B" implies c, then we want to return a proof that "B = A" implies c
              let symmProof : Expr → Array Expr → MetaM Expr := fun e fsf => do pr (← Meta.mkAppM ``Eq.symm #[e]) fsf
              ⟨c, symmProof, tr⟩
        return clausifiedResList.map map_fn 
      | Expr.const ``False _ =>
        let clausifiedResList ← clausificationStepE l.rhs false
        let map_fn : ClausificationResult → ClausificationResult :=
          fun ⟨c, pr, tr⟩ => -- If pr is a proof that "A = B" implies c, then we want to return a proof that "B = A" implies c
              let symmProof : Expr → Array Expr → MetaM Expr := fun e fsf => do pr (← Meta.mkAppM ``Eq.symm #[e]) fsf
              ⟨c, symmProof, tr⟩
        return clausifiedResList.map map_fn
      | _ => return #[]
  else
    -- Clausify inequalities of type Prop:
    let pr1 : Expr → Array Expr → MetaM Expr := fun premise _ => do
      Meta.mkAppM ``clausify_prop_inequality1 #[premise]
    let pr2 : Expr → Array Expr → MetaM Expr := fun premise _ => do
      Meta.mkAppM ``clausify_prop_inequality2 #[premise]
    return #[⟨#[Lit.fromSingleExpr l.lhs false, Lit.fromSingleExpr l.rhs false], pr1, #[]⟩,
             ⟨#[Lit.fromSingleExpr l.lhs true, Lit.fromSingleExpr l.rhs true], pr2, #[]⟩]

-- TODO: generalize combination of `orCases` and `orIntro`?
def clausificationStep : MSimpRule := fun c => do
  let c ← loadClause c
  for i in [:c.lits.size] do
    let ds ← clausificationStepLit c i 
    if ds.isEmpty then
      continue
    let mut resultClauses := #[]
    for ⟨d, dproof, tr⟩ in ds do
      let mkProof : ProofReconstructor := 
        fun (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr) (res : Clause) => do
          Meta.forallTelescope res.toForallExpr fun xs body => do
            let resLits := res.lits.map (fun l => Lit.map (fun e => e.instantiateRev xs) l)
            let (parentLits, appliedPremise, transferExprs) ← instantiatePremises parents premises xs transferExprs
            let parentLits := parentLits[0]!
            let appliedPremise := appliedPremise[0]!
            
            let mut caseProofs := Array.mkEmpty parentLits.size
            for j in [:parentLits.size] do
              let lit := parentLits[j]!
              let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
                if j == i then
                  let resLeft := resLits.toList.take (c.lits.size - 1)
                  let resRight := resLits.toList.drop (c.lits.size - 1)
                  -- Temporaryly use `Clause` to construct the expected type
                  -- So we don't need to supply universe parameters
                  let resRight' := (Clause.mk #[] #[] resRight.toArray).toForallExpr
                  let resLits' := (resLeft.map Lit.toExpr).toArray.push resRight'
                  let dproof ← dproof h transferExprs
                  if resRight.length == 0 then
                    Meta.mkLambdaFVars #[h] $ ← Meta.mkAppOptM ``False.elim #[body, dproof]
                  else
                    Meta.mkLambdaFVars #[h] $ ← orIntro resLits' (c.lits.size - 1) dproof
                else
                  let idx := if j ≥ i then j - 1 else j
                  Meta.mkLambdaFVars #[h] $ ← orIntro (resLits.map Lit.toExpr) idx h
              caseProofs := caseProofs.push $ pr

            let r ← orCases (parentLits.map Lit.toExpr) caseProofs
            let r ← Meta.mkLambdaFVars xs $ mkApp r appliedPremise
            return r
      let newClause := ⟨c.lits.eraseIdx i ++ d, c.mvars ++ tr⟩
      trace[Rule.clausification] "Yielding newClause: {newClause.lits} with mvars: {newClause.mvars}"
      let newResult ← yieldClause newClause "clausification" mkProof tr
      resultClauses := resultClauses.push newResult
    return some resultClauses
  return none

end Duper
