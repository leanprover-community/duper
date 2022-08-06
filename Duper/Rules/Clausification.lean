import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Lean
open RuleM
open SimpResult

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
theorem clausify_imp (h : (p → q) = True) : (¬ p) = True ∨ q = True := 
  (Classical.em q).elim 
    (fun hq => Or.intro_right _ (eq_true hq)) 
    (fun hq => Or.intro_left _ (eq_true (fun hp => hq ((of_eq_true h) hp))))

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
noncomputable def Inhabited.some [Inhabited α] (p : α → Prop) :=
  let _ : Decidable (∃ a, p a) := Classical.propDecidable _
  if hp: ∃ a, p a then Classical.choose hp else Inhabited.default

--TODO: move
theorem Inhabited.some_spec [Inhabited α] {p : α → Prop} (hp : ∃ a, p a) : 
  p (Inhabited.some p) := by
  simp only [Inhabited.some, hp]
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

theorem clausify_not_iff (h : (p ↔ q) = False) : p ≠ q := by
  intro p_eq_q
  rw [← h, p_eq_q]
  exact Iff.rfl

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

-- TODO: Clausify ↔ as =
def clausificationStepE (e : Expr) (sign : Bool) (c : MClause) (i : Nat) : 
    RuleM (SimpResult (List (MClause × Option (Expr → MetaM Expr)))) := do
  match sign, e with
  | false, Expr.const ``True _ _ => do
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``true_neq_false #[premise]
    return Applied [(MClause.mk #[], some pr)]
  | true, Expr.const ``False _ _ => do
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``false_neq_true #[premise]
    return Applied [(MClause.mk #[], some pr)]
  | true, Expr.app (Expr.const ``Not _ _) e _ => do
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_not #[premise]
    return Applied [(MClause.mk #[Lit.fromExpr e false], some pr)]
  | false, Expr.app (Expr.const ``Not _ _) e _ => 
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_not_false #[premise]
    return Applied [(MClause.mk #[Lit.fromExpr e true], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _ => do
    let pr₁ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_left #[premise]
    let pr₂ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_right #[premise]
    return Applied [(MClause.mk #[Lit.fromExpr e₁], some pr₁), (MClause.mk #[Lit.fromExpr e₂], some pr₂)]
  | true, Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or #[premise]
    return Applied [(MClause.mk #[Lit.fromExpr e₁, Lit.fromExpr e₂], some pr)]
  | true, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then
      if b.hasLooseBVars then
        throwError "Types depending on props are not supported" 
      let pr : Expr → MetaM Expr := fun premise => do
        return ← Meta.mkAppM ``clausify_imp #[premise]
      return Applied [(MClause.mk #[Lit.fromExpr (mkNot ty), Lit.fromExpr b], some pr)]
    else 
      let mvar ← mkFreshExprMVar ty
      let pr : Expr → MetaM Expr := fun premise => do
        let mvar ← Meta.mkFreshExprMVar ty
        return ← Meta.mkAppM ``clausify_forall #[mvar, premise]
      return Applied [(MClause.mk #[Lit.fromExpr $ b.instantiate1 mvar], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``Exists _ _) ty _) (Expr.lam _ _ b _) _ => do
    let skTerm ← makeSkTerm ty b
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``eq_true
        #[← Meta.mkAppM ``Inhabited.some_spec #[← Meta.mkAppM ``of_eq_true #[premise]]]
    return Applied [(MClause.mk #[Lit.fromExpr $ b.instantiate1 skTerm], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _  => 
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_false #[premise]
    return Applied [(MClause.mk #[Lit.fromExpr e₁ false, Lit.fromExpr e₂ false], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    let pr₁ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or_false_left #[premise]
    let pr₂ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or_false_right #[premise]
    return  Applied [(MClause.mk #[Lit.fromExpr e₁ false], some pr₁), 
             (MClause.mk #[Lit.fromExpr e₂ false], some pr₂)]
  | false, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then 
      if b.hasLooseBVars then
        throwError "Types depending on props are not supported"
      let pr₁ : Expr → MetaM Expr := fun premise => do
        Meta.mkAppM ``clausify_imp_false_left #[premise]
      let pr₂ : Expr → MetaM Expr := fun premise => do
        Meta.mkAppM ``clausify_imp_false_right #[premise]
      return Applied [(MClause.mk #[Lit.fromExpr ty], some pr₁),
               (MClause.mk #[Lit.fromExpr b false], some pr₂)]
    else
      let skTerm ← makeSkTerm ty (mkNot b)
      let pr : Expr → MetaM Expr := fun premise => do
        Meta.mkAppM ``eq_true
          #[← Meta.mkAppM ``Inhabited.some_spec #[← Meta.mkAppM ``exists_of_forall_eq_false #[premise]]]
      return Applied [(MClause.mk #[Lit.fromExpr $ (mkNot b).instantiate1 skTerm], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``Exists _ _) ty _) (Expr.lam _ _ b _) _ => do
    let mvar ← mkFreshExprMVar ty
    let pr : Expr → MetaM Expr := fun premise => do
      let mvar ← Meta.mkFreshExprMVar ty
      Meta.mkAppM ``clausify_exists_false #[mvar, premise]
    return Applied [(MClause.mk #[Lit.fromExpr (b.instantiate1 mvar) false], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``of_eq_true #[premise]
    return Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``not_of_eq_false #[premise] 
    return Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
       Meta.mkAppM ``of_eq_true #[premise]
    return Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    --This case is saying if the clause is (e_1 ≠ e_2) = False, then we can turn that into e_1 = e_2
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``of_not_eq_false #[premise]
    return Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``Iff _ _) e₁ _) e₂ _ =>
    --This case is saying if the clause is (e_1 ↔ e_2) = True, then we can turn that into e_1 = e_2
    trace[Simp.debug] "### clausificationStepE first new case called"
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_iff #[premise]
    -- I believe lvl should be levelOne and ty should be mkSort levelZero because Iff produces an expression of type Prop
    return Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := levelOne, ty := mkSort levelZero}], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``Iff _ _) e₁ _) e₂ _  =>
    --This case is saying if the clause is (e_1 ↔ e_2) = False, then we can turn that into e_1 ≠ e_2
    trace[Simp.debug] "### clausificationStepE second new case called"
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_not_iff #[premise]
    -- I believe lvl should be levelOne and ty should be mkSort levelZero because Iff produces an expression of type Prop
    return Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := levelOne, ty := mkSort levelZero}], some pr)]
  | _, _ => 
    trace[Simp.debug] "### clausificationStepE returned Unapplicable with e = {e} and sign = {sign}"
    return Unapplicable

where
  makeSkTerm ty b : RuleM Expr := do
    let mVarIds := (e.collectMVars {}).result
    let skTy := ty.abstractMVars (mVarIds.map mkMVar)
    let mVarIdTys ← (mVarIds.mapM (fun mvarId => do inferType (mkMVar mvarId)))
    let skTy := mVarIdTys.foldr
      (fun mVarIdTy skTy => mkForall `_ BinderInfo.default mVarIdTy skTy)
      skTy
    let mkProof := fun parents => do
      let d ← Meta.mkAppM ``Inhabited.some #[mkLambda `x BinderInfo.default ty b]
      return d
    let fvar ← mkFreshSkolem `sk skTy mkProof
    return mkAppN fvar (mVarIds.map mkMVar)

def clausificationStepLit (c : MClause) (i : Nat) : RuleM (SimpResult (List (MClause × Option (Expr → MetaM Expr)))) := do
  let l := c.lits[i]
  if not l.ty.isProp then return Unapplicable
  if l.sign then
    -- Clausify " = False" and "= True":
    match l.rhs with
    | Expr.const ``True _ _ => clausificationStepE l.lhs true c i
    | Expr.const ``False _ _ => clausificationStepE l.lhs false c i
    | _ => return Unapplicable
  else
    -- Clausify inequalities of type Prop:
    let pr1 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_prop_inequality1 #[premise]
    let pr2 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_prop_inequality2 #[premise]
    return Applied [(MClause.mk #[Lit.fromExpr l.lhs false, Lit.fromExpr l.rhs false], some pr1),
                    (MClause.mk #[Lit.fromExpr l.lhs true, Lit.fromExpr l.rhs true], some pr2)]
-- TODO: True/False on left-hand side?

-- TODO: generalize combination of `orCases` and `orIntro`?
def clausificationStep : MSimpRule := fun c => do
  for i in [:c.lits.size] do
    match ← clausificationStepLit c i with
    | Applied ds =>
      return Applied $ ds.map fun (d, dproof) => 
        let mkProof : ProofReconstructor := 
          fun (premises : Array Expr) (parents: Array ProofParent) (res : Clause) => do
            Meta.forallTelescope res.toForallExpr fun xs body => do
              let resLits := res.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
              let (parentLits, appliedPremise) ← instantiatePremises parents premises xs
              let parentLits := parentLits[0]
              let appliedPremise := appliedPremise[0]
              
              let mut caseProofs := #[]
              for j in [:parentLits.size] do
                let lit := parentLits[j]
                let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
                  if j == i then
                    let resLeft := resLits.toList.take (c.lits.size - 1)
                    let resRight := resLits.toList.drop (c.lits.size - 1)
                    let resRight' := (Clause.mk #[] resRight.toArray).toForallExpr
                    let resLits' := (resLeft.map Lit.toExpr).toArray.push resRight'
                    -- TODO: use dproof and h
                    let dproof ← match dproof with
                    | none => Meta.mkSorry resRight' true
                    | some dproof => dproof h
                    if not (← Meta.isDefEq (← Meta.inferType dproof) resRight') then
                      throwError "Error when reconstructing clausification. Expected type: {resRight'}, but got: {dproof}"
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
        (⟨c.lits.eraseIdx i ++ d.lits⟩, mkProof)
    | Removed => 
      return Removed
    | Unapplicable => 
      continue
  return Unapplicable

end Duper
