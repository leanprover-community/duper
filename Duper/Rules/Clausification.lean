import Duper.MClause
import Duper.RuleM
import Duper.Simp
import Duper.Util.ProofReconstruction
import Duper.Util.Misc

namespace Duper
open Lean
open RuleM
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

def clausificationStepE (e : Expr) (sign : Bool) : RuleM (Option (List (MClause × Option (Expr → MetaM Expr)))) := do
  match sign, e with
  | false, Expr.const ``True _ => do
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``true_neq_false #[premise]
    return some [(MClause.mk #[], some pr)]
  | true, Expr.const ``False _ => do
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``false_neq_true #[premise]
    return some [(MClause.mk #[], some pr)]
  | true, Expr.app (Expr.const ``Not _) e => do
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_not #[premise]
    return some [(MClause.mk #[Lit.fromSingleExpr e false], some pr)]
  | false, Expr.app (Expr.const ``Not _) e => 
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_not_false #[premise]
    return some [(MClause.mk #[Lit.fromSingleExpr e true], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``And _) e₁) e₂ => do
    let pr₁ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_left #[premise]
    let pr₂ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_right #[premise]
    /- e₂ and pr₂ are placed first in the list because "∧" is right-associative. So if we decompose "a ∧ b ∧ c ∧ d... = True" we want
       "b ∧ c ∧ d... = True" to be the first clause (which will return to Saturate's simpLoop to receive further clausification) -/
    return some [(MClause.mk #[Lit.fromSingleExpr e₂], some pr₂), (MClause.mk #[Lit.fromSingleExpr e₁], some pr₁)]
  | true, Expr.app (Expr.app (Expr.const ``Or _) e₁) e₂ =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or #[premise]
    return some [(MClause.mk #[Lit.fromSingleExpr e₁, Lit.fromSingleExpr e₂], some pr)]
  | true, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then
      if b.hasLooseBVars then
        throwError "Types depending on props are not supported" 
      let pr : Expr → MetaM Expr := fun premise => do
        return ← Meta.mkAppM ``clausify_imp #[premise]
      return some [(MClause.mk #[Lit.fromSingleExpr ty false, Lit.fromSingleExpr b], some pr)]
    else
      -- Hack. Add literal ((mvar ≠ mvar) = True) to the conclusion.
      --
      -- Here, we create a metavariable ```mvar``` to instantiate the
      -- quantifier. This metavariable is present in the result of this function
      -- and will escape into ```clausificationStep```, and be assigned
      -- by ```Meta.isDefEq (← Meta.inferType dproof) resRight'```
      -- in ```clausificationStep```. Normally the unification procedure will
      -- eliminate this metavariable. However, when the bound variable does not
      -- occur in the body ```b```, the unification
      --      ```if not (← Meta.isDefEq (← Meta.inferType dproof) resRight') then```
      -- will assign this metavariable
      -- with an expression which contains other metavariables, and these
      -- metavariables will escape from ```mkProof```, which causes the bug.
      --
      -- For example,
      -- ```example {a : Type} [Inhabited a] (h : ¬ (false = true)) :```
      -- ```  ¬(∀ a' : a, false) := by duper```
      -- will fail.
      --
      -- To solve this problem, we can add the literal ```((mvar ≠ mvar) = True)```
      -- to the conclusion.
      --
      -- This seems hacky, but I haven't thought of any other way
      -- which requires less code modification. Note that if the bound
      -- variable does not occur in the body and we don't add this
      -- dummy literal to the conclusion, then this metavariable
      -- will occur neither in the premise nor the conclusion, so
      -- there will be no way for ```yieldClause``` and ```mkProof```
      -- to discocver it.
      let pr : Expr → MetaM Expr := fun premise => do
        let premisety ← Meta.inferType premise
        let ty := (premisety.getArg! 1).bindingDomain!
        -- This `mvar` will be assigned by `isDefEq`
        let mvar ← Meta.mkFreshExprMVar ty
        let mvarNE ← Meta.mkAppM ``Ne #[mvar, mvar]
        let left_part_of_or ← Meta.mkAppM ``clausify_forall #[mvar, premise]
        return ← Meta.mkAppOptM ``Or.inl #[none, ← Meta.mkAppM ``Eq #[mvarNE, mkConst ``True], left_part_of_or]
      let mvar ← mkFreshExprMVar ty
      let mvarNE ← mkAppM ``Ne #[mvar, mvar]
      return some [(MClause.mk #[Lit.fromSingleExpr $ b.instantiate1 mvar, Lit.fromSingleExpr $ mvarNE], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``Exists _) ty) (Expr.lam _ _ b _) => do
    let skTerm ← makeSkTerm ty b
    let pr : Expr → MetaM Expr := fun premise => do
      let premisety ← Meta.inferType premise
      let ty := (premisety.getArg! 1).getArg! 0
      -- This `mvar` will be assigned by `isDefEq`
      let mvar ← Meta.mkFreshExprMVar  ty
      return ← Meta.mkAppM ``eq_true
        #[← Meta.mkAppM ``Skolem.spec #[mvar, ← Meta.mkAppM ``of_eq_true #[premise]]]
    return some [(MClause.mk #[Lit.fromSingleExpr $ b.instantiate1 skTerm], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``And _) e₁) e₂  => 
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_false #[premise]
    return some [(MClause.mk #[Lit.fromSingleExpr e₁ false, Lit.fromSingleExpr e₂ false], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``Or _) e₁) e₂ =>
    let pr₁ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or_false_left #[premise]
    let pr₂ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or_false_right #[premise]
    /- e₂ and pr₂ are placed first in the list because "∨" is right-associative. So if we decompose "a ∨ b ∨ c ∨ d... = False" we want
       "b ∨ c ∨ d... = False" to be the first clause (which will return to Saturate's simpLoop to receive further clausification) -/
    return some [(MClause.mk #[Lit.fromSingleExpr e₂ false], some pr₂), (MClause.mk #[Lit.fromSingleExpr e₁ false], some pr₁)]
  | false, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then
      -- TODO
      if b.hasLooseBVars then
        throwError "Types depending on props are not supported"
      let pr₁ : Expr → MetaM Expr := fun premise => do
        Meta.mkAppM ``clausify_imp_false_left #[premise]
      let pr₂ : Expr → MetaM Expr := fun premise => do
        Meta.mkAppM ``clausify_imp_false_right #[premise]
      return some [(MClause.mk #[Lit.fromSingleExpr ty], some pr₁),
               (MClause.mk #[Lit.fromSingleExpr b false], some pr₂)]
    else
      let skTerm ← makeSkTerm ty (mkNot b)
      let pr : Expr → MetaM Expr := fun premise => do
        let premisety ← Meta.inferType premise
        let ty := (premisety.getArg! 1).bindingDomain!
        -- This `mvar` will be assigned by `isDefEq`
        let mvar ← Meta.mkFreshExprMVar ty
        Meta.mkAppM ``eq_true
          #[← Meta.mkAppM ``Skolem.spec #[mvar, ← Meta.mkAppM ``exists_of_forall_eq_false #[premise]]]
      return some [(MClause.mk #[Lit.fromSingleExpr $ (mkNot b).instantiate1 skTerm], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``Exists _) ty) (Expr.lam _ _ b _) => do
    -- Hack. Add literal ((mvar ≠ mvar) = True). Similar to ```true, Expr.forallE```
    let pr : Expr → MetaM Expr := fun premise => do
      let premisety ← Meta.inferType premise
      let ty := (premisety.getArg! 1).getArg! 0
      let mvar ← Meta.mkFreshExprMVar ty
      let mvarNE ← Meta.mkAppM ``Ne #[mvar, mvar]
      let left_part_of_or ← Meta.mkAppM ``clausify_exists_false #[mvar, premise]
      return ← Meta.mkAppOptM ``Or.inl #[none, ← Meta.mkAppM ``Eq #[mvarNE, mkConst ``True], left_part_of_or]
    let mvar ← mkFreshExprMVar ty
    let mvarNE ← mkAppM ``Ne #[mvar, mvar]
    return some [(MClause.mk #[Lit.fromSingleExpr (b.instantiate1 mvar) false, Lit.fromSingleExpr $ mvarNE], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl]) ty) e₁) e₂  =>
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``of_eq_true #[premise]
    return some [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl]) ty) e₁) e₂  =>
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``not_of_eq_false #[premise] 
    return some [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl]) ty) e₁) e₂  =>
    let pr : Expr → MetaM Expr := fun premise => do
       Meta.mkAppM ``of_eq_true #[premise]
    return some [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl]) ty) e₁) e₂  =>
    --This case is saying if the clause is (e_1 ≠ e_2) = False, then we can turn that into e_1 = e_2
    let pr : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``of_not_eq_false #[premise]
    return some [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``Iff _) e₁) e₂ =>
    let pr1 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_iff1 #[premise]
    let pr2 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_iff2 #[premise]
    return some
      [(MClause.mk #[Lit.fromSingleExpr e₁ true, Lit.fromSingleExpr e₂ false], some pr1),
      (MClause.mk #[Lit.fromSingleExpr e₁ false, Lit.fromSingleExpr e₂ true], some pr2)]
  | false, Expr.app (Expr.app (Expr.const ``Iff _) e₁) e₂ =>
    let pr1 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_not_iff1 #[premise]
    let pr2 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_not_iff2 #[premise]
    return some
      [(MClause.mk #[Lit.fromSingleExpr e₁ false, Lit.fromSingleExpr e₂ false], some pr1),
      (MClause.mk #[Lit.fromSingleExpr e₁ true, Lit.fromSingleExpr e₂ true], some pr2)]
  | _, _ => 
    trace[Simp.debug] "### clausificationStepE is unapplicable with e = {e} and sign = {sign}"
    return none

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
  makeSkTerm ty b : RuleM Expr := do
    let p := mkLambda `x BinderInfo.default ty b
    let prf_pre ← mkAppM ``Skolem.some #[p]
    let abstres ← abstractMVarsLambdaWithIds prf_pre
    let prf := abstres.fst
    let skTy ← inferType prf
    let fvar ← mkFreshSkolem `sk skTy (fun parents => pure prf)
    let newmvar ← mkFreshExprMVar ty
    return mkApp (mkAppN fvar abstres.snd) newmvar

#check @Skolem.spec

def clausificationStepLit (c : MClause) (i : Nat) : RuleM (Option (List (MClause × Option (Expr → MetaM Expr)))) := do
  let l := c.lits[i]!
  if not l.ty.isProp then return none
  if l.sign then
    -- Clausify " = False" and "= True":
    match l.rhs with
    | Expr.const ``True _ => clausificationStepE l.lhs true
    | Expr.const ``False _ => clausificationStepE l.lhs false
    | _ =>
      -- Clausify "True = ..." and "False = ...":
      match l.lhs with
      | Expr.const ``True _ =>
        match ← clausificationStepE l.rhs true with
        | some clausifiedResList =>
          let map_fn : MClause × Option (Expr → MetaM Expr) → MClause × Option (Expr → MetaM Expr) :=
            fun clausifiedRes =>
              match clausifiedRes with
              | (c, none) => (c, none)
              | (c, some pr) => -- If pr is a proof that "A = B" implies c, then we want to return a proof that "B = A" implies c
                let symmProof : Expr → MetaM Expr := fun e => do pr (← Meta.mkAppM ``Eq.symm #[e])
                (c, some symmProof)
          return some (List.map map_fn clausifiedResList)
        | none => return none
      | Expr.const ``False _ =>
        match ← clausificationStepE l.rhs false with
        | some clausifiedResList =>
          let map_fn : MClause × Option (Expr → MetaM Expr) → MClause × Option (Expr → MetaM Expr) :=
            fun clausifiedRes =>
              match clausifiedRes with
              | (c, none) => (c, none)
              | (c, some pr) => -- If pr is a proof that "A = B" implies c, then we want to return a proof that "B = A" implies c
                let symmProof : Expr → MetaM Expr := fun e => do pr (← Meta.mkAppM ``Eq.symm #[e])
                (c, some symmProof)
          return some (List.map map_fn clausifiedResList)
        | none => return none
      | _ => return none
  else
    -- Clausify inequalities of type Prop:
    let pr1 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_prop_inequality1 #[premise]
    let pr2 : Expr → MetaM Expr := fun premise => do
      Meta.mkAppM ``clausify_prop_inequality2 #[premise]
    return some [(MClause.mk #[Lit.fromSingleExpr l.lhs false, Lit.fromSingleExpr l.rhs false], some pr1),
                    (MClause.mk #[Lit.fromSingleExpr l.lhs true, Lit.fromSingleExpr l.rhs true], some pr2)]
-- TODO: True/False on left-hand side?

-- TODO: generalize combination of `orCases` and `orIntro`?
def clausificationStep : MSimpRule := fun c => do
  let c ← loadClause c
  for i in [:c.lits.size] do
    match ← clausificationStepLit c i with
    | some ds =>
      for (d, dproof) in ds do
        let mkProof : ProofReconstructor := 
          fun (premises : List Expr) (parents : List ProofParent) (res : Clause) => do
            Meta.forallTelescope res.toForallExpr fun xs body => do
              let resLits := res.lits.map (fun l => Lit.map (fun e => e.instantiateRev xs) l)
              let (parentLits, appliedPremise) ← instantiatePremises parents premises xs
              let parentLits := parentLits[0]!
              let appliedPremise := appliedPremise[0]!
              
              let mut caseProofs := Array.mkEmpty parentLits.size
              for j in [:parentLits.size] do
                let lit := parentLits[j]!
                let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
                  if j == i then
                    let resLeft := resLits.toList.take (c.lits.size - 1)
                    let resRight := resLits.toList.drop (c.lits.size - 1)
                    let resRight' := (Clause.mk #[] resRight.toArray).toForallExpr
                    let resLits' := (resLeft.map Lit.toExpr).toArray.push resRight'
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
        yieldClause ⟨c.lits.eraseIdx i ++ d.lits⟩ "clausification" mkProof
      return true
    | none => continue
  return false

end Duper
