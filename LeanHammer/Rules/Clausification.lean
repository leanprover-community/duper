import LeanHammer.MClause
import LeanHammer.RuleM
import LeanHammer.Simp
import LeanHammer.Util.ProofReconstruction

namespace Schroedinger
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

theorem ex_eq_true_of_ex_eq_true {p : α → Prop} (h : (∃ x, p x) = True) : ∃ x, (p x = True) :=
  (of_eq_true h).elim fun a ha => ⟨a, eq_true ha⟩

-- theorem xxx {p : α → Prop} (h : (∃ x, p x) = True ∨ q) : ∃ x, (p x = True) :=
--   (of_eq_true h).elim fun a ha => ⟨a, eq_true ha⟩

--TODO: generalize `orIntro` + `orCases` & use everywhere
/-- Construct a proof of 
 `∃ a, lits[0] ∨ ... ∨ lits[i-1] ∨ lits[i+1] ∨ ... ∨ lits[n] ∨ p a = True` 
 from a proof of
`lits[0] ∨ ... ∨ (∃ a, p a) = True ∨ ... ∨ lits[n]`-/
def existsClause (lits : Array Expr) (i : Nat) (p : Expr) (ty : Expr) (pr : Expr) : MetaM Expr := do
  Meta.withLocalDeclD `a ty fun a => do
    let mut resLits := #[]
    for j in [:lits.size] do
      if j != i then
        resLits := resLits.push lits[j]
    resLits := resLits.push $ p.instantiate1 a

    let mut caseProofs := #[]
    for j in [:lits.size] do
      let lit := lits[j]
      let pr ← Meta.withLocalDeclD `h lit fun h => do
        if j == i then
          Meta.mkLambdaFVars #[h] $ ← orIntro resLits (lits.size - 1) (mkApp pr h)
        else
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro resLits idx h
      caseProofs := caseProofs.push $ pr

    let r ← orCases lits caseProofs

    return ← Meta.mkAppM ``Exists.intro #[a, pr]


--TODO: move
noncomputable def Inhabited.some [Inhabited α] (p : α → Prop) :=
  let _ : Decidable (∃ a, p a) := Classical.propDecidable _
  if hp: ∃ a, p a then Classical.choose hp else Inhabited.default

theorem Inhabited.some_spec [Inhabited α] {p : α → Prop} (hp : ∃ a, p a) : 
  p (Inhabited.some p) := by
  simp only [Inhabited.some, hp]
  exact Classical.choose_spec _

def clausificationStepE (e : Expr) (sign : Bool) (c : MClause) (i : Nat) : 
    RuleM (SimpResult (List (MClause × Option (Expr → MetaM Expr)))) := do
  match sign, e with
  | true, Expr.app (Expr.const ``Not _ _) e _ => do
    let res ← clausificationStepE e false c i -- TODO: Avoid recursive call?
    res.mapM fun res => res.mapM fun (c, pr?) => do 
      return (c, ← pr?.mapM fun pr => do 
        let pr : Expr → MetaM Expr := fun premise => do
          return ← pr $ ← Meta.mkAppM ``eq_false_of_not_eq_true #[premise]
        return pr)
  | false, Expr.app (Expr.const ``Not _ _) e _ => do
    let res ← clausificationStepE e true c i -- TODO: Avoid recursive call?
    res.mapM fun res => res.mapM fun (c, pr?) => do 
      return (c, ← pr?.mapM fun pr => do 
        let pr : Expr → MetaM Expr := fun premise => do
          return ← pr $ ← Meta.mkAppM ``eq_true_of_not_eq_false #[premise]
        return pr)
  | true, Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _ => do
    let pr₁ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_left #[premise]
    let pr₂ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_right #[premise]
    Applied [(MClause.mk #[Lit.fromExpr e₁], some pr₁), (MClause.mk #[Lit.fromExpr e₂], some pr₂)]
  | true, Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or #[premise]
    Applied [(MClause.mk #[Lit.fromExpr e₁, Lit.fromExpr e₂], some pr)]
  | true, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then
      if b.hasLooseBVars then
        throwError "Types depending on props are not supported" 
      let pr : Expr → MetaM Expr := fun premise => do
        return ← Meta.mkAppM ``clausify_imp #[premise]
      Applied [(MClause.mk #[Lit.fromExpr (mkNot ty), Lit.fromExpr b], some pr)]
    else 
      let mvar ← mkFreshExprMVar ty
      let pr : Expr → MetaM Expr := fun premise => do
        let mvar ← Meta.mkFreshExprMVar ty
        return ← Meta.mkAppM ``clausify_forall #[mvar, premise]
      Applied [(MClause.mk #[Lit.fromExpr $ b.instantiate1 mvar], some pr)]
  | true, Expr.app (Expr.app (Expr.const ``Exists _ _) ty _) (Expr.lam _ _ b _) _ => do
    let skTerm ← makeSkTerm ty b
    let pr : Expr → MetaM Expr := fun premise => do
      let mvar ← Meta.mkFreshExprMVar ty
      -- TODO: Decompose Or
      return ← Meta.mkAppM ``eq_true
        #[← Meta.mkAppM ``Inhabited.some_spec #[← Meta.mkAppM ``of_eq_true #[premise]]]
    Applied [(MClause.mk #[Lit.fromExpr $ b.instantiate1 skTerm], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _  => 
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_and_false #[premise]
    Applied [(MClause.mk #[Lit.fromExpr e₁ false, Lit.fromExpr e₂ false], some pr)]
  | false, Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    let pr₁ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or_false_left #[premise]
    let pr₂ : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``clausify_or_false_right #[premise]
    Applied [(MClause.mk #[Lit.fromExpr e₁ false], some pr₁), 
             (MClause.mk #[Lit.fromExpr e₂ false], some pr₂)]
  | false, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then 
      if b.hasLooseBVars then
        throwError "Types depending on props are not supported"
      let pr₁ : Expr → MetaM Expr := fun premise => do
        return ← Meta.mkAppM ``clausify_imp_false_left #[premise]
      let pr₂ : Expr → MetaM Expr := fun premise => do
        return ← Meta.mkAppM ``clausify_imp_false_right #[premise]
      Applied [(MClause.mk #[Lit.fromExpr ty], some pr₁),
               (MClause.mk #[Lit.fromExpr b false], some pr₂)]
    else clausifyExists ty (mkNot b)
  | false, Expr.app (Expr.app (Expr.const ``Exists _ _) ty _) (Expr.lam _ _ b _) _ => do
    let mvar ← mkFreshExprMVar ty
    let pr : Expr → MetaM Expr := fun premise => do
      let mvar ← Meta.mkFreshExprMVar ty
      return ← Meta.mkAppM ``clausify_exists_false #[mvar, premise]
    Applied [(MClause.mk #[Lit.fromExpr (b.instantiate1 mvar) false], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``of_eq_true #[premise]
    Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``not_of_eq_false #[premise] 
    Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← Meta.mkAppM ``of_eq_true #[premise]
    Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → MetaM Expr := fun premise => do
      return ← ← Meta.mkAppM ``of_not_eq_false #[premise]
    Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | _, _ => Unapplicable

where
  makeSkTerm ty b := do
    let mVarIds ← (e.collectMVars {}).result
    let skTy := ty.abstractMVars (mVarIds.map mkMVar)
    let mVarIdTys ← (mVarIds.mapM (fun mvarId => do ← inferType (mkMVar mvarId)))
    let skTy := mVarIdTys.foldr
      (fun mVarIdTy skTy => mkForall `_ BinderInfo.default mVarIdTy skTy)
      skTy
    let mkProof := fun parents => do
      trace[Meta.debug] "##B {b}"
      trace[Meta.debug] "##PRTS {parents}"
      -- TODO: Unfold Or
      let d ← Meta.mkAppM ``Inhabited.some #[mkLambda `x BinderInfo.default ty b]
      trace[Meta.debug] "##D {d}"
      return d
    let fvar ← mkFreshSkolem `sk skTy mkProof
    mkAppN fvar (mVarIds.map mkMVar)
  clausifyExists ty b := do
    let mVarIds ← (e.collectMVars {}).result
    let ty := ty.abstractMVars (mVarIds.map mkMVar)
    let mVarIdTys ← (mVarIds.mapM (fun mvarId => do ← inferType (mkMVar mvarId)))
    let ty := mVarIdTys.foldr
      (fun mVarIdTy ty => mkForall `_ BinderInfo.default mVarIdTy ty)
      ty
    let mkProof := fun parents => do
      return b
    let fvar ← mkFreshSkolem `sk ty mkProof
    let skTerm := mkAppN fvar (mVarIds.map mkMVar)
    Applied [(MClause.mk #[Lit.fromExpr $ b.instantiate1 skTerm], none)]

def clausificationStepLit (c : MClause) (i : Nat) : RuleM (SimpResult (List (MClause × Option (Expr → MetaM Expr)))) := do
  let l := c.lits[i]
  match l.rhs with
  | Expr.const ``True _ _ => clausificationStepE l.lhs true c i
  | Expr.const ``False _ _ => clausificationStepE l.lhs false c i
  | _ => return Unapplicable
-- TODO: True/False on left-hand side?


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
                    let resRight := (Clause.mk #[] resRight.toArray).toForallExpr
                    let resLits' := (resLeft.map Lit.toExpr).toArray.push resRight
                    -- TODO: use dproof and h
                    let dproof ← match dproof with
                    | none => Meta.mkSorry resRight true
                    | some dproof => dproof h
                    if not (← Meta.isDefEq (← Meta.inferType dproof) resRight) then
                      throwError "Error when reconstructing clausification. Expected type: {resRight}, but got: {dproof}"
                    Meta.mkLambdaFVars #[h] $ ← orIntro resLits' (c.lits.size - 1) dproof
                  else
                    let idx := if j ≥ i then j - 1 else j
                    Meta.mkLambdaFVars #[h] $ ← orIntro (resLits.map Lit.toExpr) idx h
                caseProofs := caseProofs.push $ pr

              let r ← orCases (← parentLits.map Lit.toExpr) caseProofs
              trace[Meta.debug] "###RES {res}"
              trace[Meta.debug] "###R {← Meta.inferType r}"
              let r ← Meta.mkLambdaFVars xs $ mkApp r appliedPremise
              trace[Meta.debug] "###R {r}"
              r
        (⟨c.lits.eraseIdx i ++ d.lits⟩, mkProof)
    | Removed => 
      return Removed
    | Unapplicable => 
      continue
  return Unapplicable

end Schroedinger