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
theorem eq_of_neq_false {α : Sort u} {a b : α} (h: (a ≠ b) = False) : a = b := 
  Classical.byContradiction fun hn => h ▸ hn

def clausificationStepE (e : Expr) (sign : Bool): 
    RuleM (SimpResult (List (MClause × Option (Expr → Expr → MetaM Expr)))) := do
  match sign, e with
  | sign, Expr.app (Expr.const ``Not _ _) e _ => do
    clausificationStepE e (not sign)
  | true, Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _ => 
    clausifyAnd e₁ e₂
  | true, Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    clausifyOr e₁ e₂
  | true, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then clausifyOr (mkNot ty) b -- TODO: what if b contains loose bvars?
    else clausifyForall ty b
  | true, Expr.app (Expr.app (Expr.const ``Exists _ _) ty _) (Expr.lam _ _ b _) _ => do
    clausifyExists ty b
  | false, Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _  => 
    clausifyOr (mkNot e₁) (mkNot e₂)
  | false, Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    clausifyAnd (mkNot e₁) (mkNot e₂)
  | false, Expr.forallE _ ty b _ => do
    if (← inferType ty).isProp
    then clausifyAnd ty (mkNot b) -- TODO: what if b contains loose bvars?
    else clausifyExists ty (mkNot b)
  | false, Expr.app (Expr.app (Expr.const ``Exists _ _) ty _) (Expr.lam _ _ b _) _ => do
    clausifyForall ty (mkNot b)
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → Expr → MetaM Expr := fun ty premise => do
      return ← Meta.mkAppM ``of_eq_true #[premise]
    Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → Expr → MetaM Expr := fun ty premise => do
      trace[Meta.debug] "ty {ty}"
      trace[Meta.debug] "premise {premise}"
      return ← Meta.mkAppM ``not_of_eq_false #[premise] 
    Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → Expr → MetaM Expr := fun ty premise => do
      return ← Meta.mkAppM ``of_eq_true #[premise]
    Applied [(MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    let pr : Expr → Expr → MetaM Expr := fun ty premise => do
      trace[Meta.debug] "ty {ty}"
      trace[Meta.debug] "premise {premise}"
      return ← ← Meta.mkAppM ``eq_of_neq_false #[premise]
    Applied [(MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}], some pr)]
  | _, _ => Unapplicable
where
  clausifyAnd e₁ e₂ := do
    let pr : Expr → Expr → MetaM Expr := fun ty premise => do
      trace[Meta.debug] "ty {ty}"
      trace[Meta.debug] "premise {premise}"
      return ← Meta.mkSorry ty true
    Applied [(MClause.mk #[Lit.fromExpr e₁], none), (MClause.mk #[Lit.fromExpr e₂], some pr)]
  clausifyOr e₁ e₂ := do
    let pr : Expr → Expr → MetaM Expr := fun ty premise => do
      trace[Meta.debug] "ty {ty}"
      trace[Meta.debug] "premise {premise}"
      return ← Meta.mkSorry ty true
    Applied [(MClause.mk #[Lit.fromExpr e₁, Lit.fromExpr e₂], some pr)]
  clausifyForall ty b := do
    let mvar ← mkFreshExprMVar ty
    Applied [(MClause.mk #[Lit.fromExpr $ b.instantiate1 mvar], none)]
  clausifyExists ty b := do
    let mVarIds ← (e.collectMVars {}).result
    let ty := ty.abstractMVars (mVarIds.map mkMVar)
    let ty := mVarIds.foldr
      (fun mVarId ty => mkForall `_ BinderInfo.default (mkMVar mVarId) ty)
      ty
    let fvar ← mkFreshSkolem `sk ty b
    let b ← b.instantiate1 (mkAppN fvar (mVarIds.map mkMVar))
    Applied [(MClause.mk #[Lit.fromExpr b], none)]

def clausificationStepLit (l : Lit) : RuleM (SimpResult (List (MClause × Option (Expr → Expr → MetaM Expr)))) := do
  match l.rhs with
  | Expr.const ``True _ _ => clausificationStepE l.lhs true
  | Expr.const ``False _ _ => clausificationStepE l.lhs false
  | _ => return Unapplicable
-- TODO: True/False on left-hand side?

-- TODO: Proof reconstruction
def clausificationStep : MSimpRule := fun c => do
  for i in [:c.lits.size] do
    match ← clausificationStepLit c.lits[i] with
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
                    | some dproof => dproof resRight h
                    Meta.mkLambdaFVars #[h] $ ← orIntro resLits' (c.lits.size - 1) dproof
                  else
                    let idx := if j ≥ i then j - 1 else j
                    Meta.mkLambdaFVars #[h] $ ← orIntro (resLits.map Lit.toExpr) idx h
                caseProofs := caseProofs.push $ pr

              let r ← orCases (← parentLits.map Lit.toExpr) body caseProofs
              trace[Meta.debug] "###RES {res}"
              trace[Meta.debug] "###R {← Meta.inferType r}"
              Meta.mkLambdaFVars xs $ mkApp r appliedPremise
        (⟨c.lits.eraseIdx i ++ d.lits⟩, mkProof)
    | Removed => 
      return Removed
    | Unapplicable => 
      continue
  return Unapplicable

end Schroedinger