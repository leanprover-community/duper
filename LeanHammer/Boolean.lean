import LeanHammer.MClause
import LeanHammer.RuleM
import LeanHammer.Simp

namespace Schroedinger
open Lean
open RuleM
open SimpResult

def clausificationStepE (e : Expr) (sign : Bool): 
    RuleM (SimpResult (List MClause)) := do
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
    Applied [MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}]]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) e₁ _) e₂ _  =>
    Applied [MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}]]
  | true, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    Applied [MClause.mk #[{sign := false, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}]]
  | false, Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) e₁ _) e₂ _  =>
    Applied [MClause.mk #[{sign := true, lhs := e₁, rhs := e₂, lvl := lvl, ty := ty}]]
  | _, _ => Unapplicable
where
  clausifyAnd e₁ e₂ := do
    Applied [MClause.mk #[Lit.fromExpr e₁], MClause.mk #[Lit.fromExpr e₂]]
  clausifyOr e₁ e₂ := do
    Applied [MClause.mk #[Lit.fromExpr e₁, Lit.fromExpr e₂]]
  clausifyForall ty b := do
    let mvar ← mkFreshExprMVar ty
    Applied [MClause.mk #[Lit.fromExpr $ b.instantiate1 mvar]]
  clausifyExists ty b := do
    let mVarIds ← (e.collectMVars {}).result
    let ty := ty.abstractMVars (mVarIds.map mkMVar)
    let ty := mVarIds.foldr
      (fun mVarId ty => mkForall `_ BinderInfo.default (mkMVar mVarId) ty)
      ty
    let fvar ← mkFreshSkolem `sk ty
    let b ← b.instantiate1 (mkAppN fvar (mVarIds.map mkMVar))
    Applied [MClause.mk #[Lit.fromExpr b]]

def clausificationStepLit (l : Lit) : RuleM (SimpResult (List MClause)) := do
  match l.rhs with
  | Expr.const ``True _ _ => clausificationStepE l.lhs true
  | Expr.const ``False _ _ => clausificationStepE l.lhs false
  | _ => return Unapplicable

def clausificationStep : MSimpRule := fun c => do
  let mut ls := c.lits
  for i in [:ls.size] do
    match ← clausificationStepLit ls[i] with
    | Applied cs =>
      return Applied (cs.map fun c => c.appendLits $ ls.eraseIdx i)
    | Removed => 
      return Removed
    | Unapplicable => 
      continue
  return Unapplicable

end Schroedinger