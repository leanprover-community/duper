import LeanHammer.MClause
import LeanHammer.RuleM
import LeanHammer.Simp

open Lean
open RuleM
open SimpResult

#check Meta.forallMetaTelescope

def clausificationStepE (e : Expr) : 
    RuleM (SimpResult (List MClause)) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _ => 
    Applied [MClause.mk #[Lit.fromExpr e₁], MClause.mk #[Lit.fromExpr e₂]]
  | Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    Applied [MClause.mk #[Lit.fromExpr e₁, Lit.fromExpr e₂]]
  | Expr.forallE .. => do
    let (mVars, _, b) ← forallMetaTelescope e
    Applied [MClause.mk #[Lit.fromExpr b]]
  | Expr.app (Expr.app (Expr.const ``Exists _ _) α _) (Expr.lam _ _ b _) _ => do
    let fvar ← mkFreshFVar `sk α
    let b ← b.instantiate1 fvar
    Applied [MClause.mk #[Lit.fromExpr b]]
  | _ => Unapplicable

def clausificationStepLit (l : Lit) : RuleM (SimpResult (List MClause)) := do
  match l.rhs with
  | Expr.const ``True _ _ => clausificationStepE l.lhs
  | _ => return Unapplicable

def clausificationStep : SimpRule := fun c => do
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