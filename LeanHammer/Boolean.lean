import LeanHammer.MClause
import LeanHammer.RuleM

open Lean
open RuleM

#check MetaM

def clausificationStepE (e : Expr) : 
    RuleM (Option (List MClause)) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _ => 
    some [MClause.mk #[Lit.fromExpr e₁], MClause.mk #[Lit.fromExpr e₂]]
  | Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ =>
    some [MClause.mk #[Lit.fromExpr e₁, Lit.fromExpr e₂]]
  -- | Expr.forallE _ ty b _ => [(lctx, ty :: bVarTypes, b)]
  | _ => none

def clausificationStepLit (l : Lit) : RuleM (Option (List MClause)) := do
  match l.rhs with
  | Expr.const ``True _ _ => clausificationStepE l.lhs
  | _ => return none

def Array.mapFirst [Inhabited α] (as : Array α) (f : α → Option α) : Option (Array α) := do
  let mut as := as
  for i in [:as.size] do
    match f as[i] with
    | some b => 
      as := as.set! i b
      return some as
    | none => 
      continue
  return none

def clausificationStep (c : MClause) : RuleM (Option (List MClause)) := do
  let mut ls := c.lits
  for i in [:ls.size] do
    match ← clausificationStepLit ls[i] with
    | some cs =>
      return cs.map fun c => c.appendLits $ ls.eraseIdx i
    | none => 
      continue
  return none