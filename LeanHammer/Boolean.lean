import LeanHammer.Clause

open Lean

#check MetaM

def clausificationStepE (lctx : LocalContext) (bVarTypes : List Expr) (e : Expr) : 
    List (LocalContext × List Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.const ``And _ _) e₁ _) e₂ _ => [(lctx, bVarTypes, e₁),(lctx, bVarTypes, e₂)]
  | Expr.app (Expr.app (Expr.const ``Or _ _) e₁ _) e₂ _ => [(lctx, bVarTypes, e₁),(lctx, bVarTypes, e₂)]
  | Expr.forallE _ ty b _ => [(lctx, ty :: bVarTypes, b)]
  | _ => e


def clausificationStep (c : Clause) : MetaM (List Clause) := do
  for i in [:c.lits.size] do
    break--c.lits[i]
  sorry