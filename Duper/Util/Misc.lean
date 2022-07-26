import Lean
open Lean

instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

-- TODO: Use this?
-- #check Lean.Meta.abstractMVars

def Lean.Expr.abstractMVars (e : Expr) (mVars : Array Expr) : Expr :=
  let rec visit (e : Expr) (offset : Nat) : Expr :=
    match e with
    | Expr.mvar .. => 
      match mVars.indexOf? e with
      | some i => mkBVar (mVars.size - 1 - i + offset)
      | none => e
    | Expr.app f a _       => e.updateApp! (visit f offset) (visit a offset)
    | Expr.mdata _ b _     => e.updateMData! (visit b offset)
    | Expr.proj _ _ b _    => e.updateProj! (visit b offset)
    | Expr.letE _ t v b _  => e.updateLet! (visit t offset) (visit v offset) (visit b (offset+1))
    | Expr.lam _ d b _     => e.updateLambdaE! (visit d offset) (visit b (offset+1))
    | Expr.forallE _ d b _ => e.updateForallE! (visit d offset) (visit b (offset+1))
    | e                    => e
  visit e 0

/-- Naively determines whether an expression is `true` or `True` (without applying any substitutions or 
    instantiating any metavariables) -/
def exprIsTrue (e : Expr) : Bool := e == mkConst ``True || e == mkConst ``true

/-- Naively determines whether an expression is `false` or `False` (without applying any substitutions or 
    instantiating any metavariables) -/
def exprIsFalse (e : Expr) : Bool := e == mkConst ``False || e == mkConst ``false