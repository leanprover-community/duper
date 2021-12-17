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
      | some i => mkBVar (offset + i)
      | none => e
    | Expr.app f a _       => return e.updateApp! (visit f offset) (visit a offset)
    | Expr.mdata _ b _     => return e.updateMData! (visit b offset)
    | Expr.proj _ _ b _    => return e.updateProj! (visit b offset)
    | Expr.letE _ t v b _  => return e.updateLet! (visit t offset) (visit v offset) (visit b (offset+1))
    | Expr.lam _ d b _     => return e.updateLambdaE! (visit d offset) (visit b (offset+1))
    | Expr.forallE _ d b _ => return e.updateForallE! (visit d offset) (visit b (offset+1))
    | e                    => return e
  visit e 0

def Option.mapM [Monad m] (f : α → m β) : Option α → m (Option β)
| some a => f a
| none   => none