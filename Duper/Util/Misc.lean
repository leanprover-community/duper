import Lean
open Lean

instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

-- The following two functions are copied from Lean's
-- standard library. The only difference is that we
-- replace `whnf e` with `e`.
private partial def instantiateForallAux (ps : Array Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩
    match e with
    | Expr.forallE _ _ b _ => instantiateForallAux ps (i+1) (b.instantiate1 p)
    | _                => throwError "invalid instantiateForallNoReducing, too many parameters"
  else
    return e

/-- Given `e` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `B[p_1, ..., p_n]`. -/
def Lean.Expr.instantiateForallNoReducing (e : Expr) (ps : Array Expr) : MetaM Expr :=
  instantiateForallAux ps 0 e

def Lean.Meta.findInstance (ty : Expr) : MetaM Expr :=
  if ty == .sort (.succ .zero) then
    return (mkConst ``Nat)
  else
    Meta.mkAppOptM ``default #[some ty, none]