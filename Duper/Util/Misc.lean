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

def Lean.Meta.findInstance (ty : Expr) : MetaM Expr := do
  let ty ← instantiateMVars ty
  forallTelescope ty fun xs ty' => do
    let u ← do
      if ty' == .sort (.succ .zero) then
        pure <| mkConst ``Nat
      else if let .sort (.succ l) := ty then
        pure <| mkSort l
      else try
        Meta.mkAppOptM ``inferInstanceAs #[ty', none]
      catch _ =>
        -- Find assumption in Local Context
        let ctx ← getLCtx
        let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
          let declExpr := decl.toExpr
          let declType ← Lean.Meta.inferType declExpr
          if ← Lean.Meta.isDefEq declType ty'
          then
            return Option.some declExpr
          else
            return Option.none
        match option_matching_expr with
        | some e => pure e
        | none => Meta.mkAppOptM ``default #[ty', none]
    mkLambdaFVars xs u