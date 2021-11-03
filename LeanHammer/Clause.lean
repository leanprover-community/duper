import Lean

open Lean
open Lean.Meta

structure Lit :=
(sign : Bool)
(lvl : Level)
(ty : Expr)
(lhs : Expr)
(rhs : Expr)
deriving Inhabited

namespace Lit

def ofExpr (e : Expr) : MetaM Lit :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq [lvl] _) ty _) lhs _) rhs _ =>
    Lit.mk true lvl ty lhs rhs
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne [lvl] _) ty _) lhs _) rhs _ =>
    Lit.mk false lvl ty lhs rhs
  | _ => throwError "Cannot make literal from {e}"

def toExpr (lit : Lit) : Expr :=
  if lit.sign
  then mkApp3 (mkConst ``Eq [lit.lvl]) lit.ty lit.lhs lit.rhs
  else mkApp3 (mkConst ``Ne [lit.lvl]) lit.ty lit.lhs lit.rhs

instance : ToMessageData Lit :=
⟨ fun lit => lit.toExpr ⟩

end Lit

structure Clause :=
(lits : Array Lit)
deriving Inhabited

namespace Clause

def ofExpr (e : Expr) : MetaM Clause :=
  forallTelescope e fun xs e => do
    return Clause.mk (← ofExprLits e)
where ofExprLits (lits : Expr) : MetaM (Array Lit) :=
  match lits with
  | Expr.app (Expr.app (Expr.const ``Or _ _) lit _) lits _ => do
    return (← ofExprLits lits).push $ ← Lit.ofExpr lit
  | _ => return #[← Lit.ofExpr lits]

def toExpr (c : Clause) : Expr :=
  litsToExpr c.lits.data
where litsToExpr : List Lit → Expr
| [] => mkConst ``False
| [l] => l.toExpr
| l :: ls => mkApp2 (mkConst ``Or) l.toExpr (litsToExpr ls)

instance : ToMessageData Clause :=
⟨ fun c => c.toExpr ⟩

end Clause