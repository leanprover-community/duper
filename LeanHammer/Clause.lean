import Lean

open Lean
open Lean.Meta

structure Lit :=
(sign : Bool)
(lvl : Level)
(ty : Expr)
(lhs : Expr)
(rhs : Expr)
deriving Inhabited, BEq, Hashable

namespace Lit

def toExpr (lit : Lit) : Expr :=
  if lit.sign
  then mkApp3 (mkConst ``Eq [lit.lvl]) lit.ty lit.lhs lit.rhs
  else mkApp3 (mkConst ``Ne [lit.lvl]) lit.ty lit.lhs lit.rhs

instance : ToMessageData Lit :=
⟨ fun lit => lit.toExpr ⟩

end Lit

structure Clause :=
(id : Nat)
(lits : List Lit)
deriving Inhabited, BEq, Hashable

namespace Clause

def toExpr (c : Clause) : Expr :=
  litsToExpr c.lits
where litsToExpr : List Lit → Expr
| [] => mkConst ``False
| [l] => l.toExpr
| l :: ls => mkApp2 (mkConst ``Or) l.toExpr (litsToExpr ls)

instance : ToMessageData Clause :=
⟨ fun c => c.toExpr ⟩

end Clause