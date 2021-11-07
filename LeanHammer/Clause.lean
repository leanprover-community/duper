import Lean
import LeanHammer.Util

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

def fromExpr (e : Expr) (sign := true) : Lit :=
  Lit.mk
    (sign := true)
    (lvl := levelZero)
    (lhs := e)
    (rhs := if sign then mkConst ``True else mkConst ``False)
    (ty := mkConst `Prop)
  

def map (f : Expr → Expr) (l : Lit) :=
  {l with ty := f l.ty, lhs := f l.lhs, rhs := f l.rhs}

def foldl {α : Type v} (f : α → Expr → α) (init : α) (l : Lit) : α :=
  f (f (f init l.ty) l.lhs) l.rhs

instance : ToMessageData Lit :=
⟨ fun lit => lit.toExpr ⟩

end Lit

structure Clause :=
(bVarTypes : Array Expr)
(lits : Array Lit)
deriving Inhabited, BEq, Hashable

namespace Clause

def fromExpr (e : Expr) : Clause :=
  Clause.mk #[] #[Lit.fromExpr e]

def toExpr (c : Clause) : Expr :=
  litsToExpr c.lits.data
where litsToExpr : List Lit → Expr
| [] => mkConst ``False
| [l] => l.toExpr
| l :: ls => mkApp2 (mkConst ``Or) l.toExpr (litsToExpr ls)

instance : ToMessageData Clause :=
⟨ fun c => c.toExpr ⟩

end Clause