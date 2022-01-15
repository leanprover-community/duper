import Lean
import LeanHammer.Util
import LeanHammer.Expr

namespace Schroedinger
open Lean
open Lean.Meta

structure Lit where
  sign : Bool
  lvl : Level
  ty : Expr
  lhs : Expr
  rhs : Expr
deriving Inhabited, BEq, Hashable

inductive LitSide | lhs | rhs
deriving Inhabited, BEq, Hashable

structure LitPos where
  side : LitSide
  pos : ExprPos
deriving Inhabited, BEq, Hashable


namespace Lit

def toExpr (lit : Lit) : Expr :=
  if lit.sign
  then mkApp3 (mkConst ``Eq [lit.lvl]) lit.ty lit.lhs lit.rhs
  else mkApp3 (mkConst ``Ne [lit.lvl]) lit.ty lit.lhs lit.rhs

def fromExpr (e : Expr) (sign := true) : Lit :=
  Lit.mk
    (sign := true)
    (lvl := levelOne)
    (ty := mkSort levelZero)
    (lhs := e)
    (rhs := if sign then mkConst ``True else mkConst ``False)
  

def map (f : Expr → Expr) (l : Lit) :=
  {l with ty := f l.ty, lhs := f l.lhs, rhs := f l.rhs}

def mapM {m : Type → Type w} [Monad m] (f : Expr → m Expr) (l : Lit) : m Lit := do
  return {l with ty := ← f l.ty, lhs := ← f l.lhs, rhs := ← f l.rhs}

def fold {α : Type v} (f : α → Expr → α) (init : α) (l : Lit) : α :=
  f (f (f init l.ty) l.lhs) l.rhs

def foldWithTypeM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → m β) (init : β) (l : Lit) : m β := do
  f (← f (← f init l.ty) l.lhs) l.rhs

def foldM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → LitPos → m β) (init : β) (l : Lit) : m β := do
  f (← f init l.lhs ⟨LitSide.lhs, ExprPos.empty⟩) l.rhs ⟨LitSide.rhs, ExprPos.empty⟩

def foldGreenM {β : Type v} [Inhabited β] {m : Type v → Type w} [Monad m] 
    (f : β → Expr → LitPos → m β) (init : β) (l : Lit) : m β := do
  let fLhs := fun acc e p => f acc e ⟨LitSide.lhs, p⟩
  let fRhs := fun acc e p => f acc e ⟨LitSide.rhs, p⟩
  l.rhs.foldGreenM fRhs (← l.lhs.foldGreenM fLhs init) 

def getAtPos! (l : Lit) (pos : LitPos) : Expr :=
  match pos.side with
  | LitSide.lhs => l.lhs.getAtPos! pos.pos
  | LitSide.rhs => l.rhs.getAtPos! pos.pos

def symm (l : Lit) : Lit :=
{l with 
  lhs := l.rhs
  rhs := l.lhs}

instance : ToFormat Lit :=
⟨ fun lit => format lit.toExpr ⟩

instance : ToMessageData Lit :=
⟨ fun lit => lit.toExpr ⟩

end Lit

structure Clause :=
(bVarTypes : Array Expr)
(lits : Array Lit)
deriving Inhabited, BEq, Hashable

structure ClausePos where
  lit : Nat
  side : LitSide
  pos : ExprPos
deriving Inhabited, BEq, Hashable

namespace Clause

def empty : Clause := ⟨#[], #[]⟩

def fromExpr (e : Expr) : Clause :=
  Clause.mk #[] #[Lit.fromExpr e]

def toExpr (c : Clause) : Expr :=
  litsToExpr c.lits.data
where litsToExpr : List Lit → Expr
| [] => mkConst ``False
| [l] => l.toExpr
| l :: ls => mkApp2 (mkConst ``Or) l.toExpr (litsToExpr ls)

def toForallExpr (c : Clause) : Expr :=
  c.bVarTypes.foldr (fun ty b => mkForall Name.anonymous BinderInfo.default ty b) c.toExpr

instance : ToFormat Clause :=
⟨ fun c => format c.toExpr ⟩

instance : ToMessageData Clause :=
⟨ fun c => c.toExpr ⟩

def weight (c : Clause) : Nat :=
  c.lits.foldl (fun acc lit => acc + weightExpr lit.lhs + weightExpr lit.rhs) 0
where 
  weightExpr : Expr → Nat
  | Expr.bvar _ _        => 1
  | Expr.fvar _ _        => 1
  | Expr.mvar _ _        => 1
  | Expr.sort _ _        => 1
  | Expr.const _ _ _     => 1
  | Expr.app a b _       => weightExpr a + weightExpr b
  | Expr.lam _ _ b _     => 1 + weightExpr b
  | Expr.forallE _ _ b _ => 1 + weightExpr b
  | Expr.letE _ _ v b _  => 1 + weightExpr v + weightExpr b
  | Expr.lit _ _         => 1
  | Expr.mdata _ b _     => 1 + weightExpr b
  | Expr.proj _ _ b _    => 1 + weightExpr b

end Clause