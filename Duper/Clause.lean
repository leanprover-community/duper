import Lean
import Duper.Util.Misc
import Duper.Expr
import Duper.Order

namespace Duper
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

namespace LitSide

def toggleSide (side : LitSide) : LitSide := match side with
| LitSide.lhs => LitSide.rhs
| LitSide.rhs => LitSide.lhs

end LitSide

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

def makeLhs (lit : Lit) (side : LitSide) := match side with
| LitSide.lhs => lit
| LitSide.rhs => lit.symm

def getSide (lit : Lit) (side : LitSide) := match side with
| LitSide.lhs => lit.lhs
| LitSide.rhs => lit.rhs

def getOtherSide (lit : Lit) (side : LitSide) := getSide lit (LitSide.toggleSide side)

instance : ToFormat Lit :=
⟨ fun lit => format lit.toExpr ⟩

instance : ToMessageData Lit :=
⟨ fun lit => lit.toExpr ⟩


open Comparison
def compare (ord : Expr → Expr → MetaM Comparison) (l₁ l₂ : Lit) : MetaM Comparison := do
  let cll ← ord l₁.lhs l₂.lhs
  if cll == Incomparable then return Incomparable
  let clr ← ord l₁.lhs l₂.rhs
  if clr == Incomparable then return Incomparable
  let crl ← ord l₁.rhs l₂.lhs
  if crl == Incomparable then return Incomparable
  let crr ← ord l₁.rhs l₂.rhs
  if crr == Incomparable then return Incomparable

  match cll, clr, crl, crr with
  | GreaterThan, GreaterThan, _, _ => return GreaterThan
  | _, _, GreaterThan, GreaterThan => return GreaterThan
  | LessThan, _, LessThan, _ => return LessThan
  | _, LessThan, _, LessThan => return LessThan

  | GreaterThan, _, _, GreaterThan => return GreaterThan
  | LessThan, _, _, LessThan => return LessThan
  | _, GreaterThan, GreaterThan, _ => return GreaterThan
  | _, LessThan, LessThan, _ => return LessThan
  | _, _, _, _ => do

    let csign := match l₁.sign, l₂.sign with
    | true, true => Equal
    | false, true => GreaterThan
    | true, false => LessThan
    | false, false => Equal

    match cll, clr, crl, crr, csign with
    | Equal, _, _, c, Equal => return c
    | _, Equal, c, _, Equal => return c
    | _, c, Equal, _, Equal => return c
    | c, _, _, Equal, Equal => return c

    | Equal, _, _, Equal, _ => return Equal
    | _, Equal, Equal, _, _ => return Equal
    
    | Equal, _, _, _, c => return c
    | _, Equal, _, _, c => return c
    | _, _, Equal, _, c => return c
    | _, _, _, Equal, c => return c

    | _, _, _, _, _ => throwError "unexpected comparisons : {cll} {clr} {crl} {crr} {csign}"

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

