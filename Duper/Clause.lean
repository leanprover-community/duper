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

def Lit.toString (l : Lit) :=
  ToString.toString l.lhs ++ if l.sign then " = " else " ≠ " ++ ToString.toString l.rhs

def LitSide.format (ls : LitSide) : MessageData :=
  match ls with
  | lhs => m!"lhs"
  | rhs => m!"rhs"

instance : ToMessageData LitSide := ⟨LitSide.format⟩

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

def fromSingleExpr (e : Expr) (sign := true) : Lit :=
  Lit.mk
    (sign := true)
    (lvl := levelOne)
    (ty := mkSort levelZero)
    (lhs := Expr.consumeMData e)
    (rhs := if sign then mkConst ``True else mkConst ``False)

def fromExpr : Expr → Lit
| .app (.app (.app (.const ``Eq lvl) ty) lhs) rhs =>
  ⟨true, lvl[0]!, ty, lhs, rhs⟩
| .app (.app (.app (.const ``Ne lvl) ty) lhs) rhs =>
  ⟨false, lvl[0]!, ty, lhs, rhs⟩
| e@(_) => dbg_trace "Lit.fromExpr :: Unexpected Expression: {e}"; Lit.fromSingleExpr e

def map (f : Expr → Expr) (l : Lit) :=
  -- Should we really map into `ty`?
  {l with ty := f l.ty, lhs := f l.lhs, rhs := f l.rhs}

def instantiateLevelParamsArray (l : Lit) (paramNames : Array Name) (levels : Array Level) :=
  {l with lvl := l.lvl.instantiateParams paramNames.data levels.data
          ty := l.ty.instantiateLevelParamsArray paramNames levels
          lhs := l.lhs.instantiateLevelParamsArray paramNames levels
          rhs := l.rhs.instantiateLevelParamsArray paramNames levels}

def mapWithPos (f : Expr → Expr × Array ExprPos) (l : Lit) :=
  let (l', lposes) := f l.lhs
  let (r', rposes) := f l.rhs
  -- Does not map into `ty`
  let lit' := {l with lhs := l', rhs := r'}
  let lp' := lposes.map (fun p => LitPos.mk .lhs p)
  let rp' := rposes.map (fun p => LitPos.mk .rhs p)
  (lit', lp' ++ rp')

def mapMWithPos [Monad m] [MonadLiftT MetaM m] (f : Expr → m (Expr × Array ExprPos)) (l : Lit) : m (Lit × Array LitPos) := do
  let (l', lposes) ← f l.lhs
  let (r', rposes) ← f l.rhs
  -- Does not map into `ty`
  let lit' := {l with lhs := l', rhs := r'}
  let lp' := lposes.map (fun p => LitPos.mk .lhs p)
  let rp' := rposes.map (fun p => LitPos.mk .rhs p)
  return (lit', lp' ++ rp')

def mapByPos (f : Expr → Array ExprPos → Expr) (l : Lit) (poses : Array LitPos) := Id.run <| do
  let mut lposes := #[]
  let mut rposes := #[]
  for ⟨side, pos⟩ in poses do
    if side == .lhs then
      lposes := lposes.push pos
    else
      rposes := rposes.push pos
  -- Does not map into `ty`
  let l' := f l.lhs lposes
  let r' := f l.rhs rposes
  return {l with lhs := l', rhs := r'}

def mapMByPos [Monad m] [MonadLiftT MetaM m] (f : Expr → Array ExprPos → m Expr) (l : Lit) (poses : Array LitPos) : m Lit := do
  let mut lposes := #[]
  let mut rposes := #[]
  for ⟨side, pos⟩ in poses do
    if side == .lhs then
      lposes := lposes.push pos
    else
      rposes := rposes.push pos
  -- Does not map into `ty`
  let l' ← f l.lhs lposes
  let r' ← f l.rhs rposes
  return {l with lhs := l', rhs := r'}

def mapM {m : Type → Type w} [Monad m] (f : Expr → m Expr) (l : Lit) : m Lit := do
  return {l with ty := ← f l.ty, lhs := ← f l.lhs, rhs := ← f l.rhs}

def fold {α : Type v} (f : α → Expr → α) (init : α) (l : Lit) : α :=
  f (f init l.lhs) l.rhs

def foldWithTypeM {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Expr → m β) (init : β) (l : Lit) : m β := do
  f (← f (← f init l.ty) l.lhs) l.rhs

def foldM {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Expr → LitPos → m β) (init : β) (l : Lit) : m β := do
  f (← f init l.lhs ⟨LitSide.lhs, ExprPos.empty⟩) l.rhs ⟨LitSide.rhs, ExprPos.empty⟩

def foldGreenM {β : Type} [Monad m] [MonadLiftT MetaM m]
    (f : β → Expr → LitPos → m β) (init : β) (l : Lit) : m β := do
  let fLhs := fun acc e p => f acc e ⟨LitSide.lhs, p⟩
  let fRhs := fun acc e p => f acc e ⟨LitSide.rhs, p⟩
  l.rhs.foldGreenM fRhs (← l.lhs.foldGreenM fLhs init)

def getAtPos! [Monad m] [MonadLiftT MetaM m] (l : Lit) (pos : LitPos) : m Expr :=
  match pos.side with
  | LitSide.lhs => l.lhs.getAtPos! pos.pos
  | LitSide.rhs => l.rhs.getAtPos! pos.pos

def replaceAtPos? [Monad m] [MonadLiftT MetaM m] (l : Lit) (pos : LitPos) (replacement : Expr) : m (Option Lit) := do
  match pos.side with
  | LitSide.lhs =>
    match ← l.lhs.replaceAtPos? pos.pos replacement with
    | some newLhs => return some {l with lhs := newLhs}
    | none => return none
  | LitSide.rhs =>
    match ← l.rhs.replaceAtPos? pos.pos replacement with
    | some newRhs => return some {l with rhs := newRhs}
    | none => return none

def replaceAtPos! [Monad m] [MonadLiftT MetaM m] [MonadError m] (l : Lit) (pos : LitPos) (replacement : Expr) : m Lit :=
  match pos.side with
  | LitSide.lhs => return {l with lhs := ← l.lhs.replaceAtPos! pos.pos replacement}
  | LitSide.rhs => return {l with rhs := ← l.rhs.replaceAtPos! pos.pos replacement}

-- Note : This function will throw error if ``pos`` is not a valid ``pos`` for `l`
def replaceAtPosUpdateType? (l : Lit) (pos : LitPos) (replacement : Expr) : MetaM (Option Lit) := do
  let repPos ← replaceAtPos! l pos replacement
  try
    let ty ← Meta.inferType repPos.lhs
    let sort ← Meta.inferType ty
    let sortReduced ← Meta.reduce sort false false true
    if ! sortReduced.isSort then
      trace[Meta.debug] "replaceAtPosUpdateType? :: {sortReduced} is not a sort"
      return none
    let lvl := sortReduced.sortLevel!
    let res : Lit := {repPos with ty := ty, lvl := lvl}
    if ← Meta.isTypeCorrect res.toExpr then
      return some res
    else
      return none
  catch _ =>
    return none

/-- This function acts as Meta.kabstract except that it takes a LitPos rather than Occurrences and expects
    the given expression to consist only of applications up to the given ExprPos. Additionally, since the exact
    position is given, we don't need to pass in Meta.kabstract's second argument p -/
def abstractAtPos! (l : Lit) (pos : LitPos) : MetaM Lit := do
  match pos.side with
  | LitSide.lhs => return {l with lhs := ← l.lhs.abstractAtPos! pos.pos}
  | LitSide.rhs => return {l with rhs := ← l.rhs.abstractAtPos! pos.pos}

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
def compare (ord : Expr → Expr → Bool → MetaM Comparison) (alreadyReduced : Bool) (l₁ l₂ : Lit) : MetaM Comparison := do
  let l₁ ←
    if alreadyReduced then pure l₁
    else l₁.mapM (fun e => betaEtaReduceInstMVars e)
  let l₂ ←
    if alreadyReduced then pure l₂
    else l₂.mapM (fun e => betaEtaReduceInstMVars e)

  let cll ← ord l₁.lhs l₂.lhs true
  if cll == Incomparable then return Incomparable
  let clr ← ord l₁.lhs l₂.rhs true
  if clr == Incomparable then return Incomparable
  let crl ← ord l₁.rhs l₂.lhs true
  if crl == Incomparable then return Incomparable
  let crr ← ord l₁.rhs l₂.rhs true
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

-- The bvar `bᵢ` in `lits` is related to `bVarTypes[l-i-1]`,
-- where `l = len(bVarTypes)`. Each Clause `c` will be
-- associated with a proof `p`.
-- !!!!!!!!!!!!!!!!! We keep an invariant !!!!!!!!!!!!!!!!
--               `p : c.toForallExpr`
structure Clause :=
(paramNames : Array Name)
(bVarTypes : Array Expr)
(lits : Array Lit)
deriving Inhabited, BEq, Hashable

structure ClausePos extends LitPos where
  lit : Nat
deriving Inhabited, BEq, Hashable

def ClausePos.format (pos : ClausePos) : MessageData :=
  m!"\{lit: {pos.lit}, side: {pos.side}, ExprPos: {pos.pos}}"

instance : ToMessageData ClausePos := ⟨ClausePos.format⟩

namespace Clause

def empty : Clause := ⟨#[], #[], #[]⟩

def fromSingleExpr (paramNames : Array Name) (e : Expr) : Clause :=
  Clause.mk paramNames #[] #[Lit.fromSingleExpr e]

def litsToExpr : List Lit → Expr
| [] => mkConst ``False
| [l] => l.toExpr
| l :: ls => mkApp2 (mkConst ``Or) l.toExpr (litsToExpr ls)

def toExpr (c : Clause) : Expr :=
  litsToExpr c.lits.data

def foldM {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → Expr → ClausePos → m β) (init : β) (c : Clause) : m β := do
  let mut acc := init
  for i in [:c.lits.size] do
    let f' := fun acc e pos => f acc e {pos with lit := i}
    acc ← c.lits[i]!.foldM f' acc
  return acc

def getAtPos! [Monad m] [MonadLiftT MetaM m] (c : Clause) (pos : ClausePos) : m Expr :=
  c.lits[pos.lit]!.getAtPos! ⟨pos.side, pos.pos⟩

def mapMUpdateType [instMonad : Monad m] (c : Clause) (f : Expr → m Expr) := do
  let bVarTypes ← c.bVarTypes.mapM f
  let lits ← c.lits.mapM (Lit.mapM f)
  return {c with bVarTypes := bVarTypes, lits := lits}

def instantiateLevelParamsArray (c : Clause) (paramNames : Array Name) (levels : Array Level) :=
  let bVarTypes := c.bVarTypes.map (fun e => e.instantiateLevelParamsArray paramNames levels)
  let lits := c.lits.map (fun l => l.instantiateLevelParamsArray paramNames levels)
  {c with bVarTypes := bVarTypes, lits := lits}

def toForallExpr (c : Clause) : Expr :=
  c.bVarTypes.foldr (fun ty b => mkForall Name.anonymous BinderInfo.default ty b) c.toExpr

def toLambdaExpr (c : Clause) : Expr :=
  c.bVarTypes.foldr (fun ty b => mkLambda Name.anonymous BinderInfo.default ty b) c.toExpr

def fromForallExpr (paramNames : Array Name) (e : Expr) : Clause :=
  let (bvarTypes, e) := deForall e
  ⟨paramNames, bvarTypes.toArray, (litsFromExpr e).toArray⟩
where
  deForall : Expr → List Expr × Expr
  | .forallE _ ty body _ => let (l, e) := deForall body; (ty::l, e)
  | e@(_) => ([], e)
  litsFromExpr : Expr → List Lit
  | .app (.app (.const ``Or _) litexpr) other => Lit.fromExpr litexpr :: litsFromExpr other
  | .const ``False _                          => []
  | e@(_)                                     => [Lit.fromExpr e]

instance : ToFormat Clause :=
⟨ fun c => format c.toForallExpr ⟩

instance : ToMessageData Clause :=
⟨ fun c => c.toForallExpr ⟩

def weight (c : Clause) : Nat :=
  c.lits.foldl (fun acc lit => acc + lit.lhs.weight + lit.rhs.weight) 0

/-- Determines the precedence clause `c` should have for clause selection. Lower values indicate higher precedence -/
def selectionPrecedence (c : Clause) (goalDistance : Nat) : Nat :=
  /- TODO: Experiment with different coefficients for c.weight and goalDistance. Zipperposition's goal_oriented
     clause selection function has (among other heuristics) c.weight given a coefficient of 4 and goalDistance given
     a coefficient of 1 (meaning the returned precedence would be `4 * c.weight + goalDistance`) -/
  c.weight + goalDistance

def ClauseAndClausePos.format (c : Clause × ClausePos) : MessageData :=
  m!"({c.1}, {c.2})"

instance : ToMessageData (Clause × ClausePos) := ⟨ClauseAndClausePos.format⟩

end Clause
