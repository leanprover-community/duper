import Duper.Clause

namespace Duper
open Lean

/-
  Note on the invariant expected of mvars: Immediately after loading a clause, it is expected
  that the resulting mclause's mvars field contains one mvar for each bVarType of the original clause,
  regardless of whether the corresponding bvar appears in the clause. However, when an mclause is
  constructed as the conclusion of an inference rule, we only require that:
  - All mvars from the mvars fields of the parent mclauses are included in the conclusion's mvars field
  - Any new mvars that do not appear in the actual mclause (i.e. that do not appear anywhere in lits) are included

  This means that it is fine if a conclusion's mclause contains new mvars that are not included in the mvars
  field so long as they appear somewhere in the lits field. The invariant that matters when an mclause is yielded
  is that all mvars appear either in the mvars field or in the lits field (since in neutralizeMClause, every
  mvar that appears in lits or mvars will be abstracted and therefore correctly accounted for)
-/
structure MClause :=
(lits : Array Lit)
(mvars : Array Expr) -- An array of every mvar that could appear in lits (even if not all of them do)
deriving Inhabited, BEq, Hashable

namespace MClause

def toExpr (c : MClause) : Expr :=
  litsToExpr c.lits.data
where litsToExpr : List Lit → Expr
| [] => mkConst ``False
| [l] => l.toExpr
| l :: ls => mkApp2 (mkConst ``Or) l.toExpr (litsToExpr ls)

def fromExpr (e : Expr) (mvars : Array Expr) : MClause :=
  MClause.mk (litsFromExpr e).toArray mvars
where   litsFromExpr : Expr → List Lit
| .app (.app (.const ``Or _) litexpr) other => Lit.fromExpr litexpr :: litsFromExpr other
| .const ``False _                            => []
| e@(_)                                       => [Lit.fromExpr e]

def appendLits (c : MClause) (mvars : Array Expr) (lits : Array Lit) : MClause :=
  ⟨c.lits.append lits, mvars⟩

def eraseLit (c : MClause) (idx : Nat) : MClause :=
  ⟨c.lits.eraseIdx idx, c.mvars⟩

def replaceLit? (c : MClause) (mvars : Array Expr) (idx : Nat) (l : Lit) : Option MClause :=
  if idx >= c.lits.size then
    none
  else
    some ⟨c.lits.set! idx l, mvars⟩

def replaceLit! (c : MClause) (mvars : Array Expr) (idx : Nat) (l : Lit) : MClause :=
  ⟨c.lits.set! idx l, mvars⟩

def map (f : Expr → Expr) (c : MClause) : MClause :=
  ⟨c.lits.map (fun l => l.map f), c.mvars⟩

def mapWithPos (f : Expr → Expr × Array ExprPos) (c : MClause) : MClause × Array ClausePos :=
  let mapres := c.lits.map (fun l => l.mapWithPos f)
  let c' := ⟨mapres.map (fun x => x.fst), c.mvars⟩
  let cps := mapres.mapIdx (fun i x => x.snd.map (fun p => ClausePos.mk i p.side p.pos))
  (c', cps.concatMap id)

def mapM {m : Type → Type w} [Monad m] (f : Expr → m Expr) (c : MClause) : m MClause := do
  return ⟨← c.lits.mapM (fun l => l.mapM f), c.mvars⟩

def fold {β : Type v} (f : β → Expr → β) (init : β) (c : MClause) : β := Id.run $ do
  let mut acc := init
  for i in [:c.lits.size] do
    let f' := fun acc e => f acc e
    acc := c.lits[i]!.fold f' acc
  return acc

def foldM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → ClausePos → m β) (init : β) (c : MClause) : m β := do
  let mut acc := init
  for i in [:c.lits.size] do
    let f' := fun acc e pos => f acc e ⟨i, pos.side, pos.pos⟩
    acc ← c.lits[i]!.foldM f' acc
  return acc

def foldGreenM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → ClausePos → m β) (init : β) (c : MClause) : m β := do
  let mut acc := init
  for i in [:c.lits.size] do
    let f' := fun acc e pos => f acc e ⟨i, pos.side, pos.pos⟩
    acc ← c.lits[i]!.foldGreenM f' acc
  return acc

def getAtPos! (c : MClause) (pos : ClausePos) : Expr :=
  c.lits[pos.lit]!.getAtPos! ⟨pos.side, pos.pos⟩

def replaceAtPos? (c : MClause) (mvars : Array Expr) (pos : ClausePos) (replacement : Expr) : Option MClause :=
  if (pos.lit ≥ c.lits.size) then none
  else
    let litPos : LitPos := {side := pos.side, pos := pos.pos}
    match c.lits[pos.lit]!.replaceAtPos? litPos replacement with
    | some newLit => some {lits := Array.set! c.lits pos.lit newLit, mvars := mvars}
    | none => none

def replaceAtPos! (c : MClause) (mvars : Array Expr) (pos : ClausePos) (replacement : Expr) [Monad m] [MonadError m]
  : m MClause := do
  let litPos : LitPos := {side := pos.side, pos := pos.pos}
  let replacedLit ← c.lits[pos.lit]!.replaceAtPos! litPos replacement
  return {
      lits := Array.set! c.lits pos.lit $ replacedLit,
      mvars := mvars
    }

def replaceAtPosUpdateType? (c : MClause) (mvars : Array Expr) (pos : ClausePos) (replacement : Expr) : MetaM (Option MClause) := do
  let litPos : LitPos := {side := pos.side, pos := pos.pos}
  if let some replacedLit ← c.lits[pos.lit]!.replaceAtPosUpdateType? litPos replacement then
    return some {
      lits := Array.set! c.lits pos.lit $ replacedLit,
      mvars := mvars
    }
  else
    return none

/-- This function acts as Meta.kabstract except that it takes a ClausePos rather than Occurrences and expects
    the given expression to consist only of applications up to the given ExprPos. Additionally, since the exact
    position is given, we don't need to pass in Meta.kabstract's second argument p -/
def abstractAtPos! (c : MClause) (pos : ClausePos) : MetaM MClause := do
  let litPos : LitPos := {side := pos.side, pos := pos.pos}
  return {
      lits := Array.set! c.lits pos.lit $ ← c.lits[pos.lit]!.abstractAtPos! litPos,
      mvars := c.mvars
    }

def append (c : MClause) (d : MClause) : MClause := ⟨c.lits.append d.lits, c.mvars ++ d.mvars⟩

def eraseIdx (i : Nat) (c : MClause) : MClause := ⟨c.lits.eraseIdx i, c.mvars⟩

def isTrivial (c : MClause) : Bool := Id.run do
  -- TODO: Also check if it contains the same literal positively and negatively?
  for lit in c.lits do
    if lit.sign ∧ lit.lhs == lit.rhs then
      return true
  return false

open Comparison
def isMaximalLit (ord : Expr → Expr → MetaM Comparison) (c : MClause) (idx : Nat) (strict := false) : MetaM Bool := do
  for j in [:c.lits.size] do
    if j == idx then continue
    let c ← Lit.compare ord c.lits[idx]! c.lits[j]!
    if c == GreaterThan || (not strict && c == Equal) || c == Incomparable
      then continue
    else return false
  return true

/-- Returns true if there may be some assignment in which the given idx is maximal, and false if there is some idx' that is strictly greater
    than idx (in this case, since idx < idx', for any subsitution σ, idx σ < idx' σ so idx can never be maximal)

    Note that for this function, strictness does not actually matter, because regardless of whether we are considering potential strict maximality
    or potential nonstrict maximality, we can only determine that idx can never be maximal if we find an idx' that is strictly gerater than it
-/
def canNeverBeMaximal (ord : Expr → Expr → MetaM Comparison) (c : MClause) (idx : Nat) : MetaM Bool := do
  for j in [:c.lits.size] do
    if j != idx && (← Lit.compare ord c.lits[idx]! c.lits[j]!) == LessThan then
      return true
    else continue
  return false

end MClause
end Duper