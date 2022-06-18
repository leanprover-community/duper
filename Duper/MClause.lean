
import Duper.Clause

namespace Duper
open Lean

structure MClause :=
(lits : Array Lit)
deriving Inhabited, BEq, Hashable

namespace MClause

def appendLits (c : MClause) (lits : Array Lit) : MClause :=
  ⟨c.lits.append lits⟩

def eraseLit (c : MClause) (idx : Nat) : MClause :=
  ⟨c.lits.eraseIdx idx⟩

def mapM {m : Type → Type w} [Monad m] (f : Expr → m Expr) (c : MClause) : m MClause := do
  return ⟨← c.lits.mapM (fun l => l.mapM f)⟩

def foldM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → ClausePos → m β) (init : β) (c : MClause) : m β := do
  let mut acc := init
  for i in [:c.lits.size] do
    let f' := fun acc e pos => f acc e ⟨i, pos.side, pos.pos⟩
    acc ← c.lits[i].foldM f' acc
  return acc

def foldGreenM {β : Type v} [Inhabited β] {m : Type v → Type w} [Monad m] 
    (f : β → Expr → ClausePos → m β) (init : β) (c : MClause) : m β := do
  let mut acc := init
  for i in [:c.lits.size] do
    let f' := fun acc e pos => f acc e ⟨i, pos.side, pos.pos⟩
    acc ← c.lits[i].foldGreenM f' acc
  return acc

def getAtPos! (c : MClause) (pos : ClausePos) : Expr :=
  c.lits[pos.lit].getAtPos! ⟨pos.side, pos.pos⟩

def append (c : MClause) (d : MClause) : MClause := ⟨c.lits.append d.lits⟩

def eraseIdx (i : Nat) (c : MClause) : MClause := ⟨c.lits.eraseIdx i⟩

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
    let c ← Lit.compare ord c.lits[idx] c.lits[j]
    if c == GreaterThan ∨ (¬ strict ∧ c == Equal)
      then continue
    else return false
  return true

/-- Determines if idx is a maximal literal in the given clause c among the list of indices given -/
def isMaximalInSubClause (ord : Expr → Expr → MetaM Comparison) (c : MClause) (subclause : List Nat) (idx : Nat) (strict := false) : MetaM Bool := do
  if(not (subclause.contains idx)) then
    return false -- idx cannot be a maximal literal in c among the list of indices given because idx is not among the list of indices given
  for j in subclause do
    if j == idx then continue
    let c ← Lit.compare ord c.lits[idx] c.lits[j]
    if c == GreaterThan || (not strict && c == Equal)
      then continue
    else return false
  return true

end MClause
end Duper