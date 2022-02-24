
import LeanHammer.Clause

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

end MClause
end Duper