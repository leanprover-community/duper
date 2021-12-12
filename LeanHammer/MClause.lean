
import LeanHammer.Clause

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
    (f : β → Expr → m β) (init : β) (c : MClause) (type := false) : m β := do
  c.lits.foldlM (fun b lit => lit.foldM f b (type := type)) init

def append (c : MClause) (d : MClause) : MClause := ⟨c.lits.append d.lits⟩

def eraseIdx (i : Nat) (c : MClause) : MClause := ⟨c.lits.eraseIdx i⟩

end MClause