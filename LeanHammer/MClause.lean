
import LeanHammer.Clause
import LeanHammer.RuleM

open Lean
open RuleM

structure MClause :=
(lits : Array Lit)
deriving Inhabited, BEq, Hashable

namespace MClause

def fromClause (c : Clause) : RuleM MClause := do
  let mVars ← c.bVarTypes.mapM fun ty => mkFreshExprMVar (some ty)
  let lits := c.lits.map fun l =>
    l.map fun e => e.instantiate mVars
  return MClause.mk lits

def toClause (c : MClause) : RuleM Clause := do
  let mVarIds := c.lits.foldl (fun acc l =>
    l.fold (fun acc e => acc.append (e.collectMVars {}).result) acc) #[]
  let lits := c.lits.map fun l =>
    l.map fun e => e.abstractMVars (mVarIds.map mkMVar)
  return Clause.mk (← mVarIds.mapM getMVarType) lits

def appendLits (c : MClause) (lits : Array Lit) : MClause :=
  ⟨c.lits.append lits⟩

def eraseLit (c : MClause) (idx : Nat) : MClause :=
  ⟨c.lits.eraseIdx idx⟩

def mapM {m : Type → Type w} [Monad m] (f : Expr → m Expr) (c : MClause) : m MClause := do
  return ⟨← c.lits.mapM (fun l => l.mapM f)⟩

def foldM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → m β) (init : β) (c : MClause) (type := false) : m β := do
  c.lits.foldlM (fun b lit => lit.foldM f b (type := type)) init

end MClause