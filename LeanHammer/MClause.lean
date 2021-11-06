import LeanHammer.Clause

open Lean
open Meta

structure MClause :=
(lits : Array Lit)
deriving Inhabited, BEq, Hashable

namespace MClause

def fromClause (c : Clause) : MetaM MClause := do
  let mVars ← c.bVarTypes.mapM fun ty => mkFreshExprMVar (some ty)
  let lits := c.lits.map fun l =>
    l.map fun e => e.instantiate mVars
  return MClause.mk lits

def toClause (c : MClause) : MetaM Clause := do
  let mVarIds := c.lits.foldl (fun acc l =>
    l.foldl (fun acc e => (e.collectMVars {}).result) acc) #[]
  let lits := c.lits.map fun l =>
    l.map fun e => e.abstractMVars (mVarIds.map mkMVar)
  return Clause.mk (← mVarIds.mapM getMVarType) lits

end MClause