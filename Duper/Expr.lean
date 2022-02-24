import Lean


namespace Duper

-- TODO: add to Lean?
instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

/-- Positions in an expression: Counting argument numbers form the right
  e.g. `a` is at #[1] and `b` is at #[0] in `f a b` -/
def ExprPos := Array Nat
deriving Inhabited, BEq, Hashable

namespace ExprPos

protected def empty : ExprPos := #[]

end ExprPos

end Duper

namespace Lean.Expr
open Duper

partial def foldGreenM {β : Type v} [Inhabited β] {m : Type v → Type w} [Monad m] 
    (f : β → Expr → ExprPos → m β) (init : β) (e : Expr)
    (pos : ExprPos := ExprPos.empty) : m β  := do
  let mut acc ← f init e pos
  let args := e.getAppRevArgs
  for i in [:args.size] do
    acc ← foldGreenM f acc args[i] (pos := pos.push i)
  return acc

partial def getAtPos! (e : Expr) (pos : ExprPos) (startIndex := 0): Expr :=
  if pos.size ≤ startIndex
  then e
  else 
    getAtPos! (e.getRevArg! pos[startIndex]) pos (startIndex := startIndex + 1)

end Lean.Expr
