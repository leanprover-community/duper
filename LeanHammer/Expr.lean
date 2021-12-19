import Lean

namespace Lean.Expr

def foldGreenM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → m β) (init : β) (e : Expr) : m β  := do
  let mut acc ← f init e
  match e with
  | Expr.app _ arg _ => foldGreenM f acc arg
  | _ => acc

end Lean.Expr