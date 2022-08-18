import Lean

namespace Duper

-- TODO: add to Lean?
instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

/-- Positions in an expression: Counting argument numbers form the right
  e.g. `a` is at #[1] and `b` is at #[0] in `f a b` -/
abbrev ExprPos := Array Nat

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
    acc ← foldGreenM f acc args[i]! (pos := pos.push i)
  return acc

partial def getAtPos! (e : Expr) (pos : ExprPos) (startIndex := 0) : Expr :=
  if pos.size ≤ startIndex then e
  else getAtPos! (e.getRevArg! pos[startIndex]!) pos (startIndex := startIndex + 1)

/-- Attempts to put replacement at pos in e. Returns some res if successful, and returns none otherwise -/
private partial def replaceAtPosHelper (e : Expr) (pos : List Nat) (replacement : Expr) : Option Expr :=
  match pos with
  | List.nil => replacement
  | List.cons 0 restPos =>
    match consumeMData e with
    | Expr.app e1 e2 =>
      match replaceAtPosHelper e2 restPos replacement with
      | some e2' => some (Expr.app e1 e2')
      | none => none
    | _ => replaceAtPosHelper e restPos replacement
  | List.cons (i + 1) restPos =>
    match consumeMData e with
    | Expr.app e1 e2 =>
      match replaceAtPosHelper e1 (i :: restPos) replacement with
      | some e1' => some (Expr.app e1' e2)
      | none => none
    | _ => none

/-- Attempts to put replacement at pos in e. Returns some res if successful, and returns none otherwise -/
partial def replaceAtPos? (e : Expr) (pos : ExprPos) (replacement : Expr) : Option Expr :=
  replaceAtPosHelper e pos.data replacement

/-- Attempts to put replacement at pos in e. Returns the result if successful and throws and error otherwise -/
partial def replaceAtPos! (e : Expr) (pos : ExprPos) (replacement : Expr) [Monad m] [MonadError m] : m Expr := do
  match replaceAtPosHelper e pos.data replacement with
  | some res => return res
  | none => throwError "replaceAtPos error: Invalid position {pos} given for expression {e}"

/-- An incomplete implementation of Meta.kabstract that uses and ExprPos list to indicate position rather than
    Occurrences. abstractAtPosHelper! assumes that e consists only of applications up to the given ExprPos.
    Implementing abstractAtPosHelper! as "replaceAtPos! e pos (mkBVar 0)" doesn't work because of how
    Lean.Expr.updateApp! and Lean.Expr.updateMData! work. -/
private partial def abstractAtPosHelper! (e : Expr) (pos : List Nat) : MetaM Expr :=
  match pos with
  | List.nil => pure (mkBVar 0)
  | List.cons 0 restPos =>
    match e with
    | Expr.app f a => return e.updateApp! f (← abstractAtPosHelper! a restPos)
    | Expr.mdata _ b => return e.updateMData! (← abstractAtPosHelper! b pos)
    | e => pure (mkBVar 0)
  | List.cons (i + 1) restPos =>
    match e with
    | Expr.app f a => return e.updateApp! (← abstractAtPosHelper! f (i :: restPos)) a
    | Expr.mdata _ b => return e.updateMData! (← abstractAtPosHelper! b pos)
    | _ => throwError "Invalid position {pos} for expression {e} given to abstractAtPos"

/-- This function acts as Meta.kabstract except that it takes an ExprPos rather than Occurrences and expects
    the given expression to consist only of applications up to the given ExprPos. Additionally, since the exact
    ExprPos is given, we don't need to pass in Meta.kabstract's second argument p -/
partial def abstractAtPos! (e : Expr) (pos : ExprPos) : MetaM Expr := do
  abstractAtPosHelper! e pos.data

end Lean.Expr
