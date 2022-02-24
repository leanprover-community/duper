

import Lean

open Lean
open Lean.Meta

inductive Iter₀ (α : Type u)
| nil : Iter₀ α
| cons (a : α) (next : Unit → Iter₀ α) : Iter₀ α
deriving Inhabited

def Iter (α : Type u) := Unit → Iter₀ α

namespace Iter

def nil : Iter α := fun () => Iter₀.nil

instance : Inhabited (Iter α) := ⟨nil⟩

def cons (a : α) (next : Iter α) : Iter α := fun () => Iter₀.cons a next


def head? (i : Iter α) : Option α :=
match i () with
| Iter₀.nil => none
| Iter₀.cons a next => some a

def tail? (i : Iter α) : Option (Iter α) :=
match i () with
| Iter₀.nil => none
| Iter₀.cons a next => some next

partial def toList (i : Iter α) : List α :=
match i () with
| Iter₀.nil => []
| Iter₀.cons a next => a :: toList next

def take (n : Nat) (i : Iter α) : Iter α :=
  match n with
  | 0 => Iter.nil
  | n + 1 => fun () =>
    match i () with
    | Iter₀.nil => Iter₀.nil
    | Iter₀.cons a next => Iter₀.cons a (take n next)

partial def concat (i : Iter α) (j : Iter α) : Iter α :=
  match i () with
  | Iter₀.nil => j
  | Iter₀.cons a next => cons a (concat next j)

partial def bind (i : Iter α) (f : α → Iter β) : Iter β :=
  match i () with
  | Iter₀.nil => Iter.nil
  | Iter₀.cons a next => concat (f a) (bind next f)

instance : Monad Iter := {
  pure := fun a => cons a nil
  bind := bind
}

end Iter


partial def test (a : Nat) : Iter Nat :=
  Iter.cons a (test (a + 1))

#eval (Iter.take 5 (test 0)).toList



def unify (cs : List (Expr × Expr)) (subst : FVarSubst) : Iter FVarSubst :=
  if cs.isEmpty then pure subst else Iter.nil