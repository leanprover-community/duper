import Lean

open Lean
open Lean.Meta

partial def unify (l : Array (Expr × Expr)) (subst : FVarSubst) : MetaM (Option FVarSubst) := do
  match l.data with
  | [] => subst
  | (s, t) :: tail => do
    let subst ← unify1 t s subst
    return subst
where unify1 (s t : Expr) (subst : FVarSubst): MetaM (Option FVarSubst) := do
  if s == t then subst else
  s.withApp fun f ss => t.withApp fun g tt =>
    match f, g with
    | Expr.const .., Expr.const .. => do
      if f == g 
      then 
        if tt.size == ss.size
        then return ← unify (tt.zip ss) subst
        else return none
      else return none
    | Expr.fvar fVarId .., Expr.const .. =>
      match subst.find? fVarId with
      | some e => 
        unify1 (mkAppN e ss) t subst
      | none =>
        if ss.isEmpty 
        then 
          if t.containsFVar fVarId
          then none
          else subst.insert fVarId t
        else none
    | Expr.const .., Expr.fvar fVarId .. => 
      match subst.find? fVarId with
      | some e => 
        unify1 s (mkAppN e tt) subst
      | none =>
        if tt.isEmpty 
        then 
          if s.containsFVar fVarId
          then none
          else subst.insert fVarId s
        else none
    | Expr.fvar fVarId .., Expr.fvar .. =>
        if tt.isEmpty && ss.isEmpty
        then
          if f == g
          then subst
          else subst.insert fVarId t
        else none
    | _, _ => return none

partial def test : CoreM (FVarSubst) := do
  return {}

constant a : Nat
constant b : Nat
constant c : Nat
constant f : Nat → Nat

open Std

namespace Std.AssocList

  def toList : AssocList α β → List (α × β)
  | AssocList.nil => []
  | AssocList.cons a b rest => (a, b) :: toList rest

end Std.AssocList

instance [Repr α] [Repr β] : Repr (AssocList α β) where
  reprPrec a n := reprPrec a.toList n

instance [ToString α] : Repr α where
  reprPrec a n := toString a

instance : Repr FVarSubst where
  reprPrec s n := reprPrec s.map n

instance [ToMessageData α] [ToMessageData β] : ToMessageData (α × β) := 
⟨fun (a, b) => "(" ++ toMessageData a ++ ", " ++ toMessageData b ++ ")"⟩

instance [ToMessageData α] [ToMessageData β] : ToMessageData (AssocList α β) :=
⟨ fun s => toMessageData s.toList ⟩ 

instance : ToMessageData FVarId :=
⟨ fun id => id.name ⟩ 

instance : ToMessageData FVarSubst :=
⟨ fun s => toMessageData s.map ⟩ 

#eval unify #[(
  mkApp (mkConst `f) (mkFVar ⟨`z⟩), 
   mkApp (mkConst `f) (mkApp (mkConst `f) (mkFVar ⟨`x⟩)))
  ] {}
