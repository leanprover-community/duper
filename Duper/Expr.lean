import Lean

namespace Duper

/-- Positions in an expression: Counting argument numbers from the right
  e.g. `a` is at #[1] and `b` is at #[0] in `f a b` -/
abbrev ExprPos := Array Nat

namespace ExprPos

protected def empty : ExprPos := #[]

end ExprPos

end Duper

namespace Lean.Expr
open Duper

partial def foldGreenM {β : Type v} {m : Type v → Type w} [Monad m] 
    (f : β → Expr → ExprPos → m β) (init : β) (e : Expr)
    (pos : ExprPos := ExprPos.empty) (_ : Inhabited β := ⟨init⟩) : m β :=
  do
    let mut acc ← f init e pos
    let args := e.getAppRevArgs
    for i in [:args.size] do
      acc ← foldGreenM f acc args[i]! (pos := pos.push i)
    return acc

partial def getAtPos! (e : Expr) (pos : ExprPos) : Expr := Id.run <| do
  let mut cur := e
  for i in pos do
    cur := cur.getRevArg! i
  return cur

/-- Returns the expression in e indiced by pos if it exists, and returns none if pos does not point to a valid
    subexpression in e -/
partial def getAtPos? (e : Expr) (pos : ExprPos) : Option Expr := do
  let mut cur := e
  for i in pos do
    cur ← cur.getAppRevArgs[i]?
  return cur

/-- Returns true if either the subexpression indiced by pos exists in e, or if it may be possible to instantiate metavariables in
    e in such a way that the subexpression indiced by pos would exist.

    For example, if e = "f 2 ?m.0", then canInstantiateToGetAtPos would return true for pos #[0, 1] (becuase "?m.0" could be instantiated
    as an application) but would return false for pos #[1, 1] (because 2 does not and can not have any arguments) -/
partial def canInstantiateToGetAtPos (e : Expr) (pos : ExprPos) (startIndex := 0) : Bool :=
  if e.isMVar then true
  else if pos.size ≤ startIndex then true
  else
    let e'_opt := (e.getAppRevArgs)[pos[startIndex]!]?
    match e'_opt with
    | none => false
    | some e' => canInstantiateToGetAtPos e' pos (startIndex := startIndex + 1)

partial def getTopSymbol (e : Expr) : Expr :=
  match e.consumeMData with
  | app f _ => getTopSymbol f
  | _ => e

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

-- Return [t₂/t₁]e, along with positions where the green subterm is replaced
partial def replaceGreenWithPos (t₁ t₂ e : Expr) : Expr × (Array ExprPos) :=
  let (e, poses) := go e
  (e, poses.map (fun x => x.reverse))
where go e :=
  if e == t₁ then
    (t₂, #[#[]])
  else
    match e with
    | .mdata _ b       => let (b, ps) := go b; (e.updateMData! b, ps)
    | .app _ _         =>
      let f := e.getAppFn
      let fcon := f.consumeMData
      if fcon.isBVar || fcon.isFVar || fcon.isConst || fcon.isSort then
        let rets := e.getAppArgs.map go
        let len := rets.size
        let args := rets.map (fun x => x.fst)
        let poses := rets.mapIdx (fun i poses => poses.snd.map (fun pos => pos.push (len - 1 - i)))
        (mkAppN f args, poses.concatMap id)
      else
        (e, #[])
    | e                => (e, #[])

-- Return [t₂/t₁]e, along with positions where the term is replaced
-- TODO !!
partial def replaceWithPos (t₁ t₂ e : Expr) : Expr :=
  if e == t₁ then
    t₂
  else
    match e with
    | .forallE _ d b _ => let d := replaceWithPos t₁ t₂ d; let b := replaceWithPos t₁ t₂ b; e.updateForallE! d b
    | .lam _ d b _     => let d := replaceWithPos t₁ t₂ d; let b := replaceWithPos t₁ t₂ b; e.updateLambdaE! d b
    | .mdata _ b       => let b := replaceWithPos t₁ t₂ b; e.updateMData! b
    | .letE _ t v b _  => let t := replaceWithPos t₁ t₂ t; let v := replaceWithPos t₁ t₂ v; let b := replaceWithPos t₁ t₂ b; e.updateLet! t v b
    | .app f a         => let f := replaceWithPos t₁ t₂ f; let a := replaceWithPos t₁ t₂ a; e.updateApp! f a
    | .proj _ _ b      => let b := replaceWithPos t₁ t₂ b; e.updateProj! b
    | e                => e

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

private partial def abstractAtPosesHelper! (e : Expr) (poses : Array (List Nat)) : Id Expr := do
  if poses.size == 0 then
    return e
  match e with
  | e'@(.app ..) => do
    let fn := e'.getAppFn
    let args := e'.getAppArgs
    let len := args.size
    let mut poseses : Array (Array (List Nat)) := (Array.mk (List.range len)).map (fun _ => #[])
    for pos in poses do
      match pos with
      | .nil => return (mkBVar 0)
      | List.cons i restPos =>
        if i >= len then
          panic! s!"abstractAtPosesHelper :: Index {i} greater or equal to length {len}"
        poseses := poseses.set! (len - 1 - i) (poseses[len - 1 - i]!.push restPos)
    let args' ← (args.zip poseses).mapM (fun (e, poses) => abstractAtPosesHelper! e poses)
    return mkAppN fn args'
  | .mdata _ e' => let e'' := abstractAtPosesHelper! e' poses; return e'.updateMData! e''
  | _ => do
    for pos in poses do
      match pos with
      | .nil => return (mkBVar 0)
      | List.cons .. => panic! s!"abstractAtPosesHelper :: Invalid position {pos} for expression {e} given to abstractAtPos"
    return e

partial def abstractAtPoses! (e : Expr) (poses : Array ExprPos) : Expr :=
  Id.run <| abstractAtPosesHelper! e (poses.map (fun x => x.data))

/-
  Note: this function may require revision to be more similar to Zipperposition's ho_weight function once we actually
  start working on higher order things (https://github.com/sneeuwballen/zipperposition/blob/master/src/core/InnerTerm.ml#L240)
-/
def weight : Expr → Nat
  | Expr.bvar _          => 1
  | Expr.fvar _          => 1
  | Expr.mvar _          => 1
  | Expr.sort _          => 1
  | Expr.const _ _       => 1
  | Expr.app a b         => weight a + weight b
  | Expr.lam _ _ b _     => 1 + weight b
  | Expr.forallE _ _ b _ => 1 + weight b
  | Expr.letE _ _ v b _  => 1 + weight v + weight b
  | Expr.lit _           => 1
  | Expr.mdata _ b       => 1 + weight b
  | Expr.proj _ _ b      => 1 + weight b

/-- Returns true iff e1 and e2 are identical except potentially at position p. Returns false if p is not a valid position
    for either e1 or e2. -/
def expressionsAgreeExceptAtPos (e1 : Expr) (e2 : Expr) (p : ExprPos) : Bool :=
  -- e1 and e2 are identical except potentially at p iff e1 is identical with (replaceAtPos e2 pos (getAtPos e1 pos))
  match e1.getAtPos? p with
  | none => false
  | some e1Subterm =>
    match e2.replaceAtPos? p e1Subterm with
    | none => false
    | some e2Replaced => e1 == e2Replaced

/-- Returns true iff e is a fully applied logical symbol. The set of symbols we consider to be logical symbols are:
    ∧, ∨, →, ↔, ¬, True, False, ∀, ∃, =, and ≠ -/
def isFullyAppliedLogicalSymbol (e : Expr) : Bool :=
  match e.consumeMData with
  | Expr.const ``False _ => true
  | Expr.const ``True _ => true
  | Expr.app (Expr.const ``Not _) _ => true
  | Expr.app (Expr.app (Expr.const ``Exists _) _) _ => true
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _) _ => true
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _) _) _ => true
  | Expr.app (Expr.app (Expr.const ``And _) _) _ => true
  | Expr.app (Expr.app (Expr.const ``Or _) _) _ => true
  | Expr.app (Expr.app (Expr.const ``Iff _) _) _ => true
  | Expr.forallE _ _ _ _ => true
  | _ => false

end Lean.Expr
