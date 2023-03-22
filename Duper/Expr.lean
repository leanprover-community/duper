import Lean

namespace Duper

/-- Positions in an expression: Counting argument numbers from the right
  e.g. `a` is at #[1] and `b` is at #[0] in `f a b`. If the head is an implication
  (an expression of the form `∀ _ : p, q` where `p` and `q` have type `Prop`) then
  we treat `p` and `q` as arguments passed to a hypothetical implication symbol. -/
abbrev ExprPos := Array Nat

namespace ExprPos

protected def empty : ExprPos := #[]

end ExprPos

end Duper

namespace Lean.Expr
open Duper

-- To support universe levels, we strip universe levels to allow fingerprint
-- function to identify constants with uninstantiated universe levels
def stripLevels : Expr → Expr
| .const name _ => .const name []
| .app fn arg => .app (stripLevels fn) (stripLevels arg)
| .lam name ty b info => .lam name (stripLevels ty) (stripLevels b) info
| .forallE name ty b info => .forallE name (stripLevels ty) (stripLevels b) info
| .letE name ty v b nd => .letE name (stripLevels ty) (stripLevels v) (stripLevels b) nd
| .mdata data e => .mdata data (stripLevels e)
| .proj name idx struct => .proj name idx (stripLevels struct)
| e => e

/-- Given `t` and `b`, determines whether `.forallE _ t b _` is an implication -/
private def expIsImplication (t : Expr) (b : Expr) : MetaM Bool :=
  try
    if (← Meta.inferType t).isProp && (← Meta.inferType b).isProp then return true
    else return false
  catch _ => -- If either of the inferType checks fail (e.g. because `b` has loose bvars), then return false
    return false

private def impAwareGetAppRevArgsAux : Expr → Array Expr → MetaM (Array Expr)
  | app f a, as => impAwareGetAppRevArgsAux f (as.push a)
  | forallE _ t b _, as => do
    if (← expIsImplication t b) then return (as.push b).push t
    else return as
  | _, as => return as

/-- Same as `Lean.Expr.getAppRevArgs` but if the head is an implication (an expression of the form
    `∀ _ : p, q` where `p` and `q` have type `Prop`), then it pretends the head has the form
    `.app (.app impSymbol p) q` -/
def impAwareGetAppRevArgs (e : Expr) : MetaM (Array Expr) :=
  impAwareGetAppRevArgsAux e (Array.mkEmpty e.getAppNumArgs)

/-- Same as `Lean.Expr.getAppArgs` but if the head is an implication (an expression of the form
    `∀ _ : p, q` where `p` and `q` have type `Prop`), then it pretends the head has the form
    `.app (.app impSymbol p) q` -/
def impAwareGetAppArgs (e : Expr) : MetaM (Array Expr) := do
  let revArgs ← impAwareGetAppRevArgs e
  return revArgs.reverse

/-- Note: This function assumes that if the head is a forallE expression and the index given indicates
    either the type or body of the forallE expression, then the head is actually an implication (in other
    words, this function does not check whether the head a valid implication as opposed to an arbitrary
    forallE expression) -/
def impAwareGetRevArg! : Expr → Nat → Expr
  | app _ a, 0   => a
  | app f _, i+1 => impAwareGetRevArg! f i
  | forallE _ _ b _, 0 => b
  | forallE _ t _ _, 1 => t
  | e, i => panic! s!"invalid index {i} given to impAwareGetRevArg! for expression {e}"

partial def foldGreenM {β : Type} [Monad m] [MonadLiftT MetaM m]
  (f : β → Expr → ExprPos → m β) (init : β) (e : Expr)
  (pos : ExprPos := ExprPos.empty) (_ : Inhabited β := ⟨init⟩) : m β :=
  do
    let mut acc ← f init e pos
    let args ← e.impAwareGetAppRevArgs
    for i in [:args.size] do
      acc ← foldGreenM f acc args[i]! (pos := pos.push i)
    return acc

partial def getAtPos! [Monad m] [MonadLiftT MetaM m] (e : Expr) (pos : ExprPos) : m Expr := do
  let mut cur := e
  for i in pos do
    cur := cur.impAwareGetRevArg! i
  return cur

/-- Returns the expression in e indiced by pos if it exists, and returns none if pos does not point to a valid
    subexpression in e -/
partial def getAtPos? [Monad m] [MonadLiftT MetaM m] (e : Expr) (pos : ExprPos) : m (Option Expr) := do
  let mut cur := e
  for i in pos do
    let impAwareRevArgs ← cur.impAwareGetAppRevArgs
    match impAwareRevArgs[i]? with
    | some e => cur := e
    | none => return none
  return cur

/-- Returns true if either the subexpression indiced by pos exists in e, or if it may be possible to instantiate metavariables in
    e in such a way that the subexpression indiced by pos would exist.

    For example, if e = "f 2 ?m.0", then canInstantiateToGetAtPos would return true for pos #[0, 1] (becuase "?m.0" could be instantiated
    as an application) but would return false for pos #[1, 1] (because 2 does not and can not have any arguments) -/
partial def canInstantiateToGetAtPos [Monad m] [MonadLiftT MetaM m] (e : Expr) (pos : ExprPos) (startIndex := 0) : m Bool :=
  if e.isMVar then return true
  else if pos.size ≤ startIndex then return true
  else do
    let e'_opt := (← e.impAwareGetAppRevArgs)[pos[startIndex]!]?
    match e'_opt with
    | none => return false
    | some e' => canInstantiateToGetAtPos e' pos (startIndex := startIndex + 1)

partial def getTopSymbol (e : Expr) : Expr :=
  match e.consumeMData with
  | app f _ => getTopSymbol f
  | _ => e

/-- Attempts to put replacement at pos in e. Returns some res if successful, and returns none otherwise -/
private partial def replaceAtPosHelper [Monad m] [MonadLiftT MetaM m] (e : Expr) (pos : List Nat) (replacement : Expr) : m (Option Expr) :=
  match pos with
  | List.nil => return replacement
  | List.cons 0 restPos => do
    match consumeMData e with
    | Expr.app e1 e2 =>
      match ← replaceAtPosHelper e2 restPos replacement with
      | some e2' => return some (Expr.app e1 e2')
      | none => return none
    | Expr.forallE name t b bi =>
      if (← expIsImplication t b) then
        match ← replaceAtPosHelper b restPos replacement with
        | some b' => return some (Expr.forallE name t b' bi)
        | none => return none
      else -- If the head is not an implication, then position 0 refers to all of e in this instance
        replaceAtPosHelper e restPos replacement
    | _ => replaceAtPosHelper e restPos replacement
  | List.cons (i + 1) restPos => do
    match consumeMData e with
    | Expr.app e1 e2 =>
      match ← replaceAtPosHelper e1 (i :: restPos) replacement with
      | some e1' => return some (Expr.app e1' e2)
      | none => return none
    | Expr.forallE name t b bi =>
      if i != 0 then return none -- If i > 0 then the position is impossible
      else -- i+1 is 1 so the position refers to `t` (assuming `e` is a valid implication)
        if (← expIsImplication t b) then
          match ← replaceAtPosHelper t restPos replacement with
          | some t' => return some (Expr.forallE name t' b bi)
          | none => return none
        else return none -- If the head is not an implication, then the position is impossible
    | _ => return none

/-- Attempts to put replacement at pos in e. Returns some res if successful, and returns none otherwise -/
partial def replaceAtPos? [Monad m] [MonadLiftT MetaM m] (e : Expr) (pos : ExprPos) (replacement : Expr) : m (Option Expr) :=
  replaceAtPosHelper e pos.data replacement

/-- Attempts to put replacement at pos in e. Returns the result if successful and throws and error otherwise -/
partial def replaceAtPos! [Monad m] [MonadLiftT MetaM m] [MonadError m] (e : Expr) (pos : ExprPos) (replacement : Expr) : m Expr := do
  match ← replaceAtPosHelper e pos.data replacement with
  | some res => return res
  | none => throwError "replaceAtPos error: Invalid position {pos} given for expression {e}"

private partial def replaceGreenWithPosHelper [Monad m] [MonadLiftT MetaM m] (t₁ t₂ e : Expr) : m (Expr × (Array ExprPos)) :=
  if e == t₁ then return (t₂, #[#[]])
  else do
    match e with
    | .mdata _ b =>
      let (b, ps) ← replaceGreenWithPosHelper t₁ t₂ b
      return (e.updateMData! b, ps)
    | .app _ _ =>
      let f := e.getAppFn
      let fcon := f.consumeMData
      if fcon.isBVar || fcon.isFVar || fcon.isConst || fcon.isSort then
        let rets ← (← e.impAwareGetAppArgs).mapM (fun x => replaceGreenWithPosHelper t₁ t₂ x)
        let len := rets.size
        let args := rets.map (fun x => x.fst)
        let poses := rets.mapIdx (fun i poses => poses.snd.map (fun pos => pos.push (len - 1 - i)))
        return (mkAppN f args, poses.concatMap id)
      else
        return (e, #[])
    | .forallE name t b bi =>
      if (← expIsImplication t b) then
        let (b', bPoses) ← replaceGreenWithPosHelper t₁ t₂ b
        let (t', tPoses) ← replaceGreenWithPosHelper t₁ t₂ t
        let bPoses := bPoses.push #[0]
        let tPoses := tPoses.push #[1]
        return (.forallE name t' b' bi, tPoses.append bPoses)
      else
        return (e, #[])
    | e => return (e, #[])

-- Return [t₂/t₁]e, along with positions where the green subterm is replaced
partial def replaceGreenWithPos [Monad m] [MonadLiftT MetaM m] (t₁ t₂ e : Expr) : m (Expr × (Array ExprPos)) := do
  let (e, poses) ← replaceGreenWithPosHelper t₁ t₂ e
  return (e, poses.map (fun x => x.reverse))

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
    Lean.Expr.updateApp! and Lean.Expr.updateMData! work.

    Note: The numBindersUnder field is designed to ensure that if the rhs of an implication is abstracted, the correct
    bvar is used (if bvar #0 is used naively to replace `q` in `p → q`, then `p → q` which is `∀ _ : p, q` would be
    transformed into `∀ a : p, a` rather than `∀ _ : p, #1` as desired)-/
private partial def abstractAtPosHelper! [Monad m] [MonadLiftT MetaM m] [MonadError m] (e : Expr) (pos : List Nat)
  (numBindersUnder : Nat) : m Expr :=
  match pos with
  | List.nil => pure (mkBVar numBindersUnder)
  | List.cons 0 restPos =>
    match e with
    | Expr.app f a => return e.updateApp! f (← abstractAtPosHelper! a restPos numBindersUnder)
    | Expr.mdata _ b => return e.updateMData! (← abstractAtPosHelper! b pos numBindersUnder)
    | Expr.forallE name t b bi => do
      if (← expIsImplication t b) then return .forallE name t (← abstractAtPosHelper! b restPos (numBindersUnder + 1)) bi
      else pure (mkBVar numBindersUnder)
    | e => pure (mkBVar numBindersUnder)
  | List.cons (i + 1) restPos =>
    match e with
    | Expr.app f a => return e.updateApp! (← abstractAtPosHelper! f (i :: restPos) numBindersUnder) a
    | Expr.mdata _ b => return e.updateMData! (← abstractAtPosHelper! b pos numBindersUnder)
    | Expr.forallE name t b bi => do
      if i == 0  && (← expIsImplication t b) then return .forallE name (← abstractAtPosHelper! t restPos numBindersUnder) b bi
      else throwError "Invalid position {pos} for expression {e} given to abstractAtPos"
    | _ => throwError "Invalid position {pos} for expression {e} given to abstractAtPos"

/-- This function acts as Meta.kabstract except that it takes an ExprPos rather than Occurrences and expects
    the given expression to consist only of applications up to the given ExprPos. Additionally, since the exact
    ExprPos is given, we don't need to pass in Meta.kabstract's second argument p -/
partial def abstractAtPos! [Monad m] [MonadLiftT MetaM m] [MonadError m] (e : Expr) (pos : ExprPos) : m Expr := do
  abstractAtPosHelper! e pos.data 0

private partial def abstractAtPosesHelper! [Monad m] [MonadLiftT MetaM m] [MonadError m] (e : Expr)
  (poses : Array (List Nat)) (numBindersUnder : Nat) : m Expr := do
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
      | .nil => return (mkBVar numBindersUnder)
      | List.cons i restPos =>
        if i >= len then
          panic! s!"abstractAtPosesHelper :: Index {i} greater or equal to length {len}"
        poseses := poseses.set! (len - 1 - i) (poseses[len - 1 - i]!.push restPos)
    let args' ← (args.zip poseses).mapM (fun (e, poses) => abstractAtPosesHelper! e poses numBindersUnder)
    return mkAppN fn args'
  | .mdata _ e' =>
    let e'' ← abstractAtPosesHelper! e' poses numBindersUnder
    return e'.updateMData! e''
  | Expr.forallE name t b bi => do
    if (← expIsImplication t b) then
      let mut bPoses := #[]
      let mut tPoses := #[]
      for pos in poses do
        match pos with
        | List.nil => return (mkBVar numBindersUnder)
        | i :: restPos =>
          if i == 0 then bPoses := bPoses.push restPos
          else if i == 1 then tPoses := tPoses.push restPos
          else throwError "abstractAtPosesHelper :: Invalid position {pos} for expression {e} given to abstractAtPos"
      let b' ← abstractAtPosesHelper! b bPoses numBindersUnder
      let t' ← abstractAtPosesHelper! t tPoses (numBindersUnder + 1)
      return .forallE name t' b' bi
    else
      for pos in poses do
        match pos with
        | .nil => return (mkBVar numBindersUnder)
        | List.cons .. => throwError "abstractAtPosesHelper :: Invalid position {pos} for expression {e} given to abstractAtPos"
      return e
  | _ => do
    for pos in poses do
      match pos with
      | .nil => return (mkBVar numBindersUnder)
      | List.cons .. => throwError "abstractAtPosesHelper :: Invalid position {pos} for expression {e} given to abstractAtPos"
    return e

partial def abstractAtPoses! [Monad m] [MonadLiftT MetaM m] [MonadError m] (e : Expr) (poses : Array ExprPos) : m Expr :=
  abstractAtPosesHelper! e (poses.map (fun x => x.data)) 0

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
def expressionsAgreeExceptAtPos [Monad m] [MonadLiftT MetaM m] (e1 : Expr) (e2 : Expr) (p : ExprPos) : m Bool := do
  -- e1 and e2 are identical except potentially at p iff e1 is identical with (replaceAtPos e2 pos (getAtPos e1 pos))
  match ← e1.getAtPos? p with
  | none => return false
  | some e1Subterm =>
    match ← e2.replaceAtPos? p e1Subterm with
    | none => return false
    | some e2Replaced => return e1 == e2Replaced

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
