import Lean
import Duper.HOUnif.UnifProblem
import Duper.HOUnif.Bindings
import Duper.Util.LazyList
import Duper.Util.Misc
open Lean
open Duper

namespace HOUnif

-- TODO
-- 1: How do we deal with `forall`?
-- 2: Do we unify the types?
-- 3: How to deal with `mdata`?
-- 4: How to deal with `let`?
-- 5: Find out whether we need to consider metavariables of
--    different depth to be rigid. (Anyway, we need to prevent
--    us from assigning the metavariables that are assumed to
--    be synthesized by typeclass resolution. It seems that
--    `Elab.Term.synthesizeSyntheticMVarsNoPostponing` might help?)
-- 6: Whether it's safe to proceed with term unification
--    when type unification is not finished.
-- 7: Will `ListT` (Haskell "ListT done right") provide a more
--    elegant way of modelling monadic nondeterminism?
-- 8: Currently only `huetProjection` and `imitation` deals with metavariables correctly

inductive HeadType where
  -- Things considered as `const`:
  -- 1. constants
  -- 2. free variables
  -- 3. metavariables not of current depth
  -- 4. literals
  | Const : HeadType
  | Bound : HeadType
  | MVar  : HeadType
  -- Currently, `mdata`, `forall`, `let`
  | Other : HeadType
  deriving Hashable, Inhabited, BEq, Repr

instance : ToString HeadType where
  toString (ht : HeadType) : String :=
  match ht with
  | .Const => "HeadType.Const"
  | .Bound => "HeadType.Bound"
  | .MVar  => "HeadType.MVar"
  | .Other => "HeadType.Other"

def HeadType.isFlex : HeadType → Bool
| Const => false
| Bound => false
| MVar => true
| Other => false

def HeadType.isRigid : HeadType → Bool
| Const => true
| Bound => true
| MVar => false
| Other => false

def headInfo (e : Expr) : MetaM (Expr × HeadType) :=
  Meta.lambdaTelescope e fun xs b => do
    let h := Expr.getAppFn b
    if h.isFVar then
      let mut bound := false
      for x in xs do
        if x == h then
          bound := true
      if bound then
        return (h, .Bound)
      else
        return (h, .Const)
    else if h.isConst ∨ h.isSort ∨ h.isLit then
      return (h, .Const)
    else if h.isMVar then
      let decl := (← getMCtx).getDecl h.mvarId!
      if decl.depth != (← getMCtx).depth then
        return (h, .Const)
      else
        return (h, .MVar)
    else
      return (h, .Other)

-- Dereference head and normalize
-- Return: (processed expression, is_flex)
-- TODO 1
partial def derefNormTerm (e : Expr) : MetaM (Expr × Bool) := dnrec #[] e
  where dnrec xs body : MetaM (Expr × Bool) := Meta.lambdaTelescope body fun xs' body => do
    let body := body.headBeta
    let fn := Expr.getAppFn body
    if let .mvar _ := fn then
      let args := Expr.getAppArgs body
      let fni ← instantiateMVars fn
      if let .mvar _ := fni then
        let body' ← Meta.etaExpand (mkAppN fni args)
        let e' ← Meta.mkLambdaFVars (xs ++ xs') body'
        return (e', true)
      else
        let body' ← Meta.etaExpand (mkAppN fni args)
        dnrec (xs ++ xs') body'
    else
      let body ← Meta.etaExpand body
      let e' ← Meta.mkLambdaFVars (xs ++ xs') body
      return (e', false)

def derefNormEq (u : UnifEq) : MetaM UnifEq := do
  let mut lhs' := u.lhs
  let mut lflex' := u.lflex
  if u.lflex then
    let n ← derefNormTerm u.lhs
    lhs' := n.fst
    lflex' := n.snd
  let mut rhs' := u.rhs
  let mut rflex' := u.rflex
  if u.rflex then
    let n ← derefNormTerm u.rhs
    rhs' := n.fst
    rflex' := n.snd
  -- avoid left-rigid right-flex
  if ¬ lflex' ∧ rflex' then
    return {lhs := rhs', lflex := rflex', rhs := lhs', rflex := lflex'}
  else 
    return {lhs := lhs', lflex := lflex', rhs := rhs', rflex := rflex'}

def derefNormProblem (p : UnifProblem) : MetaM UnifProblem := withoutModifyingMCtx <| do
  setMCtx p.mctx
  let mut p := p
  if p.isActiveEmpty then
    p := {p with flexflex := p.postponed, postponed := #[], checked := false}
  if p.checked then
    return p
  let mut rigidrigid' := p.rigidrigid
  let checked ← (p.flexrigid ++ p.flexflex).mapM derefNormEq
  let mut flexrigid' := #[]
  let mut flexflex' := #[]
  for c in checked do
    if ¬ c.lflex ∧ ¬ c.rflex then
      rigidrigid' := rigidrigid'.push c
    else if c.lflex ∧ ¬ c.rflex then
      flexrigid' := flexrigid'.push c
    else
      flexflex' := flexflex'.push c
  return {p with rigidrigid := rigidrigid', flexrigid := flexrigid', flexflex := flexflex',
                 checked := true, mctx := ← getMCtx}

-- This function takes care of `Delete`, `Fail` and `Decompose`
-- Assumming both sides of p are flex
-- If the head is unequal and number of arguments are equal, return `none`
-- If the head is equal and number of arguments are equal, return `none`
def unifyRigidRigid (p : UnifEq) : MetaM (Option (Array (Expr × Expr) × ParentRule)) := do
  -- Rule: Delete
  if p.lhs == p.rhs then
    return some (#[], .Delete p)
  Meta.lambdaTelescope p.lhs fun xs lhs' => do
    -- apply the right-hand-side to `xs`
    -- TODO 1
    let rhs' ← (do
      let n_lam := Expr.countLambdas p.rhs
      let n_red := Nat.min n_lam xs.size
      let rhs_red ← Meta.instantiateLambda p.rhs (xs.extract 0 n_red)
      return mkAppN rhs_red (xs.extract n_red xs.size))
    -- Rule: Fail
    if lhs'.isApp != rhs'.isApp then
      return none
    let fl := lhs'.getAppFn
    let fr := rhs'.getAppFn
    -- TODO: Check whether they're actually rigid
    -- Rule: Fail
    if fl != fr then
      return none
    let argsl := lhs'.getAppArgs
    let argsr := rhs'.getAppArgs
    if argsl.size != argsr.size then
      trace[Meta.debug] "unifyRigidRigid :: Head equal but number of args unequal"
    -- Rule: Decompose
    let argsl ← argsl.mapM (Meta.mkLambdaFVars xs)
    let argsr ← argsr.mapM (Meta.mkLambdaFVars xs)
    return some (argsl.zip argsr, .Decompose p)

-- MetaM : mvar assignments
-- LazyList UnifProblem : unification problems being generated
-- Bool : True -> Succeed, False -> Fail
abbrev UnifRuleResult := SumN [Array UnifProblem, LazyList (MetaM (Array UnifProblem)), Bool]

-- Rules are run inside `applyRules` without `withoutModifyingMCtx`,
-- so `applyRules` should be run with `withoutModifyingMCtx`
def applyRules (p : UnifProblem) : MetaM UnifRuleResult := do
  -- To make messages print, we set `mctx` to that of `p`'s
  setMCtx p.mctx
  let mut p := p
  if ¬ p.checked ∨ p.isActiveEmpty then
    p ← derefNormProblem p
  -- debug
  trace[Meta.debug] m!"{(← p.instantiateTrackedExpr).dropParentRulesButLast 5}"
  if let some (eq, p') := p.pop? then
    let (lh, lhtype) ← headInfo eq.lhs
    let (rh, rhtype) ← headInfo eq.rhs
    if lhtype == .Other then
      trace[Meta.debug] m!"applyRule :: Type `{lhtype}` of head `{lh}` of `{eq.lhs}` is `Other`"
      return Sum3.mk3 false
    if rhtype == .Other then
      trace[Meta.debug] m!"applyRule :: Type `{rhtype}` of head `{rh}` of `{eq.rhs}` is `Other`"
      return Sum3.mk3 false
    if eq.lflex != lhtype.isFlex then
      trace[Meta.debug] m!"applyRule :: Flex-rigid-cache mismatch in lhs of {eq}"
      return Sum3.mk3 false
    if eq.rflex != rhtype.isFlex then
      trace[Meta.debug] m!"applyRule :: Flex-rigid-cache mismatch in rhs of {eq}"
      return Sum3.mk3 false
    -- Delete
    if eq.lhs == eq.rhs then
      let p' := p'.pushParentRule (.Delete eq)
      return Sum3.mk1 #[p']
    -- Fail, Delete, Decompose
    -- If head type are both rigid
    if ¬ eq.lflex ∧ ¬ eq.rflex then
      let urr ← unifyRigidRigid eq
      -- Head equal, one unification problem generated
      if let some (eqs, prule) := urr then
        return Sum3.mk1 #[(p'.pushParentRule prule).appendUnchecked
                            (eqs.map fun (l, r) => UnifEq.fromExprPair l r)]
      else
        -- Not unifiable
        return Sum3.mk3 false
    -- Following: Bind
    -- Left flex, Right rigid
    if eq.lflex ∧ ¬ eq.rflex then
      let mut ret := #[]
      if rhtype == .Const then
        ret := ret.append (← HOUnif.imitation lh rh p' eq)
      if ¬ p.identVar.contains lh then
        ret := ret.append (← HOUnif.huetProjection lh p' eq)
      return Sum3.mk1 ret
    -- Left flex, Right flex
    -- Heads are different
    if lh != rh then
      -- Iteration for both lhs and rhs
      let liter ← HOUnif.iteration lh p' eq false
      let riter ← HOUnif.iteration rh p' eq false
      let iter := LazyList.interleave liter riter
      -- Identification
      let mut arr ← HOUnif.identification lh rh p' eq
      -- JP style projection
      if ¬ p.identVar.contains lh then
        arr := arr.append (← HOUnif.jpProjection lh p' eq)
      if ¬ p.identVar.contains rh then
        arr := arr.append (← HOUnif.jpProjection rh p' eq)
      return Sum3.mk2 (.cons (pure arr) iter)
    -- Left flex, Right flex
    -- Heads are the same
    else
      if p.elimVar.contains lh then
        return Sum3.mk1 #[]
      -- Iteration at arguments of functional type
      let iters ← HOUnif.iteration lh p' eq true
      -- Eliminations
      let elims ← HOUnif.elimination lh p' eq
      return Sum3.mk2 (LazyList.interleave elims iters)
  else
    -- No problems left
    -- debug
    trace[Meta.debug] m!"{p}"
    return Sum3.mk3 true



-- Unifier Generator

structure UnifierGenerator where
  q : Std.Queue (UnifProblem ⊕ LazyList (MetaM (Array UnifProblem)))

def UnifierGenerator.fromExprPair (e1 e2 : Expr) : MetaM UnifierGenerator := do
  let q := Std.Queue.empty
  let unifPrb ← UnifProblem.fromExprPair e1 e2
  if let some prb := unifPrb then
    -- debug
    let prb := {prb with trackedExpr := #[e1, e2]}
    return ⟨q.enqueue (.inl prb)⟩
  else
    return ⟨q⟩

def UnifierGenerator.isEmpty : UnifierGenerator → Bool
| .mk q => q.isEmpty

def UnifierGenerator.take (ug : UnifierGenerator) : MetaM (Option MetavarContext × UnifierGenerator) := do
  let q := ug.q
  let dq := q.dequeue?
  if dq.isNone then
    return (none, ⟨q⟩)
  let (top, q') := dq.get!
  match top with
  | .inl up => do
    let urr ← withoutModifyingMCtx <| applyRules up
    match urr with
    -- arr : Array UnifProblem
    | .inl arr => do
      let mut q' := q'
      for a in arr do
        q' := q'.enqueue (.inl a)
      return (none, ⟨q'⟩)
    -- ls : LazyList (MetaM (Array UnifProblem))
    | .inr (.inl ls) => pure (none, ⟨q'.enqueue (.inr ls)⟩)
    -- b : Bool
    | .inr (.inr (.inl b)) =>
      if (b : Bool) then
        return (some up.mctx, ⟨q'⟩)
      else
        return (none, ⟨q'⟩)
  | .inr ls =>
    match ls with
    | .cons arr ls' => do
      let mut q' := q'
      q' := q'.enqueue (.inr ls')
      for a in (← withoutModifyingMCtx arr) do
        q' := q'.enqueue (.inl a)
      return (none, ⟨q'⟩)
    | .nil => pure (none, ⟨q'⟩)
    | .delayed t => pure (none, ⟨q'.enqueue (.inr t.get)⟩)