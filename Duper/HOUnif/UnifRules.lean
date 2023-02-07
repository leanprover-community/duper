import Lean
import Duper.HOUnif.UnifProblem
import Duper.HOUnif.Bindings
import Duper.Util.LazyList
import Duper.Util.Misc
open Lean
open Duper

namespace HOUnif

-- TODO
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
  Meta.lambdaTelescope e fun xs t => Meta.forallTelescope t fun ys b => do
    let h := Expr.getAppFn b
    if h.isFVar then
      let mut bound := false
      for x in xs ++ ys do
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

partial def derefNormType (e : Expr) (xs : Array Expr := #[]) : MetaM (Expr × Bool) :=
  Meta.forallTelescope e fun xs' body => do
    let body := body.headBeta
    let fn := Expr.getAppFn body
    if let .mvar _ := fn then
      let args := Expr.getAppArgs body
      let fni ← instantiateMVars fn
      if let .mvar _ := fni then
        let body' := mkAppN fni args
        let e' ← Meta.mkForallFVars (xs ++ xs') body'
        return (e', true)
      else
        let body' := mkAppN fni args
        derefNormType body' (xs ++ xs')
    else
      let body ← Meta.etaExpand body
      let e' ← Meta.mkForallFVars (xs ++ xs') body
      return (e', false)

-- Dereference head and normalize
-- Return: (processed expression, is_flex)
partial def derefNormTerm (e : Expr) (xs : Array Expr := #[]) : MetaM (Expr × Bool) :=
  Meta.lambdaTelescope e fun xs' body => do
    let body := body.headBeta
    let fn := Expr.getAppFn body
    match fn with
    | .mvar _ => do
      let args := Expr.getAppArgs body
      let fni ← instantiateMVars fn
      if let .mvar _ := fni then
        let body' ← Meta.etaExpand (mkAppN fni args)
        let e' ← Meta.mkLambdaFVars (xs ++ xs') body'
        return (e', true)
      else
        let body' ← Meta.etaExpand (mkAppN fni args)
        derefNormTerm body' (xs ++ xs')
    | .forallE _ _ _ _  => do
      -- type can't be applied
      if body.getAppArgs.size != 0 then
        trace[Meta.debug] "Type {fn} is applied to arguments in {body}"
      let (body, flex) ← derefNormType fn
      let e' ← Meta.mkLambdaFVars (xs ++ xs') body
      return (e', flex)
    | _ => do
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
-- Assumming both sides of `eq` are rigid, or both sides of `eq` are flex
-- If the head is unequal and number of arguments are equal, return `none`
-- If the head is equal and number of arguments are equal, return `none`
def failDecompose (p : UnifProblem) (eq : UnifEq) : MetaM (Array UnifProblem) := do
  Meta.lambdaTelescope eq.lhs fun xs t => Meta.forallTelescope t fun ts lhs' => do
    -- apply the right-hand-side to `xs`
    let n_lam := Expr.countLambdas eq.rhs
    let n_red := Nat.min n_lam xs.size
    let rhs_red ← Meta.instantiateLambda eq.rhs (xs.extract 0 n_red)
    let mut rhs' := mkAppN rhs_red (xs.extract n_red xs.size)
    if ts.size != 0 then
      if n_lam != xs.size then
        return #[]
      let n_forall := Expr.countForalls rhs'
      if n_forall != ts.size then
        return #[]
      rhs' ← Meta.instantiateForall rhs' ts
    -- Rule: Fail
    if lhs'.isApp != rhs'.isApp then
      return #[]
    let fl := lhs'.getAppFn
    let fr := rhs'.getAppFn
    -- Rule: Fail
    if fl != fr then
      return #[]
    let argsl := lhs'.getAppArgs
    let argsr := rhs'.getAppArgs
    -- This can happen in, for example,
    -- U : ∀ α, α → α
    -- U Nat 1
    -- U (Nat → Nat) (fun x => x) 1
    if argsl.size != argsr.size then
      return #[]
    let argsl ← (← argsl.mapM (Meta.mkForallFVars ts)).mapM (Meta.mkLambdaFVars xs)
    let argsr ← (← argsr.mapM (Meta.mkForallFVars ts)).mapM (Meta.mkLambdaFVars xs)
    let neweqs := (argsl.zip argsr).map (fun (a, b) => UnifEq.fromExprPair a b)
    return #[(p.appendUnchecked neweqs).pushParentRule (.Decompose eq)]

-- MetaM : mvar assignments
-- LazyList UnifProblem : unification problems being generated
-- Bool : True -> Succeed, False -> Fail
-- TODO : Use inductive datatype
inductive UnifRuleResult
| NewArray : Array UnifProblem → UnifRuleResult
| NewLazyList : LazyList (MetaM (Array UnifProblem)) → UnifRuleResult
| Succeed : UnifRuleResult

-- Rules are run inside `applyRules` without `withoutModifyingMCtx`,
-- so `applyRules` should be run with `withoutModifyingMCtx`
def applyRules (p : UnifProblem) : MetaM UnifRuleResult := do
  -- To make messages print, we set `mctx` to that of `p`'s
  setMCtx p.mctx
  let mut p := p
  if ¬ p.checked ∨ p.isActiveEmpty then
    p ← derefNormProblem p
  -- debug
  if p.parentClauses.toList.contains 116 then
    trace[Meta.debug] m!"{(← p.instantiateTrackedExpr).dropParentRulesButLast 8}"
  if let some (eq, p') := p.pop? then
    let (lh, lhtype) ← headInfo eq.lhs
    let (rh, rhtype) ← headInfo eq.rhs
    if lhtype == .Other then
      trace[Meta.debug] m!"applyRule :: Type `{lhtype}` of head `{lh}` of `{eq.lhs}` is `Other`"
      return .NewArray #[]
    if rhtype == .Other then
      trace[Meta.debug] m!"applyRule :: Type `{rhtype}` of head `{rh}` of `{eq.rhs}` is `Other`"
      return .NewArray #[]
    if eq.lflex != lhtype.isFlex then
      trace[Meta.debug] m!"applyRule :: Flex-rigid-cache mismatch in lhs of {eq}"
      return .NewArray #[]
    if eq.rflex != rhtype.isFlex then
      trace[Meta.debug] m!"applyRule :: Flex-rigid-cache mismatch in rhs of {eq}"
      return .NewArray #[]
    -- Delete
    if eq.lhs == eq.rhs then
      let p' := p'.pushParentRule (.Delete eq)
      return .NewArray #[p']
    -- Fail, Decompose
    -- If head type are both rigid
    if ¬ eq.lflex ∧ ¬ eq.rflex then
      let urr ← failDecompose p' eq
      return .NewArray urr
    -- Following: Bind
    -- Left flex, Right rigid
    if eq.lflex ∧ ¬ eq.rflex then
      let mut ret := #[]
      if rhtype == .Const then
        ret := ret.append (← HOUnif.imitation lh rh p' eq)
      if ¬ p.identVar.contains lh then
        ret := ret.append (← HOUnif.huetProjection lh p' eq)
      return .NewArray ret
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
      return .NewLazyList (.cons (pure arr) iter)
    -- Left flex, Right flex
    -- Heads are the same
    else
      let decomp ← failDecompose p' eq
      if p.elimVar.contains lh then
        return .NewArray decomp
      -- Iteration at arguments of functional type
      let iters ← HOUnif.iteration lh p' eq true
      -- Eliminations
      let elims ← HOUnif.elimination lh p' eq
      return .NewLazyList (LazyList.cons (pure decomp) (LazyList.interleave elims iters))
  else
    -- No problems left
    return .Succeed



-- Unifier Generator

inductive QueueElement
| Problem : UnifProblem → QueueElement
| LazyListOfProblem : LazyList (MetaM (Array UnifProblem)) → QueueElement
deriving Inhabited

structure UnifierGenerator where
  q : Std.Queue QueueElement
  -- Total number of problems generated
  -- This will be used to assign ids to clauses
  N : Nat

def UnifierGenerator.fromExprPair (e1 e2 : Expr) : MetaM UnifierGenerator := do
  let q := Std.Queue.empty
  let unifPrb ← UnifProblem.fromExprPair e1 e2
  if let some prb := unifPrb then
    -- debug
    let prb := {prb.pushParentClause 0 with trackedExpr := #[e1, e2]}
    return ⟨q.enqueue (.Problem prb), 1⟩
  else
    return ⟨q, 0⟩

def UnifierGenerator.isEmpty : UnifierGenerator → Bool
| .mk q _ => q.isEmpty

def UnifierGenerator.take (ug : UnifierGenerator) : MetaM (Option MetavarContext × UnifierGenerator) := do
  let q := ug.q
  let dq := q.dequeue?
  if dq.isNone then
    return (none, ug)
  let (top, q') := dq.get!
  match top with
  | .Problem up => do
    let urr ← withoutModifyingMCtx <| applyRules up
    match urr with
    -- arr : Array UnifProblem
    | .NewArray arr => do
      let mut q' := q'
      let mut cnt := 0
      for a in arr do
        q' := q'.enqueue (.Problem (a.pushParentClause (ug.N + cnt)))
        cnt := cnt + 1
      return (none, ⟨q', ug.N + arr.size⟩)
    -- ls : LazyList (MetaM (Array UnifProblem))
    | .NewLazyList ls => pure (none, ⟨q'.enqueue (.LazyListOfProblem ls), ug.N⟩)
    -- b : Bool
    | .Succeed => return (some up.mctx, ⟨q', ug.N⟩)
  | .LazyListOfProblem ls =>
    match ls with
    | .cons arr ls' => do
      let mut q' := q'
      q' := q'.enqueue (.LazyListOfProblem ls')
      let arr ← withoutModifyingMCtx arr
      let mut cnt := 0
      for a in arr do
        q' := q'.enqueue (.Problem (a.pushParentClause (ug.N + cnt)))
        cnt := cnt + 1
      return (none, ⟨q', ug.N + arr.size⟩)
    | .nil => pure (none, ⟨q', ug.N⟩)
    | .delayed t => pure (none, ⟨q'.enqueue (.LazyListOfProblem t.get), ug.N⟩)