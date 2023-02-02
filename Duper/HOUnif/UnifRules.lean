import Lean
import Duper.HOUnif.UnifProblem
import Duper.HOUnif.Bindings
import Duper.Util.LazyList
import Duper.Util.Misc
open Lean
open Duper

namespace HOUnif

-- TODOs
-- 1: How do we deal with `forall`?
-- 2: Do we unify the types?
-- 3: How to deal with `mdata`?
-- 4: How to deal with `let`?

inductive HeadType where
  -- Note : Unbound free variables are considered constant
  --        because of their role during unification
  | Const : HeadType
  | Bound : HeadType
  | MVar  : HeadType
  -- Currently, `mdata`, `forall`, `let`
  | Other : HeadType
  deriving Hashable, Inhabited, BEq

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
  Meta.forallTelescope e fun xs b => do
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
    else if h.isConst then
      return (h, .Const)
    else if h.isMVar then
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
        let body ← Meta.etaExpand body
        let e' ← Meta.mkLambdaFVars (xs ++ xs') body
        return (e', true)
      else
        let body' := mkAppN fni args
        dnrec xs body'
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

def derefNormProblem (p : UnifProblem) : MetaM UnifProblem := do
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
                 checked := true, state := ← saveState}

--  This function takes caure of `Delete`, `Fail` and `Decompose`
-- Assumming both sides of p are flex
-- If the head is unequal and number of arguments are equal, return `none`
-- If the head is equal and number of arguments are equal, return `none`
def unifyRigidRigid (p : UnifEq) : MetaM (Option (Array (Expr × Expr))) := do
  -- Rule: Delete
  if p.lhs == p.rhs then
    return some #[]
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
    return some (argsl.zip argsr)

-- MetaM : mvar assignments
-- LazyList UnifProblem : unification problems being generated
-- Bool : True -> Succeed, False -> Fail
abbrev UnifRuleResult := SumN [Array UnifProblem, LazyList (MetaM (Array UnifProblem)), Bool]

def applyRules (p : UnifProblem) : MetaM UnifRuleResult := do
  let mut p := p
  if ¬ p.checked then
    p ← derefNormProblem p
  if let some (eq, p') := p.pop? then
    let (lh, lhtype) ← headInfo eq.lhs
    let (rh, rhtype) ← headInfo eq.rhs
    if lhtype == .Other then
      trace[Meta.debug] s!"applyRule :: Head type of {eq.lhs} is `Other`"
      return Sum3.mk3 false
    if rhtype == .Other then
      trace[Meta.debug] s!"applyRule :: Head type of {eq.rhs} is `Other`"
      return Sum3.mk3 false
    if eq.lflex != lhtype.isFlex then
      trace[Meta.debug] s!"applyRule :: Flex-rigid-cache mismatch in lhs of {eq}"
      return Sum3.mk3 false
    if eq.rflex != rhtype.isFlex then
      trace[Meta.debug] s!"applyRule :: Flex-rigid-cache mismatch in rhs of {eq}"
      return Sum3.mk3 false
    -- Fail, Delete, Decompose
    -- If head type
    if ¬ eq.lflex ∧ ¬ eq.rflex then
      let urr ← unifyRigidRigid eq
      -- Head equal, one unification problem generated
      if let some eqs := urr then
        return Sum3.mk1 #[p'.appendUnchecked (eqs.map fun (l, r) => UnifEq.fromExprPair l r)]
      else
        -- Not unifiable
        return Sum3.mk3 false
    -- Following: Bind
    -- Left flex, Right rigid
    if eq.lflex ∧ ¬ eq.rflex then
      let mut ret := #[]
      if rhtype == .Const then
        ret := ret.append (← HOUnif.imitation lh rh p)
      if ¬ p.identVar.contains lh then
        ret := ret.append (← HOUnif.huetProjection lh p)
      return Sum3.mk1 ret
    -- Left flex, Right flex
    -- Heads are different
    if lh != rh then
      -- TODO: Iteration
      let mut arr ← HOUnif.identification lh rh p
      if ¬ p.identVar.contains lh then
        arr := arr.append (← HOUnif.jpProjection lh p)
      if ¬ p.identVar.contains rh then
        arr := arr.append (← HOUnif.jpProjection rh p)
      return Sum3.mk1 arr
    -- Left flex, Right flex
    -- Heads are the same
    else
      -- TODO: Iteration
      if p.elimVar.contains lh then
        return Sum3.mk1 #[]
      let elims ← HOUnif.elimination lh p
      return Sum3.mk2 elims
  else
    -- No problems left
    return Sum3.mk3 true



-- Unifier Generator

structure UnifierGenerator where
  q : Std.Queue (UnifProblem ⊕ LazyList (MetaM (Array UnifProblem)))

def UnifierGenerator.fromExprPair (e1 e2 : Expr) : MetaM UnifierGenerator := do
  let q := Std.Queue.empty
  let emptyProblem ← UnifProblem.empty
  let ty1 ← Meta.inferType e1
  let sort1 ← Meta.inferType ty1
  let ty2 ← Meta.inferType e2
  let sort2 ← Meta.inferType ty2
  -- TODO : Unify sort
  if sort1 != sort2 then
    return ⟨q⟩
  let unifTyEq := UnifEq.fromExprPair ty1 ty2
  let unifPrb := emptyProblem.pushUnchecked unifTyEq
  let unifEq := UnifEq.fromExprPair e1 e2
  let unifPrb := unifPrb.pushUnchecked unifEq
  return ⟨q.enqueue (.inl unifPrb)⟩

def UnifierGenerator.isEmpty : UnifierGenerator → Bool
| .mk q => q.isEmpty

def UnifierGenerator.take (ug : UnifierGenerator) : MetaM (Option Meta.SavedState × UnifierGenerator) := do
  let q := ug.q
  let dq := q.dequeue?
  if dq.isNone then
    return (none, ⟨q⟩)
  let (top, q') := dq.get!
  match top with
  | .inl up => do
    let urr ← applyRules up
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
        return (some up.state, ⟨q'⟩)
      else
        return (none, ⟨q'⟩)
  | .inr ls =>
    match ls with
    | .cons arr ls' => do
      let mut q' := q'
      q' := q'.enqueue (.inr ls')
      for a in (← arr) do
        q' := q'.enqueue (.inl a)
      return (none, ⟨q'⟩)
    | .nil => pure (none, ⟨q'⟩)
    | .delayed t => pure (none, ⟨q'.enqueue (.inr t.get)⟩)