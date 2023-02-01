import Lean
import Duper.HOUnif.UnifProblem
import Duper.Util.LazyList
import Duper.Util.Misc
open Lean
open Duper

namespace HOUnif

-- TODOs
-- 1: How do we deal with `forall`?
-- 2: Do we unify the types?

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
        let e' ← Meta.mkLambdaFVars (xs ++ xs') body
        return (e', true)
      else
        let body' := mkAppN fni args
        dnrec xs body'
    else
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
  return {rigidrigid := rigidrigid', flexrigid := flexrigid', flexflex := flexflex', checked := true}

--  This function takes caure of `Delete`, `Fail` and `Decompose`
-- Assumming both sides of p are flex
-- If the head is unequal and number of arguments are equal, return `none`
-- If the head is equal and number of arguments are equal, return `none`
def unifyRigidRigid (p : UnifEq) : MetaM (Option (Array (Expr × Expr))) := do
  -- Rule: Delete
  if p.lhs == p.rhs then
    return some #[]
  Meta.lambdaTelescope p.lhs fun xs lhs' => do
    if p.lflex then
      trace[Meta.debug] "unifyRigidRigid :: lhs is nominally flex"
    if p.rflex then
      trace[Meta.debug] "unifyRigidRigid :: rhs is nominally flex"
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
-- Bool : Unifiable or not
abbrev UnifRuleResult := SumN [Array (MetaM UnifProblem), LazyList (MetaM UnifProblem), MetaM Bool]

def applyRule (mp : MetaM UnifProblem) : MetaM UnifRuleResult := do
  let mut p ← mp
  if ¬ p.checked then
    p ← derefNormProblem p
  if let some (eq, p') := p.pop? then
    -- Fail, Delete, Decompose
    if ¬ eq.lflex ∧ ¬ eq.rflex then
      let urr ← unifyRigidRigid eq
      -- Head equal, one unification problem generated
      if let some eqs := urr then
        return Sum3.mk1 #[mp *> pure (p'.appendUnchecked (eqs.map fun (l, r) => UnifEq.fromExpr l r))]
      else
        return Sum3.mk3 <| mp *> pure false
    -- Bind
    else
      sorry
  else
    return Sum3.mk3 <| mp *> pure true