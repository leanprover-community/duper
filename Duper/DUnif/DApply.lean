import Lean
import Duper.DUnif.UnifRules
open Lean

namespace DUnif

-- Note: This is copied from standard library with some code
--       removed to make it simpler and a few lines changed to
--       allow for higher-order unification

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
  Meta.throwTacticEx `apply mvarId m!"failed to unify{indentExpr eType}\nwith{indentExpr targetType}"

/--
Close the given goal using `apply e`.
-/
def execdapply (mvarId : MVarId) (e : Expr) (nAttempt : Nat) (nUnif : Nat) (cont : Nat) (cfg : Meta.ApplyConfig := {}) : MetaM (List MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `apply
    let targetType ← mvarId.getType
    let targetMVars ← Meta.getMVarsNoDelayed targetType
    let eType      ← Meta.inferType e
    let (numArgs, hasMVarHead) ← Meta.getExpectedNumArgsAux eType
    /-
    The `apply` tactic adds `_`s to `e`, and some of these `_`s become new goals.
    When `hasMVarHead` is `false` we try different numbers, until we find a type compatible with `targetType`.
    We used to try only `numArgs-targetTypeNumArgs` when `hasMVarHead = false`, but this is not always correct.
    For example, consider the following example
    ```
    example {α β} [LE_trans β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
      apply le_trans
      assumption
      assumption
    ```
    In this example, `targetTypeNumArgs = 1` because `LE` for functions is defined as
    ```
    instance {α : Type u} {β : Type v} [LE β] : LE (α → β) where
      le f g := ∀ i, f i ≤ g i
    ```
    -/
    let rangeNumArgs ← if hasMVarHead then
      pure [numArgs : numArgs+1]
    else
      let targetTypeNumArgs ← Meta.getExpectedNumArgs targetType
      pure [numArgs - targetTypeNumArgs : numArgs+1]
    /-
    Auxiliary function for trying to add `n` underscores where `n ∈ [i: rangeNumArgs.stop)`
    See comment above
    -/
    let rec go (i : Nat) : MetaM (Array Expr × Array BinderInfo) := do
      if i < rangeNumArgs.stop then
        let s ← saveState
        let (newMVars, binderInfos, eType) ← Meta.forallMetaTelescopeReducing eType i
        if (← hounif eType targetType nAttempt nUnif cont true) then
          return (newMVars, binderInfos)
        else
          s.restore
          go (i+1)
      else
        let (_, _, eType) ← Meta.forallMetaTelescopeReducing eType (some rangeNumArgs.start)
        throwApplyError mvarId eType targetType
    let (newMVars, binderInfos) ← go rangeNumArgs.start
    Meta.postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    -- Collect other mvars
    let mut otherMVarIds ← Meta.getMVarsNoDelayed e
    for m in targetMVars do
      for mvarId in (← Meta.getMVarsNoDelayed (.mvar m)) do
        if !otherMVarIds.contains mvarId then
          otherMVarIds := otherMVarIds.push mvarId
    let newMVarIds := (newMVars.map (·.mvarId!)).data
    otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    trace[Meta.Tactic] "{result}"
    result.forM (·.headBetaType)
    return result
termination_by go i => rangeNumArgs.stop - i

syntax (name := dapply) "dapply " term " attempt " num "unifier " num "contains" num : tactic

@[tactic dapply]
def evaldapply : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| dapply $e attempt $nAttempt unifier $nunif contains $cont) => Elab.Tactic.withMainContext do
    let mut val ← instantiateMVars (← Elab.Tactic.elabTermForApply e)
    if val.isMVar then
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← execdapply (← Elab.Tactic.getMainGoal) val nAttempt.getNat nunif.getNat cont.getNat
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    Elab.Tactic.replaceMainGoal mvarIds'
  | _ => Elab.throwUnsupportedSyntax

-- whnf test
def wh₁ : Nat := 3

set_option trace.Meta.Tactic true in
def wh₀ (f : Nat → Prop) (h : ∀ x, f x) : f wh₁ :=
  by dapply h attempt 5 unifier 0 contains 0

-- Imitation
set_option trace.DUnif.debug true in
def imt₀ (f : Nat → Prop) (h : ∀ x, f x) : f 3 :=
  by dapply h attempt 30 unifier 0 contains 0

def imt₁ (f : Nat → Prop)
         (h : ∀ x y (z : Nat), f z → f (x + y))
         (k : f 0) : f (3 + b) := by
  dapply h attempt 30 unifier 0 contains 0
  case a => dapply h attempt 70 unifier 0 contains 0;
            case a => apply k;
            exact 0; exact 0

def imt₂ (f : Nat → Prop)
          (comm : ∀ x y, f (x + y) → f (y + x))
          (h : ∀ x y z, f (x + z) → f (x + y))
          (g : f (u + v))
          : f (a + b) := by
  dapply h attempt 30 unifier 0 contains 0
  case a =>
    dapply comm attempt 42 unifier 0 contains 0;
    case a => dapply h attempt 42 unifier 0 contains 0;
              case a => dapply g attempt 42 unifier 0 contains 0

-- Huet-Style Projection
def hsp₁ (ftr : ∀ (f g : Nat → Prop) (x : Nat), f x → g x)
          (S T : Nat → Prop) (u v : Nat)
          (h   : S u) : T v := by
  dapply ftr attempt 100 unifier 1 contains 0
  case a => dapply h attempt 10 unifier 0 contains 0

def hsp₂ (p : Nat → Prop) (x y : Nat)
        (hp : ∀ (f : Nat → Nat → Nat), p (f x y) ∧ p (f y x))
        : p x ∧ p y := by
  dapply hp attempt 11 unifier 0 contains 0

def hsp₃ (p : Nat → Prop) (x y : Nat)
        (hp : ∀ (f : Nat → Nat → Nat), p (f x y) ∧ p (f y x))
        : p (x + y) ∧ p (y + x) := by
  dapply hp attempt 300 unifier 0 contains 0

def hsp₄ (done : Prop)
         (gene : ∀ (H : (Nat → Nat) → Nat → Nat), (fun F X => H F X) = (fun F X => F X) → done) :
         done := by
  dapply gene attempt 10 unifier 0 contains 0
  case a => dapply Eq.refl attempt 70 unifier 0 contains 0;

opaque www : Nat → Nat → Nat := fun _ _ => 1
opaque ww : Nat → Nat := id
opaque w : Nat

-- Elimination
def elm₁ (p : Nat → Prop) 
         (a b : Nat) (h : ∀ (f : Nat → Nat → Nat), p (f a b))
         (g : ∀ (ay : Nat), p ay → False)
         : False := by
  dapply g attempt 10 unifier 0 contains 0
  case a => dapply h attempt 590 unifier 0 contains 0; exact www

#print elm₁.proof_1

-- Identification
def idt₁ (p : Nat → Prop) (x : Nat)
         (hp : ∀ (f g : Nat → Nat), p (f (g x)) ∧ p (g (f x)))
         (done : Prop)
         (hq : ∀ w, p w ∧ p w → done) : done := by
  dapply hq attempt 10 unifier 0 contains 0
  case a => dapply hp attempt 10000 unifier 700 contains 0; exact www

#print idt₁.proof_1

-- Negative tests
def neg₁ (h : True) : False :=
  by dapply h attempt 10 unifier 0 contains 0