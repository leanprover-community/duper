import Lean
import Duper.HOUnif.UnifRules
open Lean

namespace HOUnif

def hounif (e1 e2 : Expr) (nAttempt : Nat) (nUnif : Nat) : MetaM Bool := do
  let mut ug ← UnifierGenerator.fromExprPair e1 e2
  let mut cnt := 0
  for _ in List.range nAttempt do
    let (mctx, ug') ← ug.take
    ug := ug'
    if let some m := mctx then
      if cnt == nUnif then
        setMCtx m
        return true
      else
        cnt := cnt + 1
  return false

-- Note: This is copied from standard library with some code
--       removed to make it simpler and a few lines changed to
--       allow for higher-order unification

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
  Meta.throwTacticEx `apply mvarId m!"failed to unify{indentExpr eType}\nwith{indentExpr targetType}"

/--
Close the given goal using `apply e`.
-/
def exechoapply (mvarId : MVarId) (e : Expr) (nAttempt : Nat) (nUnif : Nat) (cfg : Meta.ApplyConfig := {}) : MetaM (List MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `apply
    let targetType ← mvarId.getType
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
        if (← hounif eType targetType nAttempt nUnif) then
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
    for mvarId in (← Meta.getMVarsNoDelayed targetType) do
      if !otherMVarIds.contains mvarId then
        otherMVarIds := otherMVarIds.push mvarId
    let newMVarIds := (newMVars.map (·.mvarId!)).data
    otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result
termination_by go i => rangeNumArgs.stop - i

syntax (name := hoapply) "hoapply " term " attempt " num "unifier " num: tactic

@[tactic hoapply]
def evalHoApply : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| hoapply $e attempt $nAttempt unifier $nunif) => Elab.Tactic.withMainContext do
    let mut val ← instantiateMVars (← Elab.Tactic.elabTermForApply e)
    if val.isMVar then
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← exechoapply (← Elab.Tactic.getMainGoal) val nAttempt.getNat nunif.getNat
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    Elab.Tactic.replaceMainGoal mvarIds'
  | _ => Elab.throwUnsupportedSyntax


def test₁ (f : Nat → Prop)
         (h : ∀ x y (z : Nat), f z → f (x + y))
         (k : f 0) : f (3 + b) := by
  hoapply h attempt 30 unifier 0
  case a => hoapply h attempt 70 unifier 0; exact 0; apply k; exact 0; exact 0

def test₂ (f : Nat → Prop)
          (comm : ∀ x y, f (x + y) → f (y + x))
          (h : ∀ x y z, f (x + z) → f (x + y))
          (g : f (u + v))
          : f (a + b) := by
  hoapply h attempt 30 unifier 0
  case a =>
    hoapply comm attempt 42 unifier 0; hoapply h attempt 42 unifier 0
    case a.a => apply g

def test₃ (ftr : ∀ (f g : Nat → Prop) (x : Nat), f x → g x)
          (atr : ∀ (f : Nat → Prop) (x y : Nat), f x → f y)
          (S T : Nat → Prop) (u v : Nat)
          (h   : S u) : T v := by
  hoapply ftr attempt 100 unifier 1
  case a => hoapply h attempt 10 unifier 0

def ho₁ (p : Nat → Prop) (x y : Nat)
        (hp : ∀ (f : Nat → Nat → Nat), p (f x y) ∧ p (f y x))
        : p x ∧ p y := by
  hoapply hp attempt 11 unifier 0

def ho₂ (p : Nat → Prop) (x y : Nat)
        (hp : ∀ (f : Nat → Nat → Nat), p (f x y) ∧ p (f y x))
        : p (x + y) ∧ p (y + x) := by
  hoapply hp attempt 300 unifier 0