import Lean
import Duper.HOUnif.UnifRules
open Lean

namespace HOUnif

def hounif (e1 e2 : Expr) (nAttempt : Nat) : MetaM Bool := do
  let mut ug ← UnifierGenerator.fromExprPair e1 e2
  for _ in List.range nAttempt do
    let (mctx, ug') ← ug.take
    ug := ug'
    if let some m := mctx then
      setMCtx m
      return true
  return false

-- Note: This is copied from standard library with some code
--       removed to make it simpler and a few lines changed to
--       allow for higher-order unification

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
  Meta.throwTacticEx `apply mvarId m!"failed to unify{indentExpr eType}\nwith{indentExpr targetType}"

/--
Close the given goal using `apply e`.
-/
def exechoapply (mvarId : MVarId) (e : Expr) (nAttempt : Nat) (cfg : Meta.ApplyConfig := {}) : MetaM (List MVarId) :=
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
        if (← hounif eType targetType nAttempt) then
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
    let otherMVarIds ← Meta.getMVarsNoDelayed e
    -- let newMVarIds ← Meta.reorderGoals newMVars cfg.newGoals
    let newMVarIds := (newMVars.map (·.mvarId!)).data
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result
termination_by go i => rangeNumArgs.stop - i

syntax (name := hoapply) "hoapply " term " attempt " num : tactic

@[tactic hoapply]
def evalHoApply : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| hoapply $e attempt $nAttempt:num) => Elab.Tactic.withMainContext do
    let mut val ← instantiateMVars (← Elab.Tactic.elabTermForApply e)
    if val.isMVar then
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← exechoapply (← Elab.Tactic.getMainGoal) val nAttempt.getNat
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    Elab.Tactic.replaceMainGoal mvarIds'
  | _ => Elab.throwUnsupportedSyntax

set_option trace.Meta.debug true

def test (f : Nat → Prop) (h : ∀ x, f x) : f 3 := by
  hoapply h attempt 19