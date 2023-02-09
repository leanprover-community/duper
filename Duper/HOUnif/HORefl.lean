import Lean.Meta.Reduce
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply
import Duper.HOUnif.UnifRules

open Lean Meta
namespace HOUnif

/--
Close given goal using `Eq.refl`.
-/
def MVarId.refl (mvarId : MVarId) (nAttempt : Nat) (nUnif : Nat) (cont : Nat) : MetaM (Array MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `refl
    let targetType ← mvarId.getType'
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    let success ← hounif lhs rhs nAttempt nUnif cont
    unless success do
      throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)
    Meta.getMVarsNoDelayed (.mvar mvarId)

syntax (name := horefl) "horefl" " attempt " num "unifier " num "contains" num  : tactic

@[tactic horefl] def evalRefl : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| horefl attempt $nAttempt unifier $nunif contains $cont) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← HOUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat
        return ids.data
  | _ => Elab.throwUnsupportedSyntax


opaque wwww : Nat → Nat → Nat → Nat := fun _ _ _ => 1
opaque www : Nat → Nat → Nat := fun _ _ => 1
opaque ww : Nat → Nat := id
opaque w : Nat

-- Trivial
set_option trace.Meta.debug true in
def tri₁ : 1 = 1 := by horefl attempt 3 unifier 0 contains 0

-- Iteration
set_option trace.Meta.debug true in
def iter₁ (done : Prop)
          (gene : ∀ (H : (Nat → Nat) → Nat → Nat) F X, H F X = F X → done) :
          done := by
  apply gene
  case a => horefl attempt 1350 unifier 0 contains 559
            case F => exact ww
            case X => exact w

set_option trace.Meta.debug true in
def iter₂ (done : Prop) (a : Nat)
          (gene : ∀ (F G : Nat → Nat), F a = G a → done) :
          done := by
  apply gene
  case a => horefl attempt 4500 unifier 0 contains 1618; exact wwww

#print iter₂.proof_1
  