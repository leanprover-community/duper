import Lean.Meta.Reduce
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply
import Duper.DUnif.UnifRules

open Lean Meta
namespace DUnif

/--
Close given goal using `Eq.refl`.
-/
def MVarId.refl (mvarId : MVarId) (nAttempt : Nat) (nUnif : Nat) (cont : Nat) (iterOn : Bool) : MetaM (Array MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `refl
    let targetType ← mvarId.getType'
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    let success ← hounif lhs rhs nAttempt nUnif cont iterOn
    unless success do
      throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)
    Meta.getMVarsNoDelayed (.mvar mvarId)

syntax (name := horefl) "horefl" " attempt " num "unifier " num "contains" num ("iteron")? : tactic


@[tactic horefl] def evalRefl : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| horefl attempt $nAttempt unifier $nunif contains $cont iteron) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← DUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat true
        return ids.data
  | `(tactic| horefl attempt $nAttempt unifier $nunif contains $cont) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← DUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat false
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
  case a => horefl attempt 1500 unifier 0 contains 573 iteron
            case F => exact ww
            case X => exact w

set_option trace.Meta.debug true in
def iter₂ (done : Prop) (a : Nat)
          (gene : ∀ (F G : Nat → Nat), F a = G a → done) :
          done := by
  apply gene
  case a => horefl attempt 4400 unifier 0 contains 1541 iteron; exact wwww

#print iter₂.proof_1


-- ChurchNumeral
namespace ChNum

@[reducible] def ChNat := Nat → (Nat → Nat) → Nat
@[reducible] def chadd (n m : ChNat) x f := n (m x f) f
@[reducible] def chmul (n m : ChNat) x f := n x (fun z => m z f)
@[reducible] def idtest (n : ChNat) := fun z => n z (fun y => y)

@[reducible] def c0 : ChNat := fun x _ => x
@[reducible] def c1 : ChNat := fun x f => f x
@[reducible] def c2 : ChNat := fun x f => f (f x)
@[reducible] def c3 : ChNat := fun x f => f (f (f x))
@[reducible] def c7 : ChNat := fun x f => f (f (f (f (f (f (f x))))))

def pellEquation₁ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → Nat)
                  -- ?m = 2, ?n = 1
                  (h : ∀ (m n : ChNat), 
                  q (chmul (chadd n c2) (chadd n c2)) (idtest m)   (idtest n) = 
                  q (chadd (chmul (chmul c2 m) m) c1) (fun z => z) (fun z => z)  → done)
                  : done := by
  apply h;
  case a => horefl attempt 160 unifier 0 contains 0

#print pellEquation₁.proof_1

def pellEquation₂ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → Nat)
                  -- ?m = 3, ?n = 6
                  (h : ∀ (m n : ChNat), 
                  q (chmul (chadd n c2) (chadd n c2)) (idtest m)   (idtest n) = 
                  q (chadd (chmul (chmul c7 m) m) c1) (fun z => z) (fun z => z)→ done)
                  : done := by
  apply h;
  case a => horefl attempt 18000 unifier 0 contains 0

#print pellEquation₂.proof_1

def pythagoreanTriple₁ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Nat)
                       (h : ∀ (x y z : ChNat),
                       -- 3² + 4² = 5²
                       q (chadd (chmul (chadd x c1) (chadd x c1))  (chmul (chadd y c1) (chadd y c1)))  (idtest x)   (idtest y)   (idtest z) = 
                       q (chmul (chadd z c2) (chadd z c2)) (fun z => z) (fun z => z) (fun z => z) → done):
                       done := by
  apply h;
  case a => horefl attempt 6000 unifier 0 contains 0

#print pythagoreanTriple₁.proof_1

end ChNum


-- Dependent Type
namespace Dependent

def dep₁ (done : Prop)
         (h : ∀ x, x = (1, 2).1 → done) : done := by
  apply h
  case a => horefl attempt 54 unifier 0 contains 0

@[reducible] noncomputable def Nat.add1 := fun (x x_1 : Nat) =>
  @Nat.brecOn.{1} (fun (x : Nat) => Nat → Nat) x_1
    (fun (x : Nat) (f : @Nat.below.{1} (fun (x : Nat) => Nat → Nat) x) (x_2 : Nat) =>
      (fun (motive : Nat → Nat → Type) (a x : Nat) (h_1 : (a : Nat) → motive a Nat.zero)
    (h_2 : (a b : Nat) → motive a (Nat.succ b)) =>
  @Nat.casesOn.{1} (fun (x : Nat) => motive a x) x (h_1 a) fun (n : Nat) => h_2 a n) (fun (a x : Nat) => @Nat.below.{1} (fun (x : Nat) => Nat → Nat) x → Nat) x_2
        x (fun (a : Nat) (x : @Nat.below.{1} (fun (x : Nat) => Nat → Nat) Nat.zero) => a)
        (fun (a b : Nat) (x : @Nat.below.{1} (fun (x : Nat) => Nat → Nat) (Nat.succ b)) =>
          Nat.succ
            (@PProd.fst.{1, 1} ((fun (x : Nat) => Nat → Nat) b)
              (@Nat.rec.{2} (fun (t : Nat) => Type) PUnit.{1}
                (fun (n : Nat) (n_ih : Type) =>
                  PProd.{1, 1} (PProd.{1, 1} ((fun (x : Nat) => Nat → Nat) n) n_ih) PUnit.{1})
                b)
              (@PProd.fst.{1, 1}
                (PProd.{1, 1} ((fun (x : Nat) => Nat → Nat) b)
                  (@Nat.rec.{2} (fun (t : Nat) => Type) PUnit.{1}
                    (fun (n : Nat) (n_ih : Type) =>
                      PProd.{1, 1} (PProd.{1, 1} ((fun (x : Nat) => Nat → Nat) n) n_ih) PUnit.{1})
                    b))
                PUnit.{1} x)
              a))
        f)
    x

set_option maxHeartbeats 400000
def dep₂ (done : Prop)
         (h : ∀ x, x = Nat.add1 → done) : done := by
  apply h
  case a => horefl attempt 160000 unifier 0 contains 0

#print dep₂.proof_1

end Dependent

