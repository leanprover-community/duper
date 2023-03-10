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

syntax (name := drefl) "drefl" " attempt " num "unifier " num "contains" num ("iteron")? : tactic


@[tactic drefl] def evalRefl : Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| drefl attempt $nAttempt unifier $nunif contains $cont iteron) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← DUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat true
        return ids.data
  | `(tactic| drefl attempt $nAttempt unifier $nunif contains $cont) =>
      Elab.Tactic.liftMetaTactic fun mvarId => do
        let ids ← DUnif.MVarId.refl mvarId nAttempt.getNat nunif.getNat cont.getNat false
        return ids.data
  | _ => Elab.throwUnsupportedSyntax


opaque wwww : Nat → Nat → Nat → Nat := fun _ _ _ => 1
opaque www : Nat → Nat → Nat := fun _ _ => 1
opaque ww : Nat → Nat := id
opaque w : Nat

-- Trivial
set_option trace.DUnif.debug true in
def tri₁ : 1 = 1 := by drefl attempt 3 unifier 0 contains 0

def tri₂ (done : Prop)
         (gene : ∀ r (b : Nat → Nat), r = b r → done) : done := by
  apply gene;
  case a => drefl attempt 500 unifier 0 contains 0 iteron; exact 1
#print tri₂.proof_1

-- Iteration
set_option trace.DUnif.debug true in
set_option oracleInstOn false in
def iter₁ (done : Prop)
          (gene : ∀ (H : (Nat → Nat) → Nat → Nat) F X, H F X = F X → done) :
          done := by
  apply gene
  case a => drefl attempt 1500 unifier 0 contains 0 iteron
            case X => exact w

set_option trace.DUnif.debug true in
def iter₂ (done : Prop) (a : Nat)
          (gene : ∀ (F G : Nat → Nat), F a = G a → done) :
          done := by
  apply gene
  case a => drefl attempt 4400 unifier 0 contains 1541 iteron;

#print iter₂.proof_1


set_option dUnifDbgOn true

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
  case a => drefl attempt 160 unifier 0 contains 0

#print pellEquation₁.proof_1

def pellEquation₂ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → Nat)
                  -- ?m = 3, ?n = 6
                  (h : ∀ (m n : ChNat), 
                  q (chmul (chadd n c2) (chadd n c2)) (idtest m)   (idtest n) = 
                  q (chadd (chmul (chmul c7 m) m) c1) (fun z => z) (fun z => z)→ done)
                  : done := by
  apply h;
  case a => drefl attempt 18000 unifier 0 contains 0

#print pellEquation₂.proof_1

def pythagoreanTriple₁ (done : Prop) (q : ChNat → (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Nat)
                       (h : ∀ (x y z : ChNat),
                       -- 3² + 4² = 5²
                       q (chadd (chmul (chadd x c1) (chadd x c1))  (chmul (chadd y c1) (chadd y c1)))  (idtest x)   (idtest y)   (idtest z) = 
                       q (chmul (chadd z c2) (chadd z c2)) (fun z => z) (fun z => z) (fun z => z) → done):
                       done := by
  apply h;
  case a => drefl attempt 6000 unifier 0 contains 0

#print pythagoreanTriple₁.proof_1

end ChNum


-- Dependent Type
namespace Dependent

def dep₁ (done : Prop)
         (h : ∀ x, x = (1, 2).1 → done) : done := by
  apply h
  case a => drefl attempt 54 unifier 0 contains 0

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

set_option maxHeartbeats 400000 in
set_option oracleInstOn false in
set_option dUnifDbgOn false in
def dep₂ (done : Prop)
         (h : ∀ x, x = Nat.add1 → done) : done := by
  apply h
  case a => drefl attempt 120000 unifier 0 contains 0

#print dep₂.proof_1

end Dependent


-- let binders

@[reducible] def letdef₁ := let x := 2; x + x

def letrefl₁  (done : Prop)
              (lr : ∀ u, u = letdef₁ → done)
              : done := by
  apply lr
  drefl attempt 60 unifier 0 contains 0


-- Negative tests
set_option trace.DUnif.debug true in
def neg₁ (done : Prop) (f : Nat → Nat)
         (h : ∀ x, x = f x → done) : done := by
  apply h
  case a => drefl attempt 10 unifier 0 contains 0

set_option trace.DUnif.debug true in
def neg₂ (done : Prop) (f : Nat → Nat) (g : Nat → Nat →  Nat)
         (h : ∀ x y, g x y = g y (f x) → done) : done := by
  apply h
  case a => drefl attempt 10 unifier 0 contains 0