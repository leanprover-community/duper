import Duper.TPTP
import Duper.Tactic

-- Bug 1
namespace Color2

inductive Color :=
| red : Color
| green : Color

example : @Color.rec (fun _ => Nat) a b .red = a := by duper [Color.rec]

def test : Color → Color
| .red => .green
| .green => .red

set_option pp.match false
#print test
#print test.match_1
#print Color.casesOn

-- This bug demonstrates the difficulty Duper has dealing with inductive arguments and facts such as Color.rec
set_option inhabitationReasoning false in
set_option trace.Saturate.debug true in
set_option trace.Timeout.debug true in
example : ∃ c : Color, test c = .green := by
  duper [test, test.match_1, Color.rec, Color.casesOn] {portfolioInstance := 0}

example : Color.red ≠ Color.green := by
  duper {portfolioInstance := 0}
/-
  It seems that reasoning about inductive types requires solving unification problems
    that are completely out of the scope of the current algorithms duper uses
  Here is an example of proving `Color.red ≠ Color.green` without using extra
    inductive types like `Color.noConfusion`
-/
theorem red_ne_green : Color.red ≠ Color.green := fun h =>
  let color_case := fun (t : Color) => @Color.casesOn (fun _ => Prop) t True False
  have color_true : color_case Color.red := True.intro
  (h ▸ color_true : color_case Color.green)
/-
  What we're trying to here do is to rewrite `True` to `False` using `Color.red = Color.green`
  To do this, notice that `True ≝ color_case Color.red` and `False ≝ color_case Color.green`
-/

end Color2

-- Bug 5
example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper {portfolioInstance := 7}

example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper {portfolioInstance := 8}

-- Diagnosis of the above test
/-
The error appears to occur during removeVanishedVarsHelper (which is only called when inhabitationReasoning is enabled).
-/

-- Bug 8: Application type mismatch pertaining to the universe levels of skolems
axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

axiom exftrue.{u} : ∃ (x : Type u), f x
set_option trace.ProofReconstruction true in
def test : ∃ x : Type u, ∃ y : Type v, f x = f y := by
  duper [exftrue]
/-
application type mismatch
  skol.0 [anonymous]
argument has type
  Type u_1
but function has type
  Type u_2 → Type u_2
-/

-- Bug 9
-- This example can only be solved when inhabitationReasoning is disabled (saturates if inhabitationReasoning is enabled)
set_option inhabitationReasoning false in
example : ∃ (A : Type) (B : A → Type) (f : ∀ (a : A), B a) (x : A), (f x = f x) = True :=
  by duper {portfolioInstance := 0}

set_option inhabitationReasoning true in
example : ∃ (A : Type) (B : A → Type) (f : ∀ (a : A), B a) (x : A), (f x = f x) = True :=
  by duper {portfolioInstance := 0}
