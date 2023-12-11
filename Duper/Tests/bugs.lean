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
set_option trace.duper.saturate.debug true in
set_option trace.duper.timeout.debug true in
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

-- What was previously bug 5 (though I would no longer call it a bug per se)
example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper {portfolioInstance := 7}

example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper {portfolioInstance := 8}

/-
The previous bug 5 error of unknown fvars has been corrected. However, this example still fails when
inhabitation reasoning is enabled. The issue that occurs is that when inhabitation reasoning is enabled,
the clause `∀ (a a_1 : Type), (a_1 → a) → a_1 → False` is recognized as potentially vacuous. This makes
sense because if `a_1` is assigned an empty type, then no contradiction can be yielded by this clause.

Duper happens to be able to derive a contradiction from this clause when inhabitation reasoning is disabled
because the default instances that `Lean.Meta.findInstance` attempts happen to work well for this example,
though there are other examples where that strategy would not work. For instance, Duper will fail to
derive a contradiction from the clause `∀ x : Nat, Fin x → False` because the default `Nat` is 0. If the
default Nat were 1, then Duper would be able to derive a contradiction from this when inhabitation reasoning
is disabled (though Duper would still consider the clause vacuous with inhabitation reasoning enabled).

I wouldn't call the current behavior a bug so much as an area where Duper has a lot of room for improvement.
Supporting dependent type reasoning is a relatively low priority, but I'll leave this example documented
here for the future. More examples of related behavior are included at the end of test_inhabitationReasoning.lean.
-/

-- Diagnosis of the above test
/-
The error appears to occur during removeVanishedVarsHelper (which is only called when inhabitationReasoning is enabled).
-/

-- Bug 8: Application type mismatch pertaining to the universe levels of skolems
axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

axiom exftrue.{u} : ∃ (x : Type u), f x
set_option trace.duper.proofReconstruction true in
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
