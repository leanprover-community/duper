module

public import Duper
public import Duper.TPTP

/-! Duper's library modules participate in Lean's module system, so downstream projects that
    have adopted it can import Duper and call the `duper` tactic. This file is the module-system
    counterpart of `Duper/Tests/test_regression.lean`; the other test files are deliberately
    left as non-module files so that both kinds of consumers stay covered. -/

public section

set_option duper.printPortfolioInstance true

axiom a : Nat
axiom b : Nat
axiom c : Nat
axiom f : Nat → Nat
axiom g : Nat → Nat

-- `duper` with no arguments
theorem module_test0 : ∀ (x : Nat), x = x := by duper

-- `duper [*]`, reading the whole local context
theorem module_test1
(ax1 : f a = b → f c ≠ b)
(ax2 : ¬ ∃ x, f x ≠ b ∧ c = c)
: False := by duper [*]

#print axioms module_test1

-- `duper [facts]`
theorem module_test2 (x y z : Nat) (h1 : f x = g y) (h2 : g y = f z) : f x = f z := by
  duper [h1, h2]

-- Higher-order reasoning
theorem module_test3 (fn gn : α → α) : (∀ x, fn x = gn x) = (∀ x, fn x = gn x) := by duper

theorem module_test4 {ι : Type} (johanna : ι) (bill : ι) (peanuts : ι)
  (food : ι → Prop) (alive : ι → Prop)
  (likes : ι → ι → Prop) (eats : ι → ι → Prop) (was_killed_by : ι → ι → Prop)
  (h1 : ∀ x, food x → likes johanna x)
  (h2 : ∀ x, (∃ y, eats y x ∧ ¬ was_killed_by y x) → food x)
  (h3 : eats bill peanuts)
  (h4 : alive bill)
  (h5 : ∀ y, alive y → ∀ x, ¬ was_killed_by y x) :
likes johanna peanuts := by duper [*]

-- Skolemization, so that `Duper.Skolem.some` shows up in the reconstructed proof
theorem module_test5 (p : Nat → Prop) (hp : ∃ x, p x) : ¬ ∀ x, ¬ p x := by duper [hp]

#print axioms module_test5

-- Explicitly selected portfolio instances and configuration options
theorem module_test6 (x : Nat) (h1 : f x = b) : ∃ y, f y = b := by
  duper [h1] {portfolioInstance := 1}

theorem module_test7 (p : Prop) (hp : p) : p := by
  duper [hp] {portfolioMode := false, portfolioInstance := 0, preprocessing := no_preprocessing}

theorem module_test8 (x : Nat) (h1 : ∀ y, f y = g y) : f x = g x := by
  duper [h1] {portfolioMode := false, portfolioInstance := 0, inhabitationReasoning := true,
              includeExpensiveRules := true, selFunction := 4}

-- Duper's proof-producing suggestion mode
example (x y : Nat) (h1 : f x = y) : y = f x := by duper? [h1]
