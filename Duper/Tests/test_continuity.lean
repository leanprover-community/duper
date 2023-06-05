import Duper.Tactic

axiom Real : Type
axiom dist : Real → Real → Real 
axiom add : Real → Real → Real 
axiom lt : Real → Real → Prop 
axiom zero : Real
axiom one : Real

def continuous_at (f : Real → Real) (x₀ : Real) :=
  ∀ ε : Real, lt zero ε → ∃ δ : Real, lt zero δ ∧ ∀ x, lt (dist x x₀) δ → lt (dist (f x) (f x₀)) ε

def continuous (f : Real → Real) := ∀ x, continuous_at f x

def uniformly_continuous (f : Real → Real) :=
  ∀ ε : Real, lt zero ε → ∃ δ : Real, lt zero δ ∧ ∀ x y, lt (dist x y) δ → lt (dist (f x) (f y)) ε

theorem dist_self (a : Real) : dist a a = zero := sorry

theorem zero_lt_one (a : Real) : lt zero one := sorry

example (a : Real) : continuous (λ _ => a) :=
  by simp only [continuous_at, continuous]; duper [dist_self]

example (a : Real) : uniformly_continuous (λ _ => a) :=
  by simp only [uniformly_continuous]; duper [dist_self, zero_lt_one]

example (a : Real) : continuous (λ x => x) :=
  by simp only [continuous_at, continuous]; duper [dist_self]

example (a : Real) : uniformly_continuous (λ x => x) :=
  by simp only [uniformly_continuous]; duper [dist_self, zero_lt_one]

example (f : Real → Real) : uniformly_continuous f → continuous f :=
  by simp only [continuous, continuous_at, uniformly_continuous]; duper

