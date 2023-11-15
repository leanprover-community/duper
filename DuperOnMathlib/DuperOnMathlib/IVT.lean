import Mathlib.Data.Real.Basic

def ApproachesAt (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε, 0 < ε →  ∃ δ, 0 < δ ∧ ∀ x, abs (x - a) < δ → abs (f x - b) < ε

def Continuous (f : ℝ → ℝ) := ∀ x, ApproachesAt f (f x) x

theorem continuous_id : Continuous (λ x ↦ x) := by
  intro x
  intro ε εpos
  use ε
  constructor
  exact εpos
  intro x' h
  simp [h]

theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
      (ctsf : Continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  set S := { x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b } with hS
  have aS : a ∈ S := by
    exact ⟨le_of_lt hfa, le_refl a, aleb⟩
  have nonemptyS : S.Nonempty := ⟨a, aS⟩
  have bddS : BddAbove S := by
    use b
    intro x xS
    exact xS.2.2
  set x₀ := sSup S with hx₀
  have alex₀ : a ≤ x₀ := le_csSup bddS aS
  have x₀leb : x₀ ≤ b := by
    apply csSup_le nonemptyS
    intro x xS
    exact xS.2.2
  have : ¬ 0 < f x₀ := by
    intro h
    rcases ctsf x₀ _ h with ⟨δ, δpos, hδ⟩
    set x' := x₀ - δ / 2 with hx'
    have : ∃ x'' ∈ S, x' < x'' := by
      apply exists_lt_of_lt_csSup nonemptyS
      rw [hx']; linarith
    rcases this with ⟨x'', x''S, x'lt⟩
    have : x'' ≤ x₀ := by
      exact le_csSup bddS x''S
    have : abs (f x'' - f x₀) < f x₀ := by
      apply hδ
      rw [abs_of_nonpos, neg_sub]
      simp [hx₀] at *
      linarith
      linarith
    rw [abs_lt] at this
    simp [hS] at x''S
    linarith
  have : ¬ f x₀ < 0 := by
    intro h
    have : 0 < - f x₀ := by
      linarith
    rcases ctsf x₀ _ this with ⟨δ, δpos, hδ⟩
    have x₀lt1 : x₀ < b := by
      apply lt_of_le_of_ne x₀leb
      intro h'
      rw [h'] at h
      exact lt_asymm hfb h
    have minpos : 0 < min (δ / 2) (b - x₀) := by
      apply lt_min; linarith
      linarith
    set x' := x₀ + min (δ / 2) (b - x₀) with hx'
    have : abs (f x' - f x₀) < - f x₀ := by
      apply hδ
      simp [hx']
      rw [abs_of_pos minpos]
      apply lt_of_le_of_lt (min_le_left _ _)
      linarith
    have x'S : x' ∈ S := by
      dsimp [hS, hx']
      rw [abs_lt] at this
      constructor; linarith
      constructor; linarith
      linarith [min_le_right (δ / 2) (b - x₀)]
    have : x' ≤ x₀ := le_csSup bddS x'S
    dsimp [hx'] at this
    linarith
  have : f x₀ = 0 := by linarith
  use x₀, alex₀, x₀leb, this
