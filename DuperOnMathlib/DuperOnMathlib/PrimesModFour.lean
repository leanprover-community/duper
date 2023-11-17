import Mathlib.Data.Nat.Prime
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import DuperOnMathlib.DuperInterface

lemma composite_of_not_prime {n : ℕ} (h : 2 ≤ n) (hnp : ¬ n.Prime) :
    ∃ m k, n = m * k ∧ 1 < m ∧ 1 < k ∧ m < n ∧ k < n := by
  rw [Nat.prime_def_lt] at hnp
  have : ∃ m, m ∣ n ∧ m < n ∧ m ≠ 1 := by
    duper [h, hnp]
  rcases this with ⟨m, mdvd, mlt, mne⟩
  have neq : n = m * (n / m) := by symm; rwa [Nat.mul_div_eq_iff_dvd]
  use m, n / m, neq
  have mgt1 : 1 < m := by
    -- apply lt_of_le_of_ne _ (Ne.symm mne)
    -- rw [ne_eq] at mne
    -- apply Nat.pos_of_ne_zero
    -- rintro rfl
    -- have := ne_of_lt mlt
    -- simp only [zero_dvd_iff] at mdvd
    -- simp only [mdvd] at this
    have : 1 ≤ m ↔ 0 < m := Iff.refl _
    duper [zero_dvd_iff, mdvd, ne_of_lt, mlt, Nat.pos_of_ne_zero, ne_eq, this, lt_of_le_of_ne, mne]
  use mgt1
  have ndivmgt1 : 1 < n / m := by
    duper [lt_of_mul_lt_mul_left, Nat.zero_le, mul_one, neq, mlt]
    -- this also works:
    -- apply lt_of_mul_lt_mul_left _ (Nat.zero_le m)
    -- duper [mul_one, neq, mlt]
    -- but this fails:
    -- apply lt_of_mul_lt_mul_left _ (Nat.zero_le m)
    -- duper [mul_one, neq, mlt, lt_of_mul_lt_mul_left]
  use ndivmgt1
  constructor
  . have : 0 < m := zero_lt_one.trans mgt1
    duper [mul_one, neq, Nat.mul_lt_mul_of_pos_left, ndivmgt1, this]
  -- also works:
  -- duper [mul_one, neq, Nat.mul_lt_mul_of_pos_left, ndivmgt1, zero_lt_one, lt_trans, gt_iff_lt, mgt1]
  have : 1 * (n / m) < m * (n / m) := by
    duper [Nat.mul_lt_mul_of_pos_right, mgt1, zero_lt_one.trans ndivmgt1]
  rwa [one_mul, ←neq] at this

lemma composite_of_not_prime_alt (n : ℕ) (h : 2 ≤ n) (hnp : ¬ n.Prime) :
    ∃ m k, n = m * k ∧ 1 < m ∧ 1 < k ∧ m < n ∧ k < n := by
  have nne0 : n ≠ 0 := by linarith
  have aux : ∀ {m k}, n = m * k → m ≠ 1 → 1 < m ∧ k < n := by
    intros m k neq mne1
    have : m ≠ 0 := by
      contrapose! nne0
      simp only [neq, nne0, zero_mul]
    have mgt1 : 1 < m := by
      apply lt_of_le_of_ne _ (Ne.symm mne1)
      rwa [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
    use mgt1
    have : 0 < k := by
      rw [Nat.pos_iff_ne_zero]
      contrapose! nne0
      simp [neq, nne0]
    rw [←one_mul k, neq]
    apply Nat.mul_lt_mul_of_pos_right mgt1 this
  have nne1 : n ≠ 1 := by linarith
  have : ∃ m, m ≠ 1 ∧ ∃ k, n = m * k ∧ k ≠ 1 := by
    simpa [←Nat.irreducible_iff_nat_prime, irreducible_iff, nne1, not_or] using hnp
  rcases this with ⟨m, mne1, k, neq, kne1⟩
  have h1 : 1 < m ∧ k < n := aux neq mne1
  rw [mul_comm] at neq
  have h2 : 1 < k ∧ m < n := aux neq kne1
  rw [mul_comm] at neq
  use m, k, neq, h1.1, h2.1, h2.2, h1.2

lemma mod_four_eq_three_or_mod_four_eq_three_of_mul_mod_four_eq_three
    {m n : ℕ} : (m * n) % 4 = 3 → m % 4 = 3 ∨ n % 4 = 3 := by
  rw [Nat.mul_mod]
  have hm : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  have hn : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases m % 4 <;> interval_cases n % 4 <;> simp

lemma exists_prime_dvd_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  induction n using Nat.strong_induction_on
  next n ih =>
    by_cases hnprime : n.Prime
    . use n
    . have : 2 ≤ n := by
        rcases n with (- | - | n) <;> try (norm_num at h)
        simp [Nat.succ_le_succ_iff]
      rcases composite_of_not_prime this hnprime with ⟨m, k, neq, -, -, mlt, klt⟩
      cases mod_four_eq_three_or_mod_four_eq_three_of_mul_mod_four_eq_three (neq ▸ h)
      . next h' =>
        rcases ih m mlt h' with ⟨p, primep, pdvd, pmod⟩
        rw [neq]
        use p, primep, dvd_mul_of_dvd_left pdvd _, pmod
      . next h' =>
        rcases ih k klt h' with ⟨p, primep, pdvd, pmod⟩
        rw [neq]
        use p, primep, dvd_mul_of_dvd_right pdvd _, pmod

theorem infinite_primes_three_mod_four : ∀ s : Finset ℕ,
    ¬ ∀ p, p ∈ s ↔ p.Prime ∧ p % 4 = 3 := by
  intro s hs
  set n := 4 * s.prod id - 1 with hn
  have prodge1 : 1 ≤ Finset.prod s id := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, Finset.prod_eq_zero_iff]
    simp only [hs, id_eq, exists_eq_right, not_false_eq_true]
  have h₁ : n % 4 = 3 := by
    have : s.prod id = s.prod id - 1 + 1 := by
      rwa [Nat.sub_add_cancel]
    rw [hn, this, mul_add, Nat.add_sub_assoc, mul_comm 4, Nat.mul_add_mod]; rfl
    norm_num
  rcases exists_prime_dvd_mod_four_eq_three h₁ with ⟨p, primep, pdvd, pmod⟩
  have pmems : p ∈ s := by
    rw [hs]
    use primep, pmod
  have : p ∣ 4 * s.prod id - n:= by
    apply Nat.dvd_sub _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id pmems) _) pdvd
    rw [hn]
    apply tsub_le_self
  have : p ∣ 1 := by
    rwa [hn, tsub_tsub_cancel_of_le] at this
    have : 1 ≤ 4 * 1 := by norm_num
    apply le_trans this
    apply mul_le_mul_of_nonneg_left prodge1 (by norm_num)
  have : p ≤ 1 := Nat.le_of_dvd (by norm_num) this
  have : 2 ≤ p := primep.two_le
  linarith


namespace original

lemma composite_of_not_prime {n : ℕ} (h : 2 ≤ n) (hnp : ¬ n.Prime) :
    ∃ m k, n = m * k ∧ 1 < m ∧ 1 < k ∧ m < n ∧ k < n := by
  rw [Nat.prime_def_lt] at hnp
  have : ∃ m, m ∣ n ∧ m < n ∧ m ≠ 1 := by
    simpa [h] using hnp
  rcases this with ⟨m, mdvd, mlt, mne⟩
  have neq : n = m * (n / m) := by symm; rwa [Nat.mul_div_eq_iff_dvd]
  use m, n / m, neq
  have mgt1 : 1 < m := by
    apply lt_of_le_of_ne _ (Ne.symm mne)
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp at mdvd; linarith
  use mgt1
  have ndivmgt1 : 1 < n / m := by
    apply lt_of_mul_lt_mul_left _ (Nat.zero_le m)
    rwa [mul_one, ←neq]
  use ndivmgt1
  constructor
  . rw [←mul_one m, neq]
    exact Nat.mul_lt_mul_of_pos_left ndivmgt1 (zero_lt_one.trans mgt1)
  have : 1 * (n / m) < m * (n / m) := by
    apply Nat.mul_lt_mul_of_pos_right mgt1 (zero_lt_one.trans ndivmgt1)
  rwa [one_mul, ←neq] at this

lemma composite_of_not_prime_alt (n : ℕ) (h : 2 ≤ n) (hnp : ¬ n.Prime) :
    ∃ m k, n = m * k ∧ 1 < m ∧ 1 < k ∧ m < n ∧ k < n := by
  have nne0 : n ≠ 0 := by linarith
  have aux : ∀ {m k}, n = m * k → m ≠ 1 → 1 < m ∧ k < n := by
    intros m k neq mne1
    have : m ≠ 0 := by
      contrapose! nne0
      simp [neq, nne0]
    have mgt1 : 1 < m := by
      apply lt_of_le_of_ne _ (Ne.symm mne1)
      rwa [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
    use mgt1
    have : 0 < k := by
      rw [Nat.pos_iff_ne_zero]
      contrapose! nne0
      simp [neq, nne0]
    rw [←one_mul k, neq]
    apply Nat.mul_lt_mul_of_pos_right mgt1 this
  have nne1 : n ≠ 1 := by linarith
  have : ∃ m, m ≠ 1 ∧ ∃ k, n = m * k ∧ k ≠ 1 := by
    simpa [←Nat.irreducible_iff_nat_prime, irreducible_iff, nne1, not_or] using hnp
  rcases this with ⟨m, mne1, k, neq, kne1⟩
  have h1 : 1 < m ∧ k < n := aux neq mne1
  rw [mul_comm] at neq
  have h2 : 1 < k ∧ m < n := aux neq kne1
  rw [mul_comm] at neq
  use m, k, neq, h1.1, h2.1, h2.2, h1.2

lemma mod_four_eq_three_or_mod_four_eq_three_of_mul_mod_four_eq_three
    {m n : ℕ} : (m * n) % 4 = 3 → m % 4 = 3 ∨ n % 4 = 3 := by
  rw [Nat.mul_mod]
  have hm : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  have hn : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases m % 4 <;> interval_cases n % 4 <;> simp

lemma exists_prime_dvd_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  induction n using Nat.strong_induction_on
  next n ih =>
    by_cases hnprime : n.Prime
    . use n
    . have : 2 ≤ n := by
        rcases n with (- | - | n) <;> try (norm_num at h)
        simp [Nat.succ_le_succ_iff]
      rcases composite_of_not_prime this hnprime with ⟨m, k, neq, -, -, mlt, klt⟩
      cases mod_four_eq_three_or_mod_four_eq_three_of_mul_mod_four_eq_three (neq ▸ h)
      . next h' =>
        rcases ih m mlt h' with ⟨p, primep, pdvd, pmod⟩
        rw [neq]
        use p, primep, dvd_mul_of_dvd_left pdvd _, pmod
      . next h' =>
        rcases ih k klt h' with ⟨p, primep, pdvd, pmod⟩
        rw [neq]
        use p, primep, dvd_mul_of_dvd_right pdvd _, pmod

theorem infinite_primes_three_mod_four : ∀ s : Finset ℕ,
    ¬ ∀ p, p ∈ s ↔ p.Prime ∧ p % 4 = 3 := by
  intro s hs
  set n := 4 * s.prod id - 1 with hn
  have prodge1 : 1 ≤ Finset.prod s id := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, Finset.prod_eq_zero_iff]
    simp only [hs, id_eq, exists_eq_right, not_false_eq_true]
  have h₁ : n % 4 = 3 := by
    have : s.prod id = s.prod id - 1 + 1 := by
      rwa [Nat.sub_add_cancel]
    rw [hn, this, mul_add, Nat.add_sub_assoc, mul_comm 4, Nat.mul_add_mod]; rfl
    norm_num
  rcases exists_prime_dvd_mod_four_eq_three h₁ with ⟨p, primep, pdvd, pmod⟩
  have pmems : p ∈ s := by
    rw [hs]
    use primep, pmod
  have : p ∣ 4 * s.prod id - n:= by
    apply Nat.dvd_sub _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id pmems) _) pdvd
    rw [hn]
    apply tsub_le_self
  have : p ∣ 1 := by
    rwa [hn, tsub_tsub_cancel_of_le] at this
    have : 1 ≤ 4 * 1 := by norm_num
    apply le_trans this
    apply mul_le_mul_of_nonneg_left prodge1 (by norm_num)
  have : p ≤ 1 := Nat.le_of_dvd (by norm_num) this
  have : 2 ≤ p := primep.two_le
  linarith

end original
