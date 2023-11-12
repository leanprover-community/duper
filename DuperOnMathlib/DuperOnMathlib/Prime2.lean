import Duper.Tactic
import Mathlib.Data.Nat.Prime

set_option includeExpensiveRules false

/- Duper can solve this theorem when `preprocessFact` in Util.Reduction.lean is disabled (set to the identity function).
   When `preprocessFact` runs as it usually does, Duper times out when attempting to solve this theorem. Previously,
   there were PANIC error messages caused by Duper's precCompare being incomplete, but those issues have since been resolved. -/
theorem prime_def_lt''_new {p : ℕ} : Nat.Prime p ↔ 2 ≤ p ∧ ∀ (m) (_ : m ∣ p), m = 1 ∨ m = p := by
  have h1 : (1 : Nat) < 2 := @one_lt_two Nat _ _ _ _ _
  have h2 : ∀ {a b c : ℕ}, a < b → b ≤ c → a < c := @LT.lt.trans_le Nat _
  have h3 : ∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c) := @mul_right_inj' Nat _
  have h4 : ∀ {n m : ℕ}, n < m → 0 < m:= @pos_of_gt Nat _
  have h5 : ∀ (a b : ℕ), a ∣ a * b := @dvd_mul_right Nat _
  have h6 : ∀ (a : ℕ), a * 1 = a := @mul_one Nat _
  have h7 : ∀ {x y : ℕ}, x < y → y ≠ x := @LT.lt.ne' Nat _
  have h8 : ∀ {n : ℕ}, IsUnit n ↔ n = 1 := @Nat.isUnit_iff
  have h9 : ∀ {p : ℕ}, Nat.Prime p → 2 ≤ p := @Nat.Prime.two_le
  have h10 : ∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p := @Nat.Prime.eq_one_or_self_of_dvd
  have h11 := Nat.irreducible_iff_nat_prime
  have h12 : ∀ {p : ℕ}, Irreducible p ↔ ¬IsUnit p ∧ ∀ (a b : ℕ), p = a * b → IsUnit a ∨ IsUnit b := @irreducible_iff Nat _
  duper [*] {portfolioInstance := 0}

set_option reduceInstances false

theorem prime_def_lt''_new2 {p : ℕ} : Nat.Prime p ↔ 2 ≤ p ∧ ∀ (m) (_ : m ∣ p), m = 1 ∨ m = p := by
  have h1 : (1 : Nat) < 2 := @one_lt_two Nat _ _ _ _ _
  have h2 : ∀ {a b c : ℕ}, a < b → b ≤ c → a < c := @LT.lt.trans_le Nat _
  have h3 : ∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c) := @mul_right_inj' Nat _
  have h4 : ∀ {n m : ℕ}, n < m → 0 < m:= @pos_of_gt Nat _
  have h5 : ∀ (a b : ℕ), a ∣ a * b := @dvd_mul_right Nat _
  have h6 : ∀ (a : ℕ), a * 1 = a := @mul_one Nat _
  have h7 : ∀ {x y : ℕ}, x < y → y ≠ x := @LT.lt.ne' Nat _
  have h8 : ∀ {n : ℕ}, IsUnit n ↔ n = 1 := @Nat.isUnit_iff
  have h9 : ∀ {p : ℕ}, Nat.Prime p → 2 ≤ p := @Nat.Prime.two_le
  have h10 : ∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p := @Nat.Prime.eq_one_or_self_of_dvd
  have h11 := Nat.irreducible_iff_nat_prime
  have h12 : ∀ {p : ℕ}, Irreducible p ↔ ¬IsUnit p ∧ ∀ (a b : ℕ), p = a * b → IsUnit a ∨ IsUnit b := @irreducible_iff Nat _
  duper [*] {portfolioInstance := 0}
