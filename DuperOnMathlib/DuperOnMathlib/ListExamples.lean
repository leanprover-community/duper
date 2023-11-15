import Mathlib.Data.List.Basic

section
variable {α : Type*} [LinearOrder α]

/-- Returns a pair consisting of a minimal element of the list (or ⊥ if the list is empty) and the
maximal element element of the list (or ⊤ if the list if empty) -/
def foo : List α → WithBot α × WithTop α
  | [] => (⊥, ⊤)
  | (x :: xs) =>
    let (min, max) := foo xs
    (min ⊓ x, max ⊔ x)

/-- An alternative definition, using `foldr` -/
def foo' (xs : List α) : WithBot α × WithTop α :=
  xs.foldr (fun (x : α) (p : WithBot α × WithTop α) => (Prod.fst p ⊓ x, Prod.snd p ⊔ x)) (⊥, ⊤)

theorem foo'_cons (x : α) (xs : List α) : foo' (x :: xs) = ((foo' xs).fst ⊓ x, (foo' xs).snd ⊔ x) := by
  simp [foo']

theorem foo_eq_foo' (xs : List α) : foo xs = foo' xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [foo, foo'_cons, ih]

theorem fst_foo_le (xs : List α) : ∀ x ∈ xs, (foo xs).fst ≤ x := by
  induction xs with
  | nil => simp [foo]
  | cons x xs ih =>
    intro y h
    simp [foo]
    simp at h
    cases h with
    | inl h =>
      simp [h]
    | inr h =>
      simp [ih _ h]

end
