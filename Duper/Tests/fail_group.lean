import Duper.Tactic

-- vampire succeeds on this example

theorem cubeisom
  (G : Type)
  (e : G)
  (mult : G → G → G)
  (inverse : G → G)
  (cube : G → G)
  (left_identity : ∀ x, mult e x = x)
  (left_inverse : ∀ x, mult (inverse x) x = e)
  (associativity : ∀ x y z, mult (mult x y) z = mult x (mult y z))
  (cube_definition : ∀ x, cube x = mult x (mult x x))
  (cube_injective : ∀ x y, cube x = cube y → x = y)
  (cube_surjective : ∀ x, ∃ y, x = cube y)
  (cube_homomorphism : ∀ x y, cube (mult x y) = mult (cube x) (cube y))
  : ∀ x y, mult x y = mult y x := by duper [*]
