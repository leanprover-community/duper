import Duper.Tactic

axiom G : Type
axiom e : G
axiom mul : G → G → G

infix:80 (priority := high) " ⬝ " => mul

axiom mul_assoc : ∀ (x y z : G), (x ⬝ y) ⬝ z = x ⬝ (y ⬝ z)
axiom mul_e : ∀ (x : G), x ⬝ e = x
axiom exists_left_inv : ∀ (x : G), ∃ (y : G), x ⬝ y = e

noncomputable instance : Inhabited G := ⟨e⟩

theorem e_mul : e ⬝ x = x :=
by duper [mul_assoc, mul_e, exists_left_inv] {portfolioInstance := 1}

theorem exists_right_inv (x : G) : ∃ (y : G), y ⬝ x = e :=
by duper [mul_assoc, mul_e, exists_left_inv] {portfolioInstance := 1}

theorem left_neutral_unique (x : G) : (∀ y, x ⬝ y = y) → x = e :=
by duper [mul_assoc, mul_e, exists_left_inv] {portfolioInstance := 1}

theorem right_neutral_unique (x : G) : (∀ y, y ⬝ x = y) → x = e :=
by duper [mul_assoc, mul_e, exists_left_inv] {portfolioInstance := 1}

theorem right_inv_unique (x y z : G) (h : x ⬝ y = e) (h : x ⬝ z = e) : y = z :=
by duper [*, mul_assoc, mul_e, exists_left_inv] {portfolioInstance := 1}

theorem left_inv_unique (x y z : G) (h : y ⬝ x = e) (h : z ⬝ x = e) : y = z :=
by duper [*, mul_assoc, mul_e, exists_left_inv] {portfolioInstance := 1}

noncomputable def sq (x : G) := x ⬝ x

theorem sq_mul_sq_eq_e (x y : G) (h_comm : ∀ a b, a ⬝ b = b ⬝ a) (h : x ⬝ y = e) :
  sq x ⬝ sq y = e :=
by duper [h_comm, h, sq, mul_assoc, mul_e] {portfolioInstance := 1}
