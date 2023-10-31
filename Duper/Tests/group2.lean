import Duper.Tactic

class Group (G : Type) where
(one : G)
(inv : G → G)
(mul : G → G → G)
(mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z))
(mul_one : ∀ (x : G), mul x one = x)
(mul_inv : ∀ (x : G), mul x (inv x) = one)

namespace Group

variable {G : Type} [hG : Group G] (x y : G)

infix:80 (priority := high) " ⬝ " => Group.mul

noncomputable instance : Inhabited G := ⟨one⟩

theorem test : x ⬝ one = x :=
by duper [Group.mul_one]

/- Note: Currently, includeHoist must be disabled in order for duper to solve these problems. In the future,
   portfolio mode should be enhanced so that at least one portfolio instance enables hoist rules and most
   portfolio instances disable hoist rules. -/
set_option includeHoistRules false

theorem exists_right_inv (x : G) : inv x ⬝ x = one :=
by duper [Group.mul_assoc, Group.mul_one, Group.mul_inv] {portfolioInstance := 0}

theorem left_neutral_unique (x : G) : (∀ y, x ⬝ y = y) → x = one :=
by duper [Group.mul_assoc, Group.mul_one, Group.mul_inv] {portfolioInstance := 0}

theorem right_neutral_unique (x : G) : (∀ y, y ⬝ x = y) → x = one :=
by duper [Group.mul_assoc, Group.mul_one, Group.mul_inv] {portfolioInstance := 0}

theorem right_inv_unique (x y z : G) (h : x ⬝ y = one) (h : x ⬝ z = one) : y = z :=
by duper [*, Group.mul_assoc, Group.mul_one, Group.mul_inv] {portfolioInstance := 0}

theorem left_inv_unique (x y z : G) (h : y ⬝ x = one) (h : z ⬝ x = one) : y = z :=
by duper [*, Group.mul_assoc, Group.mul_one, Group.mul_inv] {portfolioInstance := 0}

noncomputable def sq := x ⬝ x

theorem sq_mul_sq_eq_e (h_comm : ∀ (a b : G), a ⬝ b = b ⬝ a) (h : x ⬝ y = one) :
  sq x ⬝ sq y = one :=
by duper [h, h_comm, sq, Group.mul_assoc, Group.mul_one, Group.mul_inv] {portfolioInstance := 0}

end Group
