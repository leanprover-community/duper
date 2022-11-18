import Duper.Tactic

class Group (G : Type) where 
(one : G)
(inv : G → G)
(mul : G → G → G)
(mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z))
(mul_one : ∀ (x : G), mul x one = x)
(mul_inv : ∀ (x : G), mul x (inv x) = e)

namespace Group

variable {G : Type} [hG : Group G] (x y : G)

infix:80 (priority := high) " ⬝ " => Group.mul

noncomputable instance : Inhabited G := ⟨one⟩

theorem test : x ⬝ one = x :=
by duper [@Group.mul_one]

theorem exists_right_inv : inv x ⬝ x = e :=
by duper [@Group.mul_assoc G hG, @Group.mul_one G hG, @Group.mul_inv G hG]

theorem left_neutral_unique (x : G) : (∀ y, x ⬝ y = y) → x = e :=
by duper [@Group.mul_assoc G hG, @Group.mul_one G hG, @Group.mul_inv G hG]

theorem right_neutral_unique (x : G) : (∀ y, y ⬝ x = y) → x = e :=
by duper [@Group.mul_assoc G hG, @Group.mul_one G hG, @Group.mul_inv G hG]

theorem right_inv_unique (x y z : G) (h : x ⬝ y = e) (h : x ⬝ z = e) : y = z :=
by duper [@Group.mul_assoc G hG, @Group.mul_one G hG, @Group.mul_inv G hG]

theorem left_inv_unique (x y z : G) (h : y ⬝ x = e) (h : z ⬝ x = e) : y = z :=
by duper [@Group.mul_assoc G hG, @Group.mul_one G hG, @Group.mul_inv G hG]

noncomputable def sq := x ⬝ x

theorem sq_mul_sq_eq_e (h_comm : ∀ (a b : G), a ⬝ b = b ⬝ a) (h : x ⬝ y = e) :
  sq x ⬝ sq y = e :=
by duper [@sq, @Group.mul_assoc G hG, @Group.mul_one G hG, @Group.mul_inv G hG]

end Group