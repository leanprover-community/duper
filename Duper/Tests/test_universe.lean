import Duper.TPTP
import Duper.Tactic

axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

set_option trace.Meta.debug true in
def unitst₁ : f.{max u v} (Sort (max u v)) ∧ f.{v} (Sort v) := by
  duper [ftrue]

axiom fmoretrue.{u} : ∀ (x : Type u), f x

set_option trace.Meta.debug true in
def unitst₂ : ∀ (x : Type v), f x := by
  duper [fmoretrue]