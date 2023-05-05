import Duper.Tactic
import Duper.TPTP

-- SkolemSorry test

namespace SkolemSorry

def skolemSorry := 2

def skolemSorry_ := 4

set_option trace.Meta.debug true

def sks₁ : True := by duper

def sks₂ : True := by duper

def sks₃ : False := by duper

def sks₄ : False := by duper

#print sks₂.proof_1

end SkolemSorry

-- Universe level tests

namespace UniverseTest

axiom f.{u} : Type u → Prop

axiom ftrue.{u} : f.{u} (Sort u)

set_option trace.Print_Proof true in
def unitst₁ : f.{max u v} (Sort (max u v)) ∧ f.{v} (Sort v) := by
  duper [ftrue]

axiom fmoretrue.{u} : ∀ (x : Type u), f x

set_option trace.Print_Proof true in
def unitst₂ : ∀ (x : Type v), f x := by
  duper [fmoretrue]

axiom exftrue.{u} : ∃ (x : Type u), f x

set_option trace.ProofReconstruction true in
def skuniverse.{u} : ∃ (x : Type u), f x := by
  duper [exftrue]

end UniverseTest

namespace ComplexUniverse

#check Lean.Level

-- Just checking whether universe level works correctly
set_option trace.ProofReconstruction true in
def rec₁ : False := by
  duper [Nat.rec]

end ComplexUniverse