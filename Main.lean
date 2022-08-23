import Duper.Tactic
import Duper.TPTP -- Note: this import is needed to make sure that TPTP is compiled for the github actions

def main : List String → IO UInt32 := fun args => do
  let propInequalityTest1 {p : Prop} {q : Prop} (h : p ≠ q) : p ∨ q :=
    by duper
  let propInequalityTest2 {p : Prop} {q : Prop} (h : p ≠ q) : p ∨ q :=
    by duper
  return 0