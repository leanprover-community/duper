import Duper
import Duper.TPTP

set_option auto.tptp true
set_option auto.tptp.premiseSelection true
set_option auto.tptp.solver.name "zipperposition"
set_option trace.auto.tptp.result true
set_option trace.auto.tptp.printQuery true
set_option auto.native true

open Lean Auto

@[rebind Auto.Native.solverFunc]
def Auto.duperPort (lemmas : Array Lemma) : MetaM Expr := do
  let formulas ← Duper.autoLemmasToFormulas lemmas
  let formulas := formulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  Duper.runDuperPortfolioMode formulas .none
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      preprocessing := Duper.PreprocessingOption.NoPreprocessing, -- It would be redundant to enable Auto's preprocessing for Auto calls
      includeExpensiveRules := none,
      selFunction := none
    }
    .none

inductive myType
| const1 : myType
| const2 : myType

inductive myType2 (t : Type _)
| const3 : t → myType2 t
| const4 : t → myType2 t

inductive myType3
| const5 : myType3
| const6 : myType3 → myType3

inductive myType4 (t1 t2 : Type _)
| const7 : t1 → t2 → myType4 t1 t2

inductive myEmpty (t1 : Type _) (t2 : Type _)

open myType myType2 myType3 myType4

set_option duper.collectDatatypes true
set_option trace.duper.rule.datatypeExhaustiveness true
set_option trace.duper.printProof true
set_option trace.duper.collectDatatypes.debug true

example : ∀ xs : List Unit, ∀ x : Unit, x :: xs ≠ xs := by
  -- duper [List.all_nil] {portfolioInstance := 7}
  sorry -- Works when datatypeAcyclicity is enabled

--------------------------------------------------------------------
/- This example times out when `duper.collectDatatypes` is enabled, look into whether this is a bug or to be expected

example (f : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat)
  (g : Nat → Nat → Nat → Nat → Nat → Nat)
  (inertia : TPTP.iota → TPTP.iota → TPTP.iota → Prop)
  (goodInertia goodChance : TPTP.iota → Prop)
  (organization: TPTP.iota → TPTP.iota → Prop)
  -- good inertia implies good survival chance
  (dummy: ∀ (Y T2 I2 P2 : TPTP.iota), organization Y T2 ∧ inertia Y I2 T2 ∧ goodInertia I2 → goodChance P2)
  : ∃ x : Nat,
       f (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) (g x x x x x)
     = f (g 1 x x x x) (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) (g x x x x x) (g x 1 x x x) :=
  by duper {portfolioInstance := 7}
-/
