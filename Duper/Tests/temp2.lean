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

--------------------------------------------------------------------
-- Issues relating to Bool support

set_option trace.duper.saturate.debug true in
theorem Bool.not_eq_true2 (b : Bool) : (¬(b = true)) = (b = false) := by
  duper {portfolioInstance := 1}
  -- Final Active Set: [∀ (a a_1 : Bool), a = a_1]

set_option trace.duper.saturate.debug true in
theorem Bool.not_eq_false2 (b : Bool) : (¬(b = false)) = (b = true) := by
  duper {portfolioInstance := 1}
  -- Final Active Set: [∀ (a a_1 : Bool), a = a_1]

--------------------------------------------------------------------
-- Issues relating to type inhabitation reasoning

set_option trace.duper.timeout.debug true in
theorem forall_comm2 {p : α → β → Prop} : (∀ a b, p a b) ↔ (∀ b a, p a b) :=
  by sorry -- duper {inhabitationReasoning := true}

set_option trace.duper.timeout.debug true in
theorem exists_comm2 {p : α → β → Prop} : (∃ a b, p a b) ↔ (∃ b a, p a b) :=
  by sorry -- duper {inhabitationReasoning := true}

set_option trace.duper.timeout.debug true in
theorem forall_apply_eq_imp_iff2 {f : α → β} {p : β → Prop} :
  (∀ b a, f a = b → p b) ↔ ∀ a, p (f a) := by sorry -- duper {inhabitationReasoning := true}

theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
  ∃ a, p a ∧ q (f a) → (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) := by duper

theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
  ∃ a, p (f a) → (∃ b, (∃ a, f a = b) ∧ p b) := by duper

--------------------------------------------------------------------
theorem forall₂_true_iff1 {β : α → Sort} : (∀ a, β a → True) ↔ True := by duper [*]

-- Look into why Duper can solve `forall₂_true_iff1` but not `forall₂_true_iff2`
theorem forall₂_true_iff2 {β : α → Sort _} : (∀ a, β a → True) ↔ True := by duper [*]
