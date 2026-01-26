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
def Auto.duperPort (lemmas inhLemmas : Array Lemma) : MetaM Expr := do
  let (formulas, extraFormulas) ← Duper.autoLemmasToFormulas lemmas
  let formulas := formulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  let extraFormulas := extraFormulas.map (fun f => (f.1, f.2.1, f.2.2.1, f.2.2.2, none))
  Duper.runDuperPortfolioMode formulas extraFormulas .none
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      preprocessing := Duper.PreprocessingOption.NoPreprocessing, -- It would be redundant to enable Auto's preprocessing for Auto calls
      includeExpensiveRules := none,
      selFunction := none
    }
    .none

-- Misc Duper issue:
example (hFin : ∀ x : Nat, ∀ y : Nat, x < y ↔ ∃ a : Fin x, a.1 = x)
  (lt_succ : ∀ n : Nat, n < n.succ) (lt_trans : ∀ x y z : Nat, x < y → y < z → x < z) :
  ∃ a : Fin (Nat.succ (Nat.succ 0)), a.1 = 0 := by
  sorry -- duper [*] {portfolioInstance := 7} -- This causes a stack overflow

inductive myProd (t1 t2 : Type _)
| mk : t1 → t2 → myProd t1 t2

open myProd

-- `unfoldProj` bug in lean-auto
example (sum : myProd Int Int → Int)
  (hSum : ∀ x : Int, ∀ y : Int, sum (mk x y) = x + y)
  (x : myProd Int Int) : ∃ y : myProd Int Int, sum x < sum y := by
  have test :
    let _mk_sel0 : myProd Int Int → Int := myProd.rec (motive := fun _ => Int) fun arg0 arg1 => arg0
    _mk_sel0 x = 0 := sorry -- This triggers `unfoldProj :: myProd is not a structure`
  duper [*] {portfolioInstance := 1}

-- PANIC at Duper.RootCFPTrie.transformToUntypedFirstOrderTerm Duper.Fingerprint:162:27...
example (x y : Nat) (hx : x ≤ 100) (hy : y ≤ 100)
  (hxy : x * y ≥ 7625) : x + y ≥ 150 := by
  have :
    have _let_1 := Int.ofNat x + Int.ofNat y;
    ¬Int.ofNat 150 ≤ _let_1 → ¬_let_1 ≥ Int.ofNat 150 :=
    sorry
  have :
    (Eq (α := Nat → Prop) (fun (a : Nat) => True) fun (_n : Nat) => Int.ofNat _n ≥ Int.ofNat 0) ∧ (fun (a : Nat) => True) x →
      Int.ofNat x ≥ Int.ofNat 0 :=
    sorry
  have : Int.ofNat y ≤ Int.ofNat 100 → ¬Int.ofNat y ≥ Int.ofNat 101 := sorry
  have :
    (Eq (α := Nat → Prop) (fun (a : Nat) => True) fun (_n : Nat) => Int.ofNat _n ≥ Int.ofNat 0) ∧ (fun (a : Nat) => True) y →
      Int.ofNat y ≥ Int.ofNat 0 :=
    sorry
  have : Int.ofNat 7625 ≤ Int.ofNat x * Int.ofNat y → Int.ofNat x * Int.ofNat y ≥ Int.ofNat 7625 := sorry
  have : Int.ofNat x ≤ Int.ofNat 100 → ¬Int.ofNat x ≥ Int.ofNat 101 := sorry
  have : (¬Int.ofNat x ≥ Int.ofNat 0 ∨ Int.ofNat x = Int.ofNat 0) ∨ Int.ofNat x ≥ Int.ofNat 1 := sorry
  have : Int.ofNat x > Int.ofNat 0 → Int.ofNat x ≥ Int.ofNat 1 := sorry
  have :
    have _let_1 := Int.ofNat x * Int.ofNat y;
    ¬_let_1 ≥ Int.ofNat 7625 ∨ ¬_let_1 = Int.ofNat 0 :=
    sorry
  have : Int.ofNat y = Int.ofNat 0 → Int.ofNat x * Int.ofNat y = Int.ofNat 0 := sorry
  have :
    have _let_1 := Int.ofNat x * Int.ofNat y;
    have _let_2 := -Int.ofNat 1 * _let_1;
    (_let_1 ≥ Int.ofNat 7625 ∧ Int.ofNat 101 * Int.ofNat y + _let_2 ≥ Int.ofNat 1) ∧
        Int.ofNat 101 * Int.ofNat x + _let_2 ≥ Int.ofNat 1 →
      Int.ofNat x + Int.ofNat y ≥ Int.ofNat 150 :=
    sorry
  have : (¬Int.ofNat y ≥ Int.ofNat 0 ∨ Int.ofNat y = Int.ofNat 0) ∨ Int.ofNat y ≥ Int.ofNat 1 := sorry
  have : Int.ofNat y > Int.ofNat 0 → Int.ofNat y ≥ Int.ofNat 1 := sorry
  have : Int.ofNat x = Int.ofNat 0 → Int.ofNat x * Int.ofNat y = Int.ofNat 0 := sorry
  duper [*]
