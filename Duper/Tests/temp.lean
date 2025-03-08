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
