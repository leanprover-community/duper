import Auto.Tactic
import Duper.Tactic

open Lean Auto

def Auto.duperRaw (lemmas : Array Lemma) : MetaM Expr := do
  /- Adding `isFromGoal := false` to each formula because there is no means of distinguishing goal formulas
     from non-goal formulas in this context -/
  let lemmas : Array (Expr × Expr × Array Name × Bool) ←
    lemmas.mapM (fun ⟨proof, ty, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], false))
  runDuper lemmas.data 0

def Auto.duperPort (lemmas : Array Lemma) : MetaM Expr := do
  /- Adding `isFromGoal := false` to each formula because there is no means of distinguishing goal formulas
     from non-goal formulas in this context -/
  let formulas : Array (Expr × Expr × Array Name × Bool) ←
    lemmas.mapM (fun ⟨proof, ty, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], false))
  runDuperPortfolioMode formulas.data .none
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      preprocessing := PreprocessingOption.NoPreprocessing, -- It would be redundant to enable Auto's preprocessing for Auto calls
      includeExpensiveRules := none,
      selFunction := none
    }
    .none
