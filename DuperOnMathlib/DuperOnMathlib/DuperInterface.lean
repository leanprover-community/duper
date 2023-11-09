import Auto.Tactic
import Duper.Tactic

open Lean Auto

def Auto.duperRaw (lemmas : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name) ← lemmas.mapM
    (fun ⟨proof, ty, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[]))
  runDuper lemmas.data 0

def Auto.duperPort (lemmas : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name) ← lemmas.mapM
    (fun ⟨proof, ty, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[]))
  runDuperPortfolioMode lemmas.data
    { portfolioMode := true,
      portfolioInstance := none,
      inhabitationReasoning := none,
      monomorphization := false, -- It would be redundant to enable monomorphization for Auto
      includeExpensiveRules := none,
      selFunction := none
    }
    .none
