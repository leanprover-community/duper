import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

namespace Schroedinger
open RuleM
open Lean

-- move to proof reconstruction file
/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n] → target`, given proofs (`casesProofs`) of `lits[i] → target` -/
def orCases (lits : Array Expr) (target : Expr) (caseProofs : Array Expr) : MetaM Expr := do
  let mut ors := #[lits[lits.size - 1]]
  for l in [2:lits.size+1] do
    ors := ors.push (mkApp2 (mkConst ``Or) lits[lits.size - l] ors[ors.size-1])
  let mut r ← caseProofs[caseProofs.size - 1]
  for k in [2:caseProofs.size+1] do
    let newOne ← caseProofs[caseProofs.size - k]
    r ← Meta.withLocalDeclD `h ors[k-1] fun h => do
      let p := mkApp6
        (mkConst ``Or.elim)
        lits[lits.size - k]
        ors[k-2]
        target
        h
        newOne
        r
      Meta.mkLambdaFVars #[h] p
  return r

-- move to proof reconstruction file
/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n]`, given a `proof` of `lits[i]` -/
def orIntro (lits : Array Expr) (i : Nat) (proof : Expr) : MetaM Expr := do
  let mut tyR := lits[lits.size-1]
  for j in [2:lits.size-i] do
    tyR := mkApp2 (mkConst ``Or) lits[lits.size - j] tyR
  let mut proofRight := ←
    if i != lits.size - 1 then
      mkApp3 (mkConst ``Or.inl) lits[i] tyR proof
    else
      proof
  if i != lits.size - 1 then
    tyR := mkApp2 (mkConst ``Or) lits[i] tyR
  for j in [lits.size-i+1:lits.size+1] do
    proofRight := mkApp3 (mkConst ``Or.inr) lits[lits.size-j] tyR proofRight
    tyR := mkApp2 (mkConst ``Or) lits[lits.size-j] tyR
  return proofRight

end Schroedinger