import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open SimpResult
open Lean

initialize Lean.registerTraceClass `Rule.elimDupLit

def mkElimDupLitProof (refs : Array (Nat × Bool)) (premises : List Expr) (parents: List ProofParent) (c : Clause) 
  : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let proofCase ← Meta.withLocalDeclD `h parentLits[i]!.toExpr fun h => do
        let (refsI, isFlipped) := refs[i]!
        if isFlipped then
          let appropriateSymmRule :=
            if (parentLits[i]!.sign) then ``Eq.symm
            else ``Ne.symm
          let hSymm ← Meta.mkAppM appropriateSymmRule #[h]
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) refsI hSymm
        else
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) refsI h
      proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    let proof ← Meta.mkLambdaFVars xs $ mkApp proof appliedPremise
    return proof

/-- Remove duplicate literals -/
def elimDupLit : MSimpRule := fun c => do
  let c ← loadClause c
  let mut newLits : Array Lit := Array.mkEmpty c.lits.size
  let mut refs : Array (Nat × Bool) := Array.mkEmpty c.lits.size
  for i in [:c.lits.size] do
    match newLits.getIdx? c.lits[i]! with
    | some j => do
      trace[Rule.elimDupLit] "Accessed nonsymmetry case"
      refs := refs.push (j, false) -- j is index of duplicate lit, false indicates the literal is not flipped
    | none => do
      match newLits.getIdx? (c.lits[i]!.symm) with
      | some j => do
        trace[Rule.elimDupLit] "Accessed symmetry case"
        refs := refs.push (j, true) -- j is index of duplicate lit, false indicates the literal is flipped
      | none => do
        refs := refs.push (newLits.size, false)
        newLits := newLits.push c.lits[i]!
  
  if newLits.size = c.lits.size then
    return none
  else
    let cp ← yieldClause (MClause.mk newLits) "eliminate duplicate literals"
      (some (mkElimDupLitProof refs))
    return some #[cp]

end Duper