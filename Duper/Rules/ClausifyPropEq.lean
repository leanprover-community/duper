import Duper.RuleM
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean
open Meta

initialize Lean.registerTraceClass `Rule.clausifyPropEq

theorem c1_soundness {p : Prop} {q : Prop} (h : p = q) : (p = True) ∨ (q = False) := by
  rw [h]
  exact Classical.propComplete q

/-  From a parent clause that has the literal p = q, we want to prove c which is identical to the parent clause except:
    1. The literal p = q is removed from c
    2. The literals p = True and q = False are appended to the end of c (in that order)
-/
def mkC1Proof (i : Nat) (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        --lit has the form p = q and is the propositional equality that is currently being clausified
        --We want to derive `p = q -> L_1 ∨ ... ∨ L_{n-1} ∨ L_n` by showing p = q -> L_{n-1} ∨ L_n where L_{n-1} is p = True and L_n = q = False
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let proofCase ← Meta.mkAppM ``c1_soundness #[h]
          Meta.mkLambdaFVars #[h] $ ← orSubclause (cLits.map Lit.toExpr) 2 proofCase
        proofCases := proofCases.push proofCase
      else
        --lit is not the propositional equality that is currently being clausified
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        proofCases := proofCases.push proofCase
    let r ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

theorem c2_soundness {p : Prop} {q : Prop} (h : p = q) : (p = False) ∨ (q = True) := by
  rw [h]
  cases Classical.propComplete q with
  | inl q_true => exact Or.intro_right _ q_true
  | inr q_false => exact Or.intro_left _ q_false

/-  From a parent clause that has the literal p = q, we want to prove c which is identical to the parent clause except:
    1. The literal p = q is removed from c
    2. The literals p = False and q = True are appended to the end of c (in that order)
-/
def mkC2Proof (i : Nat) (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        --lit has the form p = q and is the propositional equality that is currently being clausified
        --We want to derive `p = q -> L_1 ∨ ... ∨ L_{n-1} ∨ L_n` by showing p = q -> L_{n-1} ∨ L_n where L_{n-1} is p = False and L_n = q = True
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let proofCase ← Meta.mkAppM ``c2_soundness #[h]
          Meta.mkLambdaFVars #[h] $ ← orSubclause (cLits.map Lit.toExpr) 2 proofCase
        proofCases := proofCases.push proofCase
      else
        --lit is not the propositional equality that is currently being clausified
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        proofCases := proofCases.push proofCase
    let r ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def clausifyPropEq (given : Clause)(c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[Rule.clausifyPropEq] "ClausifyPropEq inferences with {c.lits}"
  let mut streams := #[]
  for i in [:c.lits.size] do
    let lit := c.lits[i]!
    if lit.sign = true && lit.ty.isProp && litSelectedOrNothingSelected c i then
      -- TODO: check both sides?
      if ¬ lit.rhs.isConstOf ``True && ¬ lit.rhs.isConstOf ``False then
        let c' := c.eraseLit i
        let c1 := c'.appendLits #[Lit.fromSingleExpr lit.lhs true, Lit.fromSingleExpr lit.rhs false]
        let c2 := c'.appendLits #[Lit.fromSingleExpr lit.lhs false, Lit.fromSingleExpr lit.rhs true]
        trace[Rule.clausifyPropEq] "clausifyPropEq called on {lit} in {c.lits} to produce {c1.lits} and {c2.lits}"
        let loaded ← getLoadedClauses
        let ug ← unifierGenerator #[]
        let yield1 := do
          setLoadedClauses loaded
          yieldClause c1 "clausify Prop equality" (mkProof := some (mkC1Proof i))
        let yield2 := do
          setLoadedClauses loaded
          yieldClause c2 "clausify Prop equality" (mkProof := some (mkC2Proof i))
        streams := streams.append #[ClauseStream.mk ug given yield1, ClauseStream.mk ug given yield2]
  return streams

end Duper