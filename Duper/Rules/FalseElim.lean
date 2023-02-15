import Duper.Simp
import Duper.Util.ProofReconstruction
import Lean.Meta.Basic

namespace Duper
open RuleM
open SimpResult
open Lean

initialize registerTraceClass `Rule.falseElim

/-- Determines whether a literal has can be unified with the form `False = True` or `True = False`. If it can
    be, then the substitution necessary to achieve that match is applied (if the match is unsuccessful, then
    the MCtx remains unchanged) -/
def isFalseLiteral (lit : Lit) : MetaM Bool := do
  if ← Meta.unify #[(lit.lhs, mkConst ``False), (lit.rhs, mkConst ``True)] then return true
  else if ← Meta.unify #[(lit.lhs, mkConst ``True), (lit.rhs, mkConst ``False)] then return true
  else return false

theorem false_ne_true (h : False = True) : False := by rw [h]; exact ⟨⟩
theorem true_ne_false (h : True = False) : False := by rw [← h]; exact ⟨⟩

def mkFalseElimProof (i : Nat) (premises : List Expr) (parents : List ProofParent) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises) ← instantiatePremises parents premises xs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if i == j then
        if lit.lhs == mkConst ``True then -- lit unified with `True = False`
          let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
            let proofCase := mkApp (mkConst ``true_ne_false) h
            let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
            Meta.mkLambdaFVars #[h] proofCase
          caseProofs := caseProofs.push pr
        else -- lit unified with `False = True`
          let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
            let proofCase := mkApp (mkConst ``false_ne_true) h
            let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
            Meta.mkLambdaFVars #[h] proofCase
          caseProofs := caseProofs.push pr
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofs := caseProofs.push pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def falseElimAtLit (given : Clause) (c : MClause) (i : Nat) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]!
    let eligibility ← eligibilityPreUnificationCheck c i
    if eligibility == Eligibility.notEligible then return #[]
    let loaded ← getLoadedClauses
    let ug ← runMetaAsRuleM $ DUnif.UnifierGenerator.fromMetaMProcedure (isFalseLiteral lit)
    let yC := do
      setLoadedClauses loaded
      if (not $ ← eligibilityPostUnificationCheck c i eligibility (strict := true)) then return none
      let c := c.eraseLit i
      trace[Rule.falseElim] "Successfully yielded {c.lits} by removing literal {i}"
      yieldClause c "falseElim" $ some (mkFalseElimProof i)
    return #[⟨ug, given, yC⟩]

/-- If there is a substitution σ and literal l in c such that σ(l) equates `True` and `False`, then
    falseElim yields the clause obtained by removing l from c and applying sigma to the rest of c -/
def falseElim (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[Rule.falseElim] "Attempting to apply falseElim to {c.lits}"
  let mut streams := #[]
  for i in [:c.lits.size] do
    if c.lits[i]!.sign then
      let str ← falseElimAtLit given c i
      streams := streams.append str
  return streams

end Duper