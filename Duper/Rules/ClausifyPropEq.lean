import Duper.ProverM
import Duper.RuleM
import Duper.Selection

namespace Duper
open RuleM

def clausifyPropEq (c : MClause) : RuleM Unit := do
  for i in [:c.lits.size] do
    let lit := c.lits[i]
    if lit.sign = true ∧ lit.ty.isProp ∧ litSelectedOrNothingSelected c i then
      -- TODO: check both sides?
      if ¬ lit.rhs.isConstOf ``True ∧ ¬ lit.rhs.isConstOf ``False then
        let c' := c.eraseLit i
        let c1 := c'.appendLits #[Lit.fromExpr lit.lhs true, Lit.fromExpr lit.rhs false]
        let c2 := c'.appendLits #[Lit.fromExpr lit.lhs false, Lit.fromExpr lit.rhs true]
        yieldClause c1 "clausify Prop equality" (mkProof := none) --TODO
        yieldClause c2 "clausify Prop equality" (mkProof := none) --TODO

open ProverM

def performClausifyPropEq (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "ClausifyPropEq inferences with {givenClause}"
  performInference clausifyPropEq givenClause

end Duper