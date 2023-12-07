import Duper.Simp
import Duper.Util.ProofReconstruction
import Lean.Meta.Basic

namespace Duper
open RuleM
open SimpResult
open Lean
open Meta

initialize Lean.registerTraceClass `duper.rule.decElim

/-- Checks whether a literal is decidably false. Returns true if the literal is decidably false and false otherwise. -/
def isDecidablyFalse (lit : Lit) : MetaM Bool := do
  try
    let d ← mkDecide lit.toExpr
    let d ← instantiateMVars d
    let r ← withDefault <| whnf d
    return r.isConstOf ``false
  catch _ =>
    return false

def mkDecElimProof (refs : List (Option Nat)) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    if refs.length != parentLits.size then throwError "mkDecElimProof error: {refs} and {parentLits} have different sizes"

    let mut caseProofs := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      match refs[i]! with
      | none =>
        -- This is adapted from the internals of `decide`
        let expectedType := lit.toExpr
        trace[duper.rule.decElim] "Trying to decide {expectedType}"
        let d ← mkDecide expectedType
        let d ← instantiateMVars d
        let r ← withDefault <| whnf d
        unless r.isConstOf ``false do
          throwError "mkDecElimProof: Failed to reduce to 'false'{indentExpr r}"
        trace[duper.rule.decElim] "{d} is false"
        let s := d.appArg! -- get instance from `d`
        let rflPrf ← mkEqRefl (toExpr false)
        let proofCase := mkApp3 (Lean.mkConst ``of_decide_eq_false) expectedType s rflPrf
        trace[duper.rule.decElim] "Built {proofCase} proving {d} is false"
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let proofCase := mkApp proofCase h
          let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
          Meta.mkLambdaFVars #[h] proofCase
        caseProofs := caseProofs.push pr
      | some j =>
        -- need proof of `L_i → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofs := caseProofs.push pr
    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

/-- If there are any literals in `c` that are decidably true, then `decElim` removes `c`. Otherwise, if there are
    any literals in `c` that are decidably false, then `decElim` yields the clause obtained by removing all such literals. -/
def decElim : MSimpRule := fun c => do
  let c ← loadClause c
  /-
    Spec for newLits and refs:
    If c.lits[i] is decidably false, then refs[i] = none
    If c.lits[i] isn't decidably false, then refs[i] = some j where newLits[j] = c.lits[i]
  -/
  let mut newLits : List Lit := []
  let mut refs : List (Option Nat) := []
  for lit in c.lits do
    if ← isDecidablyFalse lit then -- Remove the decidably false literal from the clause
      refs := none :: refs
    else
      refs := (some newLits.length) :: refs
      newLits := lit :: newLits
  -- To achieve the desired spec for newLits and refs, I must reverse them
  newLits := newLits.reverse
  refs := refs.reverse
  trace[duper.rule.decElim] "newLits: {newLits}, refs: {refs}"
  if (newLits.length = c.lits.size) then
    return none
  else
    let resultClause ← yieldClause (MClause.mk newLits.toArray) "decidable false elimination"
      (some (mkDecElimProof refs))
    return some #[resultClause]

end Duper
