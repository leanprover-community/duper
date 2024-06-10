import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta

initialize Lean.registerTraceClass `duper.rule.datatypeDistinctness

def litEquatesDistinctConstructors (lit : Lit) : MetaM Bool := do
  let litTyIsInductive ← matchConstInduct lit.ty.getAppFn' (fun _ => pure false) (fun _ _ => pure true)
  if litTyIsInductive then
    trace[duper.rule.datatypeDistinctness] "lit.ty {lit.ty} is an inductive datatype"
    let lhsCtorOpt ← matchConstCtor lit.lhs.getAppFn' (fun _ => pure none) (fun cval lvls => pure (some (cval, lvls)))
    let rhsCtorOpt ← matchConstCtor lit.rhs.getAppFn' (fun _ => pure none) (fun cval lvls => pure (some (cval, lvls)))
    match lhsCtorOpt, rhsCtorOpt with
    | some lhsCtor, some rhsCtor =>
      trace[duper.rule.datatypeDistinctness] "Both lit.lhs {lit.lhs} and lit.rhs {lit.rhs} have constructors as heads"
      return lhsCtor != rhsCtor
    | _, _ =>
      trace[duper.rule.datatypeDistinctness] "Either lit.lhs {lit.lhs} or lit.rhs {lit.rhs} does not have a constructor at its head"
      return false
  else -- `lit.ty` is not an inductive datatype so `lit` cannot be equating distinct constructors
    trace[duper.rule.datatypeDistinctness] "lit.ty {lit.ty} is not an inductive datatype"
    return false

def mkDistPosProof (refs : List (Option Nat)) (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if ← litEquatesDistinctConstructors lit then
        let matchConstInductK := (fun ival lvls => pure (some (ival.name, ival.numParams, lvls)))
        let some (tyName, numParams, lvls) ← matchConstInduct lit.ty.getAppFn' (fun _ => pure none) matchConstInductK
          | throwError "mkDistPosProof :: Failed to find the inductive datatype corresponding to {lit.ty}"
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let noConfusionArgs := #[some (mkConst ``False), none, none, some h]
          -- noConfusion first takes `numParams` arguments for parameters, so we need to add that many `none`s to the front of `noConfusionArgs`
          let noConfusionArgs := (Array.range numParams).map (fun _ => none) ++ noConfusionArgs
          let proofCase ← mkAppOptM' (mkConst (.str tyName "noConfusion") (0 :: lvls)) noConfusionArgs
          let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
          Meta.mkLambdaFVars #[h] proofCase
        proofCases := proofCases.push proofCase
      else -- refs[i] should have the value (some j) where parentLits[i] == c[j]
        match refs[i]! with
        | none =>
          panic! "There is a bug in mkDistPosProof (The refs invariant is not satisfied)"
        | some j =>
          let proofCase ← Meta.withLocalDeclD `h parentLits[i]!.toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Implements the Dist-S⁺ rule described in https://arxiv.org/pdf/1611.02908 -/
def distPos : MSimpRule := fun c => do
  let c ← loadClause c
  /- Spec for newLits and refs:
     - If c.lits[i] equates distinct constructors (e.g. has the form `f s = g t` where `f` and `g` are constructors),
       then refs[i] = none
     - If c.lits[i] does not equate distinct constructors, then refs[i] = some j where newLits[j] = c.lits[i] -/
  let mut newLits : List Lit := []
  let mut refs : List (Option Nat) := []
  for lit in c.lits do
    if ← litEquatesDistinctConstructors lit then
      refs := none :: refs
    else
      refs := (some newLits.length) :: refs
      newLits := lit :: newLits
  -- To achieve the desired spec for newLits and refs, I must reverse them
  newLits := newLits.reverse
  refs := refs.reverse
  if (newLits.length = c.lits.size) then
    return none
  else
    trace[duper.rule.datatypeDistinctness] "datatypeDistinctness applied with the newLits: {newLits}"
    let yc ← yieldClause (MClause.mk newLits.toArray) "datatype dist-S+" (some (mkDistPosProof refs))
    return some #[yc]

end Duper
