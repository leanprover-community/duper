import Duper.Simp
import Duper.Util.ProofReconstruction

set_option linter.unusedVariables false

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta

initialize Lean.registerTraceClass `duper.rule.datatypeInjectivity

/-- Returns `none` if `lit` does not compare identical constructors, returns `some true` if `lit` says two identical
    constructors are equal, and returns `some false` if `lit` says two identical constructors are not equal. -/
def litComparesIdenticalConstructors (lit : Lit) : MetaM (Option Bool) := do
  let litTyIsInductive ← matchConstInduct lit.ty.getAppFn' (fun _ => pure false) (fun _ _ => pure true)
  if litTyIsInductive then
    trace[duper.rule.datatypeInjectivity] "lit.ty {lit.ty} is an inductive datatype"
    let lhsCtorOpt ← matchConstCtor lit.lhs.getAppFn' (fun _ => pure none) (fun cval lvls => pure (some (cval, lvls)))
    let rhsCtorOpt ← matchConstCtor lit.rhs.getAppFn' (fun _ => pure none) (fun cval lvls => pure (some (cval, lvls)))
    match lhsCtorOpt, rhsCtorOpt with
    | some lhsCtor, some rhsCtor =>
      trace[duper.rule.datatypeInjectivity] "Both lit.lhs {lit.lhs} and lit.rhs {lit.rhs} have constructors as heads"
      if lhsCtor == rhsCtor then return lit.sign
      else return none
    | _, _ => -- `lit` is not comparing two constructors
      trace[duper.rule.datatypeInjectivity] "Either lit.lhs {lit.lhs} or lit.rhs {lit.rhs} does not have a constructor at its head"
      return none
  else -- `lit.ty` is not an inductive datatype so `lit` cannot be comparing identical constructors
    trace[duper.rule.datatypeInjectivity] "lit.ty {lit.ty} is not an inductive datatype"
    return none

def mkDatatypeInjectivityPosProof (removedLitNum ctorArgNum : Nat) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if i == removedLitNum then -- `lit` is the constructor equality to be replaced with the argument equality
        let matchConstCtorK := (fun cval lvls => pure (some (cval, lvls)))
        let some (sharedCtor, sharedCtorLvls) ← matchConstCtor lit.lhs.getAppFn' (fun _ => pure none) matchConstCtorK
          | throwError "mkDatatypeInjectivityPosProof :: Failed to find the constructor at the head of both sides of {lit}"
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          /- injEq first takes `numParams` arguments for the inductive datatype's parameters, then the lhs constructor's arguments
             (not including the datatype's parameter arguments), and finally, rhs constructor's arguments (again not including the
             datatype's parameter arguments) -/
          let datatypeParamArgs := (Array.range sharedCtor.numParams).map (fun _ => none)
          let lhsArgs := (lit.lhs.consumeMData.getAppArgs.toList.drop sharedCtor.numParams).map (fun x => some x)
          let rhsArgs := (lit.rhs.consumeMData.getAppArgs.toList.drop sharedCtor.numParams).map (fun x => some x)
          let injEqArgs := datatypeParamArgs ++ lhsArgs.toArray ++ rhsArgs.toArray
          let proofCase ← mkAppOptM' (mkConst (.str sharedCtor.name "injEq") sharedCtorLvls) injEqArgs
          let proofCase ← Meta.mkAppM ``Eq.mp #[proofCase, h]
          let proofCase ← andGet (getConjunctiveHypotheses (← inferType proofCase)) ctorArgNum proofCase
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i proofCase
        proofCases := proofCases.push proofCase
      else -- `lit` is not the constructor equality that is currently being modified
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
        proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/- Note: This proof reconstruction procedure will fail if it is run on a constructor inequality where the constructor
   contains zero arguments (e.g. `[] ≠ []`). However, this should never occur so long as Saturate.lean's `forwardSimpRules`
   array contains `elimResolvedLit` before `datatypeInjectivity` -/
def mkDatatypeInjectivityNegProof (removedLitNum : Nat) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if i == removedLitNum then -- `lit` is the constructor inequality to be replaced with the argument inequality disjunction
        let matchConstCtorK := (fun cval lvls => pure (some (cval, lvls)))
        let some (sharedCtor, sharedCtorLvls) ← matchConstCtor lit.lhs.getAppFn' (fun _ => pure none) matchConstCtorK
          | throwError "mkDatatypeInjectivityNegProof :: Failed to find the constructor at the head of both sides of {lit}"
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          /- injEq first takes `numParams` arguments for the inductive datatype's parameters, then the lhs constructor's arguments
             (not including the datatype's parameter arguments), and finally, rhs constructor's arguments (again not including the
             datatype's parameter arguments) -/
          let datatypeParamArgs := (Array.range sharedCtor.numParams).map (fun _ => none)
          let lhsArgs := (lit.lhs.consumeMData.getAppArgs.toList.drop sharedCtor.numParams).map (fun x => some x)
          let rhsArgs := (lit.rhs.consumeMData.getAppArgs.toList.drop sharedCtor.numParams).map (fun x => some x)
          let injEqArgs := datatypeParamArgs ++ lhsArgs.toArray ++ rhsArgs.toArray
          let injEq ← mkAppOptM' (mkConst (.str sharedCtor.name "injEq") sharedCtorLvls) injEqArgs
          -- `injEq : (constructor x1 y1 = constructor x2 y2) = (x1 = x2 ∧ y1 = y2)`
          let argEqualities ←
            match ← inferType injEq with
            | Expr.app (Expr.app (Expr.app (Expr.const ``Eq [_]) _) _) e2 => pure e2
            | _ => throwError "mkDatatypeInjectivityNegProof :: Type of {injEq} is not an equality as expected"
          let propMVar ← mkFreshExprMVar (mkSort Lean.Level.zero)
          let abstrLam ← mkLambdaFVars #[propMVar] $ ← mkAppM ``Eq #[← mkAppM ``Not #[propMVar], ← mkAppM ``Not #[argEqualities]]
          let proofCase ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[abstrLam, injEq], ← mkAppM ``Eq.refl #[← mkAppM ``Not #[argEqualities]]]
          let proofCase ← mkAppM ``Eq.mp #[proofCase, h]
          let proofCase ← notAndDistribute (← inferType proofCase) proofCase
          Meta.mkLambdaFVars #[h] $ ← orSubclause (cLits.map Lit.toExpr) (1 + cLits.size - parentLits.size) proofCase
        proofCases := proofCases.push proofCase
      else -- `lit` is not the constructor inequality that is currently being modified
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if i ≥ removedLitNum then i - 1 else i
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Implements the injectivity rules described in section 6.3 of https://arxiv.org/pdf/1611.02908 -/
def datatypeInjectivity : MSimpRule := fun c => do
  let c ← loadClause c
  for i in [:c.lits.size] do
    let lit := c.lits[i]!
    match ← litComparesIdenticalConstructors lit with
    | some true => -- datatypeInjectivity⁺ (the first of the rules described in above paper)
      let lhsArgs := lit.lhs.consumeMData.getAppArgs
      let rhsArgs := lit.rhs.consumeMData.getAppArgs
      let numArgs ←
        if lhsArgs.size != rhsArgs.size then
          throwError "datatypeInjectivity: The same constructor takes different numbers of arguments in {lit.lhs} and {lit.rhs}"
        else pure lhsArgs.size
      let numTyParams ← matchConstInduct lit.ty.getAppFn' (fun _ => pure 0) (fun ival _ => pure ival.numParams)
      -- Create `numArgs` conclusions each of the form `cWithoutLit ∨ lhsArgs[k] = rhsArgs[k]` (where `numTyParams ≤ k < numArgs`)
      let mut conclusions : Array (Clause × Proof) := #[]
      for k in [numTyParams:numArgs] do --Iterate over actual constructor arguments (skipping the inductive datatype's parameters)
        let lhsArg := lhsArgs[k]!
        let rhsArg := rhsArgs[k]!
        let ty ← inferType lhsArg
        let tyLvl := (← inferType ty).sortLevel!
        let argEqLit : Lit := {
          sign := true,
          lvl := tyLvl,
          ty := ty,
          lhs := lhsArg,
          rhs := rhsArg
        }
        let mclause := MClause.mk $ c.lits.set! i argEqLit
        conclusions := conclusions.push $ ← yieldClause mclause "datatypeInjectivity+" $ mkDatatypeInjectivityPosProof i (k - numTyParams)
      trace[duper.rule.datatypeInjectivity] "datatypeInjectivity+ applied to {c.lits} to create conclusions {conclusions.map (fun x => x.1)}"
      return some conclusions
    | some false => -- datatypeInjectivity⁻ (the second of the rules described in above paper)
      let lhsArgs := lit.lhs.consumeMData.getAppArgs
      let rhsArgs := lit.rhs.consumeMData.getAppArgs
      let numArgs ←
        if lhsArgs.size != rhsArgs.size then
          throwError "datatypeInjectivity: The same constructor takes different numbers of arguments in {lit.lhs} and {lit.rhs}"
        else pure lhsArgs.size
      let mut res : Array Lit := #[]
      for j in [:c.lits.size] do
        if i != j then res := res.push c.lits[j]!
      let numTyParams ← matchConstInduct lit.ty.getAppFn' (fun _ => pure 0) (fun ival _ => pure ival.numParams)
      -- For each `k` such that `numTyParams ≤ k < numArgs`, add the literal `lhsArgs[k] ≠ rhsArgs[k]` onto `res`
      for k in [numTyParams:numArgs] do
        let lhsArg := lhsArgs[k]!
        let rhsArg := rhsArgs[k]!
        let ty ← inferType lhsArg
        let tyLvl := (← inferType ty).sortLevel!
        let kLit : Lit := {
          sign := false,
          lvl := tyLvl,
          ty := ty,
          lhs := lhsArg,
          rhs := rhsArg
        }
        res := res.push kLit
      let yC ← yieldClause (MClause.mk res) "datatypeInjectivity-" $ mkDatatypeInjectivityNegProof i
      trace[duper.rule.datatypeInjectivity] "datatypeInjectivity- applied to {c.lits} to yield {yC.1}"
      return some #[yC]
    | none => continue
  return none
