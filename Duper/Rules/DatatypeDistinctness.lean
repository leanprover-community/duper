import Duper.Simp
import Duper.Util.ProofReconstruction

set_option linter.unusedVariables false

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta

initialize Lean.registerTraceClass `duper.rule.datatypeDistinctness

/-- Returns `none` if `lit` does not compare distinct constructors, returns `some false` if `lit` says two distinct
    constructors are equal, and returns `some true` if `lit` says two distinct constructors are not equal. -/
def litComparesDistinctConstructors (lit : Lit) : MetaM (Option Bool) := do
  let litTyIsInductive ← matchConstInduct lit.ty.getAppFn' (fun _ => pure false) (fun _ _ => pure true)
  if litTyIsInductive then
    trace[duper.rule.datatypeDistinctness] "lit.ty {lit.ty} is an inductive datatype"
    let lhsCtorOpt ← matchConstCtor lit.lhs.getAppFn' (fun _ => pure none) (fun cval lvls => pure (some (cval, lvls)))
    let rhsCtorOpt ← matchConstCtor lit.rhs.getAppFn' (fun _ => pure none) (fun cval lvls => pure (some (cval, lvls)))
    match lhsCtorOpt, rhsCtorOpt with
    | some lhsCtor, some rhsCtor =>
      trace[duper.rule.datatypeDistinctness] "Both lit.lhs {lit.lhs} and lit.rhs {lit.rhs} have constructors as heads"
      if lhsCtor == rhsCtor then return none
      else return !lit.sign
    | _, _ => -- `lit` is not comparing two constructors
      trace[duper.rule.datatypeDistinctness] "Either lit.lhs {lit.lhs} or lit.rhs {lit.rhs} does not have a constructor at its head"
      return none
  else -- `lit.ty` is not an inductive datatype so `lit` cannot be comparing distinct constructors
    trace[duper.rule.datatypeDistinctness] "lit.ty {lit.ty} is not an inductive datatype"
    return none

def mkDatatypeDistinctnessProof (refs : List (Option Nat)) (premises : List Expr) (parents: List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      match ← litComparesDistinctConstructors lit with
      | some true => -- Throw an error because Dist-S⁻ should have been applied, not Dist-S⁺
        throwError "mkDistPosProof :: Found a literal {lit} asserting that two distinct constructors are not equal"
      | some false => -- `lit` equates distinct instructors and should not appear in the final clause `c`
        let matchConstInductK := (fun ival lvls => pure (some (ival.name, ival.numParams, lvls)))
        let some (tyName, numParams, lvls) ← matchConstInduct lit.ty.getAppFn' (fun _ => pure none) matchConstInductK
          | throwError "mkDistPosProof :: Failed to find the inductive datatype corresponding to {lit.ty}"
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          /- The strucure of `noConfusion`'s arguments is as follows (as of `v4.27.0`):
              If `lit.ty` has zero parameters then `noConfusion` takes exactly four arguments:
              - `P : Sort u` which serves as the motive of the `noConfusionType`
              - Two arguments with type `lit.ty`
              - A final argument equating the two previous arguments
              If `lit.ty` has one or more parameters then:
              - `noConfusion` first takes in `P : Sort u` which serves as the motive of the `noConfusionType`. The datatype distinctness inference
                always instantiates `P` with `False`
              - `noConfusion` then takes in `numParams` arguments of the form `param : Type universe_param`. Call this list of parameters `(*)`
              - `noConfusion` then takes in one element of the datatype instantiated with the previous `numParams` parameters.
              - `noConfusion` then takes in another `numParams` arguments of the form `param : Type universe_param`. Call this list of parameters `(**)`
              - `noConfusion` then takes in another element of the datatype instantiated with the previous `numParams` parameters.
              - `noConfusion` then takes in `numParams` proofs that the `i`-th parameter from the first list `(*)` is equal to the `i`-th parameter
                from the second list `(**)`. The datatype distinctness inference instantiates all of these with `rfl`.
              - `noConfusion` finally takes in a proof that the first element of the datatype is equal to the second element of the datatype (this is expressed
                in terms of a heterogeneous equality). The datatype distinctness inference always instantiates this last argument with `heq_of_eq h`. -/
          let noConfusionArgs ←
            if numParams = 0 then
              pure $ #[some (mkConst ``False), none, none, some h]
            else
              pure $ #[some (mkConst ``False)] ++ (Array.range (2 * numParams + 2)).map (fun _ => none) ++
                (← (Array.range numParams).mapM (fun x => do pure $ some (← mkAppOptM ``rfl #[none, some (lit.ty.getAppArgs[x]!)]))) ++ #[some (← mkAppM ``heq_of_eq #[h])]
          let proofCase ← mkAppOptM' (mkConst (.str tyName "noConfusion") (0 :: lvls)) noConfusionArgs
          let proofCase := mkApp2 (mkConst ``False.elim [levelZero]) body proofCase
          Meta.mkLambdaFVars #[h] proofCase
        proofCases := proofCases.push proofCase
      | none => -- refs[i] should have the value (some j) where parentLits[i] == c[j]
        match refs[i]! with
        | none =>
          throwError "There is a bug in mkDistPosProof (The refs invariant is not satisfied)"
        | some j =>
          let proofCase ← Meta.withLocalDeclD `h parentLits[i]!.toExpr fun h => do
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
          proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Implements the Dist-S⁺ and Dist-S⁻ rules described in https://arxiv.org/pdf/1611.02908 -/
def datatypeDistinctness : MSimpRule := fun c => do
  let c ← loadClause c
  /- Spec for newLits and refs:
     - If c.lits[i] equates distinct constructors (e.g. has the form `f s = g t` where `f` and `g` are constructors),
       then refs[i] = none
     - If c.lits[i] does not equate distinct constructors, then refs[i] = some j where newLits[j] = c.lits[i] -/
  let mut newLits : List Lit := []
  let mut refs : List (Option Nat) := []
  for lit in c.lits do
    match ← litComparesDistinctConstructors lit with
    | some true => -- Apply Dist-S⁻ rule and delete the clause
      trace[duper.rule.datatypeDistinctness] "datatypeDistinctness- used to remove {c.lits} (due to lit: {lit})"
      return some #[]
    | some false => -- Apply Dist-S⁺ rule and remove `lit` from the clause
      refs := none :: refs
    | none =>
      refs := (some newLits.length) :: refs
      newLits := lit :: newLits
  -- To achieve the desired spec for newLits and refs, I must reverse them
  newLits := newLits.reverse
  refs := refs.reverse
  if (newLits.length = c.lits.size) then
    return none
  else
    trace[duper.rule.datatypeDistinctness] "datatypeDistinctness+ applied with the newLits: {newLits}"
    let yc ← yieldClause (MClause.mk newLits.toArray) "datatypeDistinctness+" (some (mkDatatypeDistinctnessProof refs))
    return some #[yc]

end Duper
