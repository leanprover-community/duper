module

public import Duper.Simp
public import Duper.Util.ProofReconstruction

public section

set_option linter.unusedVariables false

namespace Duper
open Std
open RuleM
open SimpResult
open Lean
open Meta
open LitSide

initialize Lean.registerTraceClass `duper.rule.datatypeAcyclicity

theorem one_add_ge (n : Nat) : 1 + n > n := by grind

def addAllRight (head : Expr) (xs : Array Expr) : MetaM Expr := do
  xs.foldlM (init := head) fun acc lit => do mkAppM ``Nat.lt_add_right #[← mkAppM ``sizeOf #[lit], acc]

def buildLeftSum (head : Expr) (xs : Array Expr) : MetaM Expr :=
  xs.foldlM (init := head) fun acc lit => mkAppM ``HAdd.hAdd #[acc, lit]

def liftAddRight (eq s : Expr) : MetaM Expr := do
  let f ← withLocalDeclD `t (mkConst ``Nat) fun t => do
    mkLambdaFVars #[t] (← mkAppM ``HAdd.hAdd #[t, s])
  mkAppM ``congrArg #[f, eq]

def flattenAddRight (head : Expr) (xs : Array Expr) : MetaM Expr := do
  let n := xs.size
  if n ≤ 1 then
    return ← mkAppM ``Eq.refl #[← buildLeftSum head xs]
  let innerSum ← buildLeftSum xs[0]! (xs.extract 1 n)
  let lhs ← mkAppM ``HAdd.hAdd #[head, innerSum]
  let mut eq ← mkAppM ``Eq.refl #[lhs]
  for k in [:n - 1] do
    let stillIn := xs.extract 0 (n - 1 - k)
    let remaining ← buildLeftSum xs[0]! (stillIn.extract 1 stillIn.size)
    let assocSymm ← mkAppM ``Eq.symm #[← mkAppM ``Nat.add_assoc #[head, remaining, xs[n - 1 - k]!]]
    let alreadyOut := xs.extract (n - k) n
    let lifted ← alreadyOut.foldlM (init := assocSymm) liftAddRight
    eq ← mkAppM ``Eq.trans #[eq, lifted]
  return eq

partial def bubbleToLeft (spec : Expr) (sizes : Array Expr) (idx : Nat) : MetaM Expr := do
  if idx = 0 then return spec
  let prefixSum ← buildLeftSum (mkNatLit 1) (sizes.extract 0 (idx - 1))
  let comm ← mkAppM ``Nat.add_right_comm #[prefixSum, sizes[idx - 1]!, sizes[idx]!]
  let suffix := sizes.extract (idx + 1) sizes.size
  let lifted ← suffix.foldlM (init := comm) liftAddRight
  let newSpec ← mkAppM ``Eq.trans #[spec, lifted]
  bubbleToLeft newSpec (sizes.swapIfInBounds (idx - 1) idx) (idx - 1)

/-- Produces a list of (possibly duplicate) constructor subterms for `e` -/
partial def collectConstructorSubterms (e : Expr) : MetaM (Array Expr) := do
  let isConstructor ← matchConstCtor e.getAppFn' (fun _ => pure false) (fun _ _ => pure true)
  if isConstructor then
    let constructorSubterms ← e.getAppArgs.mapM (fun arg => collectConstructorSubterms arg)
    return constructorSubterms.flatten.push e
  else
    return #[e]

/-- Builds a proof of `sizeOf lhs > sizeOf rhs` with `rhs` guaranteed to be a subterm of `lhs` -/
partial def buildGtProof (lhs : Expr) (rhs : Expr) : MetaM Expr := do
  let ctor := lhs.getAppFn'
  let some ctorName := ctor.constName?
    | throwError "datatypeAcyclicity: lhs head is not a constant"
  let ctorType ← inferType ctor
  let explicitLhsArgs ← forallTelescopeReducing ctorType fun binders _ =>
    (binders.zip lhs.getAppArgs).filterMapM fun (b, a) => do
      if (← b.fvarId!.getDecl).binderInfo.isExplicit then pure (some a)
      else pure none
  let specName := ctorName ++ `sizeOf_spec
  unless (← getEnv).contains specName do throwError "datatypeAcyclicity: no sizeOf_spec for {ctorName}"
  let specExpr ← mkConstWithFreshMVarLevels specName
  let specImplicitCount ← forallTelescopeReducing (← inferType specExpr) fun binders _ => do
    let mut count := 0
    for b in binders do
      if !(← b.fvarId!.getDecl).binderInfo.isExplicit then
        count := count + 1
      else
        break
    pure count
  let nones := Array.replicate specImplicitCount none
  let specApplied ← mkAppOptM specName (nones ++ explicitLhsArgs.map some)
  let sizes ← explicitLhsArgs.mapM fun a => mkAppM ``sizeOf #[a]
  match ← explicitLhsArgs.findIdxM? (fun a => isDefEq a rhs) with
  | some rhsIdx => -- base case: `rhsIdx` is where `rhs` was found in the direct subterms of `lhs`
    let rearranged ← bubbleToLeft specApplied sizes rhsIdx
    let oneAddGe ← mkAppM ``one_add_ge #[← mkAppM ``sizeOf #[rhs]]
    let lhsArgsExtra := explicitLhsArgs.eraseIdx! rhsIdx
    let gtProof ← addAllRight oneAddGe lhsArgsExtra
    let rearrangedSymm ← mkAppM ``Eq.symm #[rearranged]
    let motive ← withLocalDeclD `y (mkConst ``Nat) fun y => do
      mkLambdaFVars #[y] (← mkAppM ``LT.lt #[← mkAppM ``sizeOf #[rhs], y])
    mkAppOptM ``Eq.subst #[none, some motive, none, none, some rearrangedSymm, some gtProof]
  | none => -- recursive case: `subtermIdx` is a direct subterm of `lhs` with `rhs` as a subterm
    let some subtermIdx ← explicitLhsArgs.findIdxM? (fun term => do
      let subterms ← collectConstructorSubterms term
      subterms.anyM (fun s => isDefEq s rhs))
      | throwError "datatypeAcyclicity: rhs {rhs} not found among subterms"
    let subterm := explicitLhsArgs[subtermIdx]!
    let subProof ← buildGtProof subterm rhs
    let lhsArgsExtra := explicitLhsArgs.eraseIdx! subtermIdx
    let subProof ← addAllRight subProof lhsArgsExtra
    let subProof ← mkAppM ``Nat.lt_add_left #[mkNatLit 1, subProof]
    let rearranged ← bubbleToLeft specApplied sizes subtermIdx
    let rearrangedSymm ← mkAppM ``Eq.symm #[rearranged]
    let restInOrder := (sizes.extract 0 subtermIdx) ++ (sizes.extract (subtermIdx + 1) sizes.size)
    let parenInner := #[sizes[subtermIdx]!] ++ restInOrder
    let flattenEq ← flattenAddRight (mkNatLit 1) parenInner
    let combined ← mkAppM ``Eq.trans #[flattenEq, rearrangedSymm]
    let sizeOfRhs ← mkAppM ``sizeOf #[rhs]
    let motive ← withLocalDeclD `y (mkConst ``Nat) fun y => do
      mkLambdaFVars #[y] (← mkAppM ``LT.lt #[sizeOfRhs, y])
    mkAppOptM ``Eq.subst #[none, some motive, none, none, some combined, some subProof]

/-- Returns `none` if `lit` does not compare constructor subterms, and returns `some litside` if `lit.litside`
    is a subterm of the constructor it is being compared to. Note that `lit.litside` may not itself be a constructor
    (e.g. `xs` is a constructor subterm of `x :: xs`) -/
def litComparesConstructorSubterms (lit : Lit) : MetaM (Option LitSide) := do
  let litTyIsInductive ← matchConstInduct lit.ty.getAppFn' (fun _ => pure false) (fun _ _ => pure true)
  if litTyIsInductive then
    trace[duper.rule.datatypeAcyclicity] "lit.ty {lit.ty} is an inductive datatype"
    -- If `e1` is a constructor subterm of `e2`, then `e1.weight ≤ e2.weight`
    if lit.lhs.weight < lit.rhs.weight then
      let rhsConstructorSubterms ← collectConstructorSubterms lit.rhs
      if rhsConstructorSubterms.contains lit.lhs then return some lhs
      else return none
    else if lit.rhs.weight < lit.lhs.weight then
      let lhsConstructorSubterms ← collectConstructorSubterms lit.lhs
      if lhsConstructorSubterms.contains lit.rhs then return some rhs
      else return none
    else
      if lit.lhs == lit.rhs then return some lhs
      else return none
  else -- `lit.ty` is not an inductive datatype so `lit` cannot be comparing constructor subterms
    trace[duper.rule.datatypeAcyclicity] "lit.ty {lit.ty} is not an inductive datatype"
    return none

def mkDatatypeAcyclicityProof (removedLitNum : Nat) (litSide : LitSide) (premises : List Expr)
  (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mut proofCases : Array Expr := Array.mkEmpty parentLits.size
    for i in [:parentLits.size] do
      let lit := parentLits[i]!
      if i == removedLitNum then -- `lit` is the equality asserting an acyclic constructor
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let sizeOfInst ← mkAppOptM ``inferInstance #[← mkAppOptM ``SizeOf #[lit.ty], none]
          let litTyMVar ← mkFreshExprMVar lit.ty
          let abstrLam ← mkLambdaFVars #[litTyMVar] $ ← mkAppOptM ``sizeOf #[some lit.ty, some sizeOfInst, some litTyMVar]
          let sizeOfEq ← mkAppM ``congrArg #[abstrLam, h] -- Has the type `sizeOf lit.lhs = sizeOf lit.rhs`
          let sizeOfEq ←
            match litSide with
            | lhs => mkAppM ``Eq.symm #[sizeOfEq]
            | rhs => pure sizeOfEq
          let lit : Lit :=
            match litSide with
            | lhs => lit.symm
            | rhs => lit
          let sizeOfEqFalseMVar ← mkFreshExprMVar $ ← mkAppM ``Not #[← inferType sizeOfEq] -- Has the type `¬(sizeOf lit.lhs = sizeOf lit.rhs)`
          let sizeOfEqFalseMVarId := sizeOfEqFalseMVar.mvarId!
          let gtProof ← buildGtProof lit.lhs lit.rhs
          let neProof ← mkAppM ``Nat.ne_of_gt #[gtProof]
          sizeOfEqFalseMVarId.assign neProof
          let proofCase := mkApp2 (mkConst ``False.elim [Level.zero]) body $ mkApp sizeOfEqFalseMVar sizeOfEq -- Has the type `body`
          trace[duper.rule.datatypeAcyclicity] "lit: {lit}, lit.ty: {lit.ty}, sizeOfInst: {sizeOfInst}, abstrLam: {abstrLam}, sizeOfEq: {sizeOfEq}"
          trace[duper.rule.datatypeAcyclicity] "sizeOfEqFalseMVar: {sizeOfEqFalseMVar}, proofCase: {proofCase}"
          Meta.mkLambdaFVars #[h] proofCase
        proofCases := proofCases.push proofCase
      else -- `lit` is not the equality to be removed
        let proofCase ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
        proofCases := proofCases.push proofCase
    let proof ← orCases (parentLits.map Lit.toExpr) proofCases
    Meta.mkLambdaFVars xs $ mkApp proof appliedPremise

/-- Implements the acyclicity rules described in section 6.4 of https://arxiv.org/pdf/1611.02908 -/
def datatypeAcyclicity : MSimpRule := fun c => do
  let c ← loadClause c
  for i in [:c.lits.size] do
    let lit := c.lits[i]!
    match ← litComparesConstructorSubterms lit with
    | some side =>
      if lit.sign then -- `lit` is never true so `lit` can be removed from `c`
        let res := c.eraseIdx i
        let yC ← yieldClause res "datatypeAcyclicity" $ mkDatatypeAcyclicityProof i side
        trace[duper.rule.datatypeAcyclicity] "datatypeAcyclicity applied to {c.lits} to yield {yC.1}"
        return some #[yC]
      else -- `lit` is a tautology so the clause `c` can simply be removed
        trace[duper.rule.datatypeAcyclicity] "datatypeAcyclicity applied to remove {c.lits}"
        return some #[]
    | none => continue
  return none
