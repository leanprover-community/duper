import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Util.Misc

namespace Duper
open RuleM
open Lean

initialize Lean.registerTraceClass `InstantiatePremises

-- `xs` is usually obtained by `Meta.forallTelescope c.toForallExpr fun xs body =>`
def instantiatePremises (parents : List ProofParent) (premises : List Expr) (xs : Array Expr) (transferExprs : Array Expr) : 
    MetaM (List (Array Lit) × List Expr × Array Expr) := do
  let mut parentsLits := []
  let mut appliedPremises := []
  for (parent, premise) in List.zip parents premises do
    let finstantiatedparent_pre ← parent.expr.instantiateForallNoReducing xs
    -- `fvars = xs ++ vanishedvars`
    -- `finstantiatedparent = ((.mdata) fun [vars] => parent[vars]) mvars[fvars]`
    let (mvars, bis, finstantiatedparent) ← Meta.forallMetaTelescope finstantiatedparent_pre
    for m in mvars do
      let ty ← Meta.inferType m
      let id := m.mvarId!
      id.assign (← Meta.findInstance ty)
    -- `parentInstantiations = mvars[fvars]`
    let parentInstantiations := finstantiatedparent.getAppArgs
    trace[InstantiatePremises] "parentInstantiations: {parentInstantiations}"
    let parentParamNames := parent.clause.paramNames
    let parentParamSubst := parent.paramSubst
    let parentLits := parent.clause.lits.map fun lit =>
      (lit.map (fun e => (e.instantiateRev parentInstantiations))).instantiateLevelParamsArray parentParamNames parentParamSubst
    parentsLits := parentLits :: parentsLits
    let newprem := (mkAppN premise parentInstantiations).instantiateLevelParams parentParamNames.data parentParamSubst.data
    appliedPremises := newprem :: appliedPremises
    -- Now, `appliedPremises[i] : parentsLits[i]`, for all `i`
  let transferExprs := transferExprs.map (fun e => mkAppN e xs)
  return (parentsLits, appliedPremises, transferExprs)

/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n] → target`, given proofs (`casesProofs`) of `lits[i] → target` -/
def orCases (lits : Array Expr) (caseProofs : Array Expr) : MetaM Expr := do
  let mut ors := #[lits[lits.size - 1]!]
  for l in [2:lits.size+1] do
    ors := ors.push (mkApp2 (mkConst ``Or) lits[lits.size - l]! ors[ors.size-1]!)
  let mut r := caseProofs[caseProofs.size - 1]!
  for k in [2:caseProofs.size+1] do
    let newOne := caseProofs[caseProofs.size - k]!
    r ← Meta.withLocalDeclD `h ors[k-1]! fun h => do
      let p ← Meta.mkAppM ``Or.elim #[h, newOne, r]
      Meta.mkLambdaFVars #[h] p
  return r

/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n]`, given a `proof` of `lits[i]` -/
def orIntro (lits : Array Expr) (i : Nat) (proof : Expr) : MetaM Expr := do
  let mut tyR := lits[lits.size-1]!
  for j in [2:lits.size-i] do
    tyR := mkApp2 (mkConst ``Or) lits[lits.size - j]! tyR
  let mut proofRight :=
    if i != lits.size - 1 then
      mkApp3 (mkConst ``Or.inl) lits[i]! tyR proof
    else
      proof
  if i != lits.size - 1 then
    tyR := mkApp2 (mkConst ``Or) lits[i]! tyR
  for j in [lits.size-i+1:lits.size+1] do
    proofRight := mkApp3 (mkConst ``Or.inr) lits[lits.size-j]! tyR proofRight
    tyR := mkApp2 (mkConst ``Or) lits[lits.size-j]! tyR
  return proofRight

/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n]`, given a `proof` of the subclause consisting of the last `i` literals -/
def orSubclause (lits : Array Expr) (i : Nat) (proof : Expr) : MetaM Expr := do
  let mut tyR := lits[lits.size - 1]!
  for j in [2:i+1] do
    tyR := mkApp2 (mkConst ``Or) lits[lits.size - j]! tyR
  let mut proofRight := proof -- proof is a proof of the last `i` literals, which is currently the subclause contained by tyR
  for j in [i+1:lits.size+1] do
    proofRight := mkApp3 (mkConst ``Or.inr) lits[lits.size-j]! tyR proofRight
    tyR := mkApp2 (mkConst ``Or) lits[lits.size-j]! tyR
  return proofRight

/-- Given a list `l` of propositions, constructs the proposition `l[0] ∧ ... ∧ l[n]` -/
def andBuild (l : List Expr) : MetaM Expr :=
  match l with
  | List.nil => throwError "Cannot build an empty conjunction"
  | l1 :: List.nil => return l1
  | l1 :: restL => return mkApp2 (mkConst ``And) l1 $ ← andBuild restL

/-- Given a proof of `l[0] ∧ ... ∧ l[n]`, constructs a proof of `l[i]` -/
def andGet (l : List Expr) (i : Nat) (proof : Expr) : MetaM Expr := do
  match l with
  | List.nil => throwError "andGet index {i} out of bound (l is {l})"
  | _ :: List.nil =>
    if i == 0 then return proof
    else throwError "andGet index {i} out of bound (l is {l})"
  | l1 :: restL => -- restL is not List.nil so it is safe to pass into andbuild
    if i == 0 then return mkApp3 (mkConst ``And.left) l1 (← andBuild restL) proof
    else andGet restL (i - 1) $ mkApp3 (mkConst ``And.right) l1 (← andBuild restL) proof

end Duper