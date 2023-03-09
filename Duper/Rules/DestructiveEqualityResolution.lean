import Duper.Simp
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open SimpResult
open Lean
open Meta

def is_var (e : Expr) : Bool :=
  match Expr.consumeMData e with
  | Expr.mvar _ => true
  | Expr.fvar _ => true
  | Expr.bvar _ => true
  | _ => false

def mkDestructiveEqualtiyResolutionProof (i : Nat) (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        -- lit has the form t ≠ t
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let pr := mkApp2 (mkConst ``rfl [lit.lvl]) lit.ty lit.lhs
          let pr := mkApp h pr
          let pr := mkApp2 (mkConst ``False.elim [levelZero]) body pr
          Meta.mkLambdaFVars #[h] pr
        caseProofs := caseProofs.push pr
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        caseProofs := caseProofs.push $ pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def destructiveEqualityResolutionAtLit (c : MClause) (i : Nat) : RuleM (Option (Clause × Proof)) :=
  withoutModifyingMCtx do
    let lit := c.lits[i]!
    if ← fastUnify #[(lit.lhs, lit.rhs)] then
      some <$> yieldClause (c.eraseLit i) "destructive equality resolution"
        (some (mkDestructiveEqualtiyResolutionProof i))
    else
      return none -- Cannot apply destructive equality resolution to this literal,
                   -- but it may still be possible to apply it to a different literal in the clause

def destructiveEqualityResolution : MSimpRule := fun c => do
  let c ← loadClause c
  for i in [:c.lits.size] do
    if c.lits[i]!.sign = false ∧ (is_var c.lits[i]!.lhs ∨ is_var c.lits[i]!.rhs) then
      match ← destructiveEqualityResolutionAtLit c i with
      | some cp => return some #[cp]
      | none => continue
  return none