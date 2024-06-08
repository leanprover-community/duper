import Duper.RuleM
import Duper.MClause
import Duper.Util.ProofReconstruction

namespace Duper
open RuleM
open Lean
open Meta

initialize Lean.registerTraceClass `duper.rule.argCong

def mkArgumentCongruenceProof (i : Nat) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let parentLits := parentsLits[0]!
    let appliedPremise := appliedPremises[0]!
    let mVarTys := transferExprs

    let mut caseProofs := Array.mkEmpty parentLits.size
    for j in [:parentLits.size] do
      let lit := parentLits[j]!
      if j == i then
        let newMVars ← (mVarTys.map some).mapM Meta.mkFreshExprMVar
        let newFVars ← newMVars.mapM Lean.instantiateMVars
        let cj := cLits[j]!
        let pj := lit
        let cjl := cj.lhs
        let pjl ← Meta.mkAppM' pj.lhs newMVars
        let able_to_match ← Meta.performMatch #[(cjl, pjl)] #[]
        if able_to_match then
          trace[duper.rule.argCong] m!"lhs of conclusion: {cjl}, lhs of parent: {pjl}"
          let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
            let mut pr := h
            for x in newFVars do
              pr ← Meta.mkAppM ``congrFun #[pr, x]
            trace[duper.rule.argCong] m!"pr: {pr}, type: {← Meta.inferType pr}"
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j pr
          caseProofs := caseProofs.push pr
        else
          throwError s!"mkArgumentCongruenceProof:: " ++
                     s!"Unable to unify lhs of conclusion: {cjl} with " ++
                     s!"lhs of parent: {pjl}"
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) j h
        caseProofs := caseProofs.push pr

    let r ← orCases (parentLits.map Lit.toExpr) caseProofs
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def argCongAtLit (given : Clause) (c : MClause) (i : Nat) : RuleM (Array ClauseStream) :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]!
    let mut streams := #[]
    if ← eligibilityNoUnificationCheck c (alreadyReduced := true) i (strict := true) then
      let ty ← inferType lit.lhs
      let (mVars, _, _) ← forallMetaTelescope ty
      trace[duper.rule.argCong] s!"Lhs: {lit.lhs}, Level: {lit.lvl}, Type of lhs: {ty}, Telescope: {mVars}"
      let lhs := lit.lhs; let rhs := lit.rhs;
      let mut newMVars := #[]
      let mut mVarTys := #[]
      let loaded ← getLoadedClauses
      for m in mVars do
        newMVars := newMVars.push m
        mVarTys := mVarTys.push (← instantiateMVars (← inferType m))
        let newlhs := mkAppN lhs newMVars
        let newrhs := mkAppN rhs newMVars
        let newty ← inferType newlhs
        let newsort ← inferType newty
        let newlit := { lit with lhs := newlhs,
                                 rhs := newrhs,
                                 ty  := ← inferType newlhs
                                 lvl := Expr.sortLevel! newsort}
        let c' := c.replaceLit! i newlit
        let ug ← unifierGenerator #[]
        let yC := do
          setLoadedClauses loaded
          yieldClause c' "argument congruence" (mkProof := mkArgumentCongruenceProof i) (transferExprs := mVarTys)
        streams := streams.push (ClauseStream.mk ug given yC "argument congruence")
    return streams

def argCong (given : Clause) (c : MClause) (cNum : Nat) : RuleM (Array ClauseStream) := do
  trace[duper.rule.argCong] "ArgCong inferences with {c.lits}"
  let mut streams := #[]
  for i in [:c.lits.size] do
    if c.lits[i]!.sign = true then
      let str ← argCongAtLit given c i
      streams := streams.append str
  return streams

end Duper
