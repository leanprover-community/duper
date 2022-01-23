import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

namespace Schroedinger
open RuleM
open Lean

-- move to proof reconstruction file
def orCases (lits : Array Expr) (target : Expr) (caseProofs : Array Expr) : MetaM Expr := do
  let mut ors := #[lits[lits.size - 1]]
  for l in [2:lits.size+1] do
    ors := ors.push (mkApp2 (mkConst ``Or) lits[lits.size - l] ors[ors.size-1])
  let mut r ← caseProofs[caseProofs.size - 1]
  for k in [2:caseProofs.size+1] do
    let newOne ← caseProofs[caseProofs.size - k]
    r ← Meta.withLocalDeclD `h ors[k-1] fun h => do
      let p := mkApp6
        (mkConst ``Or.elim)
        lits[lits.size - k]
        ors[k-2]
        target
        h
        newOne
        r
      Meta.mkLambdaFVars #[h] p
  return r

-- TODO: Pass in the clauses later?
def mkEqualityResolutionProof (c : Clause) (i : Nat) (premises : Array Expr) (parents: Array ProofParent) : MetaM Expr := do
  let premise := premises[0]
  let parent := parents[0]
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let vanishingVarSkolems ← parent.vanishingVarTypes.mapM (fun ty => Lean.Meta.mkSorry ty (synthetic := true))
    let parentInstantiations := parent.instantiations.map (fun ins => ins.instantiate (xs ++ vanishingVarSkolems))
    let parentLits := parent.clause.lits.map (fun lit => lit.map (fun e => e.instantiateRev parentInstantiations))

    let caseProofs ← parentLits.mapM fun lit => do Lean.Meta.mkSorry (← Meta.mkArrow lit.toExpr body) (synthetic := true)
    
    let r ← orCases (← parentLits.map Lit.toExpr) body caseProofs
    let appliedPremise := mkAppN premise parentInstantiations
    Meta.mkLambdaFVars xs $ mkApp r appliedPremise

def equalityResolutionAtLit (c : MClause) (i : Nat) : RuleM Unit :=
  withoutModifyingMCtx $ do
    let lit := c.lits[i]
    if ← unify #[(lit.lhs, lit.rhs)]
    then
      let c := c.eraseLit i
      yieldClause c "equality resolution" 
        (mkProof := mkEqualityResolutionProof (← neutralizeMClause c) i)

def equalityResolution (c : MClause) : RuleM Unit := do
  for i in [:c.lits.size] do
    if c.lits[i].sign = false then
      equalityResolutionAtLit c i

def superpositionAtLitWithPartner (mainPremise : MClause) (mainPremiseSubterm : Expr) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : RuleM Unit := do
  Core.checkMaxHeartbeats "superposition"
  withoutModifyingMCtx $ do
    if mainPremiseSubterm.isMVar then
      return ()
    if not $ ← unify #[(mainPremiseSubterm, sidePremiseLit.lhs)] then
      return ()
    let lhs ← instantiateMVars sidePremiseLit.lhs
    let rhs ← instantiateMVars sidePremiseLit.rhs
    if (← compare lhs rhs) == Comparison.LessThan then
      return ()
    let mainPremiseReplaced ← 
      mainPremise.mapM fun e => do
        replace (← instantiateMVars e) lhs rhs
    let restOfSidePremise ← restOfSidePremise.mapM fun e => instantiateMVars e
    yieldClause (MClause.append mainPremiseReplaced restOfSidePremise) "superposition"

def superpositionAtLit (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseLit : Lit) (restOfSidePremise : MClause) : 
    RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at literal {sidePremiseLit}"
  let potentialPartners ← mainPremiseIdx.getUnify sidePremiseLit.lhs
  -- trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      superpositionAtLitWithPartner c (c.getAtPos! partnerPos)
          sidePremiseLit restOfSidePremise

def superpositionAtExpr (e : Expr) (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos)
    (mainPremise : MClause) : RuleM Unit := do
  trace[Rule.debug] "Superposition inferences at expression {e}"
  let potentialPartners ← sidePremiseIdx.getUnify e
  -- trace[Rule.debug] "Potential partners {potentialPartners}"
  for (partnerClause, partnerPos) in potentialPartners do
    withoutModifyingLoadedClauses $ do
      trace[Rule.debug] "Superposition with partner clause {partnerClause}"
      let c ← loadClause partnerClause
      let lit := match partnerPos.side with
      | LitSide.lhs => c.lits[partnerPos.lit]
      | LitSide.rhs => c.lits[partnerPos.lit].symm
      superpositionAtLitWithPartner mainPremise e
          lit
          (c.eraseIdx partnerPos.lit)

def superposition 
    (mainPremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (sidePremiseIdx : ProverM.ClauseDiscrTree ClausePos) 
    (givenMClause : MClause) : RuleM Unit := do
  -- With given clause as side premise:
  -- trace[Rule.debug] "Superposition inferences with {givenClause} as side premise"
  for i in [:givenMClause.lits.size] do
    if givenMClause.lits[i].sign = true
    then 
      let restOfGivenClause ← givenMClause.eraseIdx i
      for lit in #[(givenMClause.lits[i]), (givenMClause.lits[i]).symm] do
        if (← RuleM.compare lit.lhs lit.rhs) == Comparison.LessThan then
          continue
        let cs ← superpositionAtLit mainPremiseIdx lit restOfGivenClause
  -- With given clause as main premise
  -- trace[Rule.debug] "Superposition inferences with {givenClause} as main premise"
  givenMClause.foldGreenM fun acc e pos => do
      superpositionAtExpr e sidePremiseIdx givenMClause
      ()
    ()
  -- TODO: What about inference with itself?
      
open ProverM

def performEqualityResolution (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "EqRes inferences with {givenClause}"
  performInference equalityResolution givenClause

def performSuperposition (givenClause : Clause) : ProverM Unit := do
  trace[Prover.debug] "Superposition inferences with {givenClause}"
  let mainPremiseIdx ← getSupMainPremiseIdx
  let sidePremiseIdx ← getSupSidePremiseIdx
  performInference (superposition mainPremiseIdx sidePremiseIdx) givenClause


end Schroedinger