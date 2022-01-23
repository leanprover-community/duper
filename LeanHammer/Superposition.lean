import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause

namespace Schroedinger
open RuleM
open Lean

-- move to proof reconstruction file
/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n] → target`, given proofs (`casesProofs`) of `lits[i] → target` -/
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

-- move to proof reconstruction file
/-- Construct a proof of `lits[0] ∨ ... ∨ lits[n]`, given a `proof` of `lits[i]` -/
def orIntro (lits : Array Expr) (i : Nat) (proof : Expr) : MetaM Expr := do
  let mut tyR := lits[lits.size-1]
  for j in [2:lits.size-i] do
    tyR := mkApp2 (mkConst ``Or) lits[lits.size - j] tyR
  let mut proofRight := ←
    if i != lits.size - 1 then
      mkApp3 (mkConst ``Or.inl) lits[i] tyR proof
    else
      proof
  if i != lits.size - 1 then
    tyR := mkApp2 (mkConst ``Or) lits[i] tyR
  for j in [lits.size-i+1:lits.size+1] do
    proofRight := mkApp3 (mkConst ``Or.inr) lits[lits.size-j] tyR proofRight
    tyR := mkApp2 (mkConst ``Or) lits[lits.size-j] tyR
  return proofRight

-- TODO: Pass in the clauses later?
def mkEqualityResolutionProof (c : Clause) (i : Nat) (premises : Array Expr) (parents: Array ProofParent) : MetaM Expr := do
  let premise := premises[0]
  let parent := parents[0]
  Meta.forallTelescope c.toForallExpr fun xs body => do
    -- TODO: get rid of this sorry (need inhabited types!)
    let vanishingVarSkolems ← parent.vanishingVarTypes.mapM (fun ty => Lean.Meta.mkSorry ty (synthetic := true))
    let parentInstantiations := parent.instantiations.map (fun ins => ins.instantiateRev (xs ++ vanishingVarSkolems))
    let parentLits := parent.clause.lits.map (fun lit => lit.map (fun e => e.instantiateRev parentInstantiations))
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))

    let mut caseProofs := #[]
    for j in [:parentLits.size] do
      let lit := parentLits[j]
      if j == i then
        -- lit has the form t ≠ t
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let pr ← mkApp2 (mkConst ``rfl [lit.lvl]) lit.ty lit.lhs
          let pr ← mkApp h pr
          let pr ← mkApp2 (mkConst ``False.elim [levelZero]) body pr
          Meta.mkLambdaFVars #[h] pr
        caseProofs := caseProofs.push pr
      else
        -- need proof of `L_j → L_1 ∨ ... ∨ L_n`
        let pr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          let idx := if j ≥ i then j - 1 else j
          Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) idx h
        -- caseProofs := caseProofs.push $ ← Lean.Meta.mkSorry (← Meta.mkArrow lit.toExpr body) (synthetic := true)
        caseProofs := caseProofs.push $ pr

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