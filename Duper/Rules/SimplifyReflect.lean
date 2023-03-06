import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction

namespace Duper

open Lean
open Lean.Meta
open RuleM
open SimpResult
open Comparison
initialize Lean.registerTraceClass `Rule.simplifyReflect

def mkPositiveSimplifyReflectProof (mainPremisePos : ClausePos) (isForward : Bool) (premises : List Expr) (parents : List ProofParent)
  (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs

    let mainParentLits := if isForward then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if isForward then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if isForward then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if isForward then appliedPremises[0]! else appliedPremises[1]!

    let eqLit := sideParentLits[0]! 

    let proof ← Meta.withLocalDeclD `heq eqLit.toExpr fun heq => do
      let mut caseProofs : Array Expr := Array.mkEmpty mainParentLits.size
      for i in [:mainParentLits.size] do
        let lit := mainParentLits[i]!
        let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if(i == mainPremisePos.lit) then
            let motiveTy ← inferType (lit.lhs.getAtPos! mainPremisePos.pos)
            if mainPremisePos.side == LitSide.lhs then -- the lhs of the side clause can be matched onto mainPremisePos.pos of lit.lhs
              let motive :=
                mkLambda .anonymous BinderInfo.default motiveTy $
                  mkAppN (mkConst ``Ne [lit.lvl]) #[lit.ty, ← lit.lhs.replaceAtPos! mainPremisePos.pos (Expr.bvar 0), lit.rhs]
              let hAfterRw ← Meta.mkAppOptM ``Eq.ndrec #[none, none, motive, h, none, appliedSidePremise]
              Meta.mkLambdaFVars #[h] $ mkApp2 (mkConst ``False.elim [levelZero]) body $ ← Meta.mkAppM' hAfterRw #[← Meta.mkAppM ``Eq.refl #[lit.rhs]]
            else -- the lhs of the side clause can be matched onto mainPremisePos.pos of lit.rhs
              let motive :=
                mkLambda .anonymous BinderInfo.default motiveTy $
                  mkAppN (mkConst ``Ne [lit.lvl]) #[lit.ty, lit.lhs, ← lit.rhs.replaceAtPos! mainPremisePos.pos (Expr.bvar 0)]
              let hAfterRw ← Meta.mkAppOptM ``Eq.ndrec #[none, none, motive, h, none, appliedSidePremise]
              Meta.mkLambdaFVars #[h] $ mkApp2 (mkConst ``False.elim [levelZero]) body $ ← Meta.mkAppM' hAfterRw #[← Meta.mkAppM ``Eq.refl #[lit.lhs]]
          else if (i < mainPremisePos.lit) then
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
          else -- i > mainPremisePos.lit, so we have to adjust for the off-by-one error by giving orIntro `i - 1` rather than `i`
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) (i - 1) h
        caseProofs := caseProofs.push pr
      let r ← orCases (mainParentLits.map Lit.toExpr) caseProofs
      Meta.mkLambdaFVars #[heq] $ mkApp r appliedMainPremise
    let proof ← Meta.mkLambdaFVars xs $ mkApp proof appliedSidePremise
    return proof

def mkNegativeSimplifyReflectProof (mainPremiseLitIdx : Nat) (mainPremiseLhs : LitSide) (isForward : Bool) (premises : List Expr)
  (parents : List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs

    let mainParentLits := if isForward then parentsLits[1]! else parentsLits[0]!
    let sideParentLits := if isForward then parentsLits[0]! else parentsLits[1]!
    let appliedMainPremise := if isForward then appliedPremises[1]! else appliedPremises[0]!
    let appliedSidePremise := if isForward then appliedPremises[0]! else appliedPremises[1]!

    let neLit := sideParentLits[0]!

    let proof ← Meta.withLocalDeclD `hne neLit.toExpr fun hne => do
      let mut caseProofs : Array Expr := Array.mkEmpty mainParentLits.size
      for i in [:mainParentLits.size] do
        let lit := mainParentLits[i]!
        let pr : Expr ← Meta.withLocalDeclD `h lit.toExpr fun h => do
          if(i == mainPremiseLitIdx) then
            if mainPremiseLhs == LitSide.lhs then
              Meta.mkLambdaFVars #[h] $ mkApp2 (mkConst ``False.elim [levelZero]) body $ mkApp appliedSidePremise h
            else
              Meta.mkLambdaFVars #[h] $ mkApp2 (mkConst ``False.elim [levelZero]) body $ mkApp (← Meta.mkAppM ``Ne.symm #[appliedSidePremise]) h
          else if (i < mainPremiseLitIdx) then
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) i h
          else -- i > mainPremisePos.lit, so we have to adjust for the off-by-one error by giving orIntro `i - 1` rather than `i`
            Meta.mkLambdaFVars #[h] $ ← orIntro (cLits.map Lit.toExpr) (i - 1) h
        caseProofs := caseProofs.push $ pr
      let r ← orCases (mainParentLits.map Lit.toExpr) caseProofs
      Meta.mkLambdaFVars #[hne] $ mkApp r appliedMainPremise
    let proof ← Meta.mkLambdaFVars xs $ mkApp proof appliedSidePremise
    return proof

/-- Checks that (getAtPos mainPremiseLit.lhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseLhs and that
    (getAtPos mainPremiseLit.rhs mainPremisePos.pos) can be matched with sidePremise[0].sidePremiseRhs. Importantly, this function
    does NOT check mainPremise[pos.lit].sign or that mainPremise[pos.lit].lhs and mainPremise[pos.lit].rhs agree outside of the given pos. -/
def forwardPositiveSimplifyReflectWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId)
  (mainPremisePos : ClausePos) (sidePremise : Clause) : RuleM (Option (Array (Clause × Proof))) := do
  withoutModifyingLoadedClauses do
    let sidePremise ← loadClause sidePremise
    let sidePremiseLit := sidePremise.lits[0]!
    let mainPremiseLit := mainPremise.lits[mainPremisePos.lit]!.makeLhs mainPremisePos.side
    let matchSuccess ← -- Try to match lhs of sidePremise to mainPremisePos.side of mainPremise and rhs of sidePremise to other side of main premise
      RuleM.performMatch #[(mainPremiseLit.lhs.getAtPos! mainPremisePos.pos, sidePremiseLit.lhs),
                          (mainPremiseLit.rhs.getAtPos! mainPremisePos.pos, sidePremiseLit.rhs)] mainPremiseMVarIds
    if matchSuccess then
      let mut mainPremiseLitsExceptSimplifiedLit : List Lit := []
      for i in [:mainPremise.lits.size] do
        if i = mainPremisePos.lit then continue
        else mainPremiseLitsExceptSimplifiedLit := mainPremise.lits[i]! :: mainPremiseLitsExceptSimplifiedLit
      let res := MClause.mk mainPremiseLitsExceptSimplifiedLit.toArray.reverse
      trace[Rule.simplifyReflect] "(forward positive): Main clause: {mainPremise.lits}, side clause: {sidePremise.lits}, res: {res.lits}"
      let cp ← yieldClause res
        "forward positive simplify reflect"
        (some $ mkPositiveSimplifyReflectProof mainPremisePos true)
      return some #[cp]
    else return none

def forwardPositiveSimplifyReflectAtExpr (mainPremise : MClause) (pos : ClausePos)
  (potentialSideClauses : Array Clause) (mainMVarIds : Array MVarId) :
  RuleM (Option (Array (Clause × Proof))) := do
  for sideClause in potentialSideClauses do
    match ← forwardPositiveSimplifyReflectWithPartner mainPremise mainMVarIds pos sideClause with
    | none => continue
    | some cp => return cp
  return none

/-- Performs positive simplifyReflect with the given clause c as the main clause -/
def forwardPositiveSimplifyReflect (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  let fold_fn := fun acc _ pos => do
    match acc with
    | none =>
      if c.lits[pos.lit]!.sign then return none -- Can only perform positive simplify reflect at negative literals
      -- To find potential side clauses for the current literal, we search for clauses that subsume curLitButPositive
      let curLitButPositive := {c.lits[pos.lit]! with sign := true}
      -- Temporarily use `Clause`, don't need to suppply universe parameters
      let potentialSideClauses ← subsumptionTrie.getPotentialSubsumingClauses ⟨#[], #[], #[curLitButPositive]⟩
      /-
        The lit c[pos.lit] can be expressed as u[p ← σ(s)] ≠ u[p ← σ(t)] if and only if the following holds:
        1. c[pos.lit].sign is false
        2. c[pos.lit].lhs and c[pos.lit].rhs are identical everywhere except at p
        3. s (the lhs of the side clause) can be matched onto position p of c[pos.lit].lhs
        4. t (the rhs of the side clause) can be matched onto position p of c[pos.lit].rhs
        Conditions 1 and 2 are checked here, conditions 3 and 4 are checked in forwardPositiveSimplifyReflectAtExpr.
      -/
      let sidesAgree := Expr.expressionsAgreeExceptAtPos c.lits[pos.lit]!.lhs c.lits[pos.lit]!.rhs pos.pos
      if sidesAgree then forwardPositiveSimplifyReflectAtExpr c pos potentialSideClauses cMVarIds
      else return none
    | some cp => return some cp
  -- TODO: Determine if foldGreenM is an appropriate function here or if I need one that considers all subexpressions,
  -- rather than just green ones
  c.foldGreenM fold_fn none

def forwardNegativeSimplifyReflectWithPartner (mainPremise : MClause) (mainPremiseMVarIds : Array MVarId)
  (sidePremise : Clause) (mainPremiseLitIdx : Nat) (mainPremiseLhs : LitSide) : RuleM (Option (Array (Clause × Proof))) := do
  withoutModifyingLoadedClauses do
    let sidePremise ← loadClause sidePremise
    let sidePremiseLit := sidePremise.lits[0]!
    let mainPremiseLit := mainPremise.lits[mainPremiseLitIdx]!.makeLhs mainPremiseLhs
    let matchSuccess ← -- Try to match lhs of sidePremise to mainPremiseLhs of mainPremise and rhs of sidePremise to other side of main premise
      RuleM.performMatch #[(mainPremiseLit.lhs, sidePremiseLit.lhs), (mainPremiseLit.rhs, sidePremiseLit.rhs)] mainPremiseMVarIds
    if matchSuccess then
      let mut mainPremiseLitsExceptSimplifiedLit := mainPremise.lits.extract 0 (mainPremiseLitIdx - 1) ++ mainPremise.lits.extract mainPremiseLitIdx mainPremise.lits.size
      let res := MClause.mk mainPremiseLitsExceptSimplifiedLit
      trace[Rule.simplifyReflect] "(forward negative): Main clause: {mainPremise.lits}, side clause: {sidePremise.lits}, res: {res.lits}"
      let cp ← yieldClause res
        "forward negative simplify reflect"
        (some $ mkNegativeSimplifyReflectProof mainPremiseLitIdx mainPremiseLhs true)
      return some #[cp]
    else return none

def forwardNegativeSimplifyReflectAtLit (subsumptionTrie : SubsumptionTrie) (mainPremise : MClause)
  (mainPremiseMVarIds : Array MVarId) (mainPremiseLit : Nat) : RuleM (Option (Array (Clause × Proof))) := do
  let curLitButNegative := {mainPremise.lits[mainPremiseLit]! with sign := false}
  -- Temporarily use `Clause`, don't need to suppply universe parameters
  let potentialSideClauses ← subsumptionTrie.getPotentialSubsumingClauses ⟨#[], #[], #[curLitButNegative]⟩
  for sidePremise in potentialSideClauses do
    match ← forwardNegativeSimplifyReflectWithPartner mainPremise mainPremiseMVarIds sidePremise mainPremiseLit LitSide.lhs with
    | none =>
      match ← forwardNegativeSimplifyReflectWithPartner mainPremise mainPremiseMVarIds sidePremise mainPremiseLit LitSide.rhs with
      | none => continue
      | some cp => return cp
    | some cp => return cp
  return none

/-- Performs negative simplifyReflect with the given clause c as the main clause -/
def forwardNegativeSimplifyReflect (subsumptionTrie : SubsumptionTrie) : MSimpRule := fun c => do
  let (cMVars, c) ← loadClauseCore c
  let cMVarIds := cMVars.map Expr.mvarId!
  for curLitIdx in [0:c.lits.size] do
    if ¬ c.lits[curLitIdx]!.sign then
      continue
    match ← forwardNegativeSimplifyReflectAtLit subsumptionTrie c cMVarIds curLitIdx with
    | none => continue
    | some cp => return cp
  return none

/-- Performs positive simplifyReflect with the given clause as the side clause -/
def backwardPositiveSimplifyReflect (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSideClause => do
  -- Return Unapplicable if givenSideClause is anything other than a clause with exactly one positive literal
  if (givenSideClause.lits.size != 1 || !givenSideClause.lits[0]!.sign) then return #[]
  -- To find potential main clauses for the given side clause, we search for clauses that would be subsumed by sideClauseButNegative
  -- Temporarily use `Clause`, don't need to suppply universe parameters
  let sideClauseButNegative := ⟨#[], #[], #[{givenSideClause.lits[0]! with sign := false}]⟩
  let potentialMainClauses ← subsumptionTrie.getPotentialSubsumedClauses sideClauseButNegative
  let givenSideClause ← loadClause givenSideClause
  let mut results := #[]
  for mainClause in potentialMainClauses do
    let backwardPositiveSimplifyReflect ←
      withoutModifyingLoadedClauses do
        let (mclauseMVarIds, mainClause) ← loadClauseCore mainClause
        let mclauseMVarIds := mclauseMVarIds.map Expr.mvarId!
        let fold_fn := fun acc _ pos => do
          -- If we've already successfully performed positive simplify reflect on this main clause, then we don't need to do more
          if let some _ := acc then return acc
          /-
            The lit mainClause[pos.lit] can be expressed as u[p ← σ(s)] ≠ u[p ← σ(t)] if and only if the following holds:
            1. mainClause[pos.lit].sign is false
            2. mainClause[pos.lit].lhs and mainClause[pos.lit].rhs are identical everywhere except at p
            3. s (the lhs of the side clause) can be matched onto position p of mainClauseLit.lhs
            4. t (the rhs of the side clause) can be matched onto position p of mainClauseLit.rhs
          -/
          let sidesAgree := Expr.expressionsAgreeExceptAtPos mainClause.lits[pos.lit]!.lhs mainClause.lits[pos.lit]!.rhs pos.pos
          if(!mainClause.lits[pos.lit]!.sign && sidesAgree) then
            let sideClauseLit := givenSideClause.lits[0]!
            let mainClauseLit := mainClause.lits[pos.lit]!.makeLhs pos.side
            let matchSuccess ← -- Try to match lhs of sidePremise to pos.side of mclause and rhs of sidePremise to other side of mclause
              RuleM.performMatch #[(mainClauseLit.lhs.getAtPos! pos.pos, sideClauseLit.lhs),
                                  (mainClauseLit.rhs.getAtPos! pos.pos, sideClauseLit.rhs)] mclauseMVarIds
            if matchSuccess then
              let mainClauseLitsExceptSimplifiedLit := mainClause.lits.extract 0 (pos.lit - 1) ++ mainClause.lits.extract pos.lit mainClause.lits.size
              let res := MClause.mk mainClauseLitsExceptSimplifiedLit
              trace[Rule.simplifyReflect] "Backward positive simplify reflect with givenSideClause: {givenSideClause.lits} and main clause: {mainClause.lits}"
              trace[Rule.simplifyReflect] "Result: {res.lits}"
              let cp ← yieldClause res "backward positive simplify reflect" $ some $ mkPositiveSimplifyReflectProof pos false
              return some cp
            else return none
          else return none
        mainClause.foldGreenM fold_fn none
    if let some cp := backwardPositiveSimplifyReflect then
      results := results.push (mainClause, some cp)
  return results

/-- Performs negative simplifyReflect with the given clause as the side clause -/
def backwardNegativeSimplifyReflect (subsumptionTrie : SubsumptionTrie) : BackwardMSimpRule := fun givenSideClause => do
  -- Return Unapplicable if givenSideClause is anything other than a clause with exactly one negative literal
  if (givenSideClause.lits.size != 1 || givenSideClause.lits[0]!.sign) then return #[]
  -- To find potential main clauses for the given side clause, we search for clauses that would be subsumed by sideClauseButPositive
  -- Temporarily use `Clause`, don't need to suppply universe parameters
  let sideClauseButPositive := ⟨#[], #[], #[{givenSideClause.lits[0]! with sign := true}]⟩
  let potentialMainClauses ← subsumptionTrie.getPotentialSubsumedClauses sideClauseButPositive
  let givenSideClause ← loadClause givenSideClause
  let mut results := #[]
  for mainClause in potentialMainClauses do
    let backwardNegativeSimplifyReflect ←
      withoutModifyingLoadedClauses do
        let (mclauseMVarIds, mainClause) ← loadClauseCore mainClause
        let mclauseMVarIds := mclauseMVarIds.map Expr.mvarId!
        let sideClauseLit := givenSideClause.lits[0]!
        for mainClauseLitIdx in [0:mainClause.lits.size] do
          if !mainClause.lits[mainClauseLitIdx]!.sign then continue -- mainClauseLit must be positive
          for mainClauseLhs in [LitSide.lhs, LitSide.rhs] do
            let mainClauseLit := mainClause.lits[mainClauseLitIdx]!.makeLhs mainClauseLhs
            let matchSuccess ← -- Try to match sideClause.lhs to mainClauseLit.lhs and sideClause.rhs to mainClauseLit.rhs
              RuleM.performMatch #[(mainClauseLit.lhs, sideClauseLit.lhs), (mainClauseLit.rhs, sideClauseLit.rhs)] mclauseMVarIds
            if matchSuccess then
              let mut mainClauseLitsExceptSimplifiedLit : List Lit := []
              for i in [:mainClause.lits.size] do
                if i = mainClauseLitIdx then continue
                else mainClauseLitsExceptSimplifiedLit := mainClause.lits[i]! :: mainClauseLitsExceptSimplifiedLit
              let res := MClause.mk mainClauseLitsExceptSimplifiedLit.toArray.reverse
              trace[Rule.simplifyReflect] "Backward negative simplify reflect with givenSideClause: {givenSideClause.lits} and main clause: {mainClause.lits}"
              trace[Rule.simplifyReflect] "Result: {res.lits}"
              let cp ← yieldClause res "backward negative simplify reflect" (some $ mkNegativeSimplifyReflectProof mainClauseLitIdx mainClauseLhs false)
              return some cp
            else continue
        return none
    if let some cp := backwardNegativeSimplifyReflect then
      results := results.push (mainClause, some cp)
  return results