import Lean
import Duper.Saturate
import Duper.Unif

open Lean
open Lean.Meta
open Duper
open ProverM


namespace Lean.Elab.Tactic

partial def printProof (state : ProverM.State) : TacticM Unit := do
  Core.checkMaxHeartbeats "printProof"
  let rec go c (hm : Array (Nat × Clause) := {}) : TacticM Unit := do
    let info ← getClauseInfo! c
    if hm.contains (info.number, c) then throwError "Loop! {hm} {info.number}"
    let hm := hm.push (info.number, c)
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! pp.clause) 
    let parentIds := parentInfo.map fun info => info.number
    trace[Prover.debug] "Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {c}"
    for proofParent in info.proof.parents do
      go proofParent.clause hm
  go Clause.empty
where 
  getClauseInfo! (c : Clause) : TacticM ClauseInfo := do
    let some ci := state.allClauses.find? c
      | throwError "clause info not found: {c}"
    return ci

def getClauseInfo! (state : ProverM.State) (c : Clause) : TacticM ClauseInfo := do
  let some ci := state.allClauses.find? c
    | throwError "clause info not found: {c}"
  return ci

partial def collectClauses (state : ProverM.State) (c : Clause) (acc : ClauseHeap) : TacticM ClauseHeap := do
  Core.checkMaxHeartbeats "collectClauses"
  let info ← getClauseInfo! state c
  let mut acc := acc
  -- recursive calls
  acc := acc.insert (info.number, c)
  for proofParent in info.proof.parents do
    acc ← collectClauses state proofParent.clause acc
  return acc

partial def mkProof (state : ProverM.State) : List Clause → TacticM Expr
| [] => panic! "empty clause list"
| c :: cs => do
  Core.checkMaxHeartbeats "mkProof"
  let info ← getClauseInfo! state c
  let newTarget := c.toForallExpr
  let mut parents := #[]
  for parent in info.proof.parents do
    let number := (← getClauseInfo! state parent.clause).number
    parents := parents.push ((← getLCtx).findFromUserName? (Name.mkNum `clause number)).get!.toExpr
  let mut lctx ← getLCtx
  let mut skdefs : List Expr := []
  for (fvarId, mkSkProof) in info.proof.introducedSkolems do
    trace[Meta.debug] "Reconstructing skolems {mkFVar fvarId}"
    let ty := (state.lctx.get! fvarId).type
    trace[Meta.debug] "Reconstructing skolems {toString ty}"
    let userName := (state.lctx.get! fvarId).userName
    let skdef ← mkSkProof parents
    skdefs := skdef :: skdefs
    lctx := lctx.mkLetDecl fvarId userName ty skdef
  let proof ← withLCtx lctx (← getLocalInstances) do
    trace[Meta.debug] "Reconstructing proof for #{info.number}: {c}"
    let newProof ← info.proof.mkProof parents info.proof.parents c
    if cs == [] then return newProof
    let proof ←
      withLetDecl (Name.mkNum `clause info.number) newTarget newProof fun g => do
        let remainingProof ← mkProof state cs
        let mut remainingProof ← mkLambdaFVars (usedLetOnly := false) #[g] remainingProof
        for (fvarId, _) in info.proof.introducedSkolems do
          remainingProof ← mkLambdaFVars (usedLetOnly := false) #[mkFVar fvarId] remainingProof
        return remainingProof
    return proof
  return proof

def applyProof (state : ProverM.State) : TacticM Unit := do
  let l := (← collectClauses state Clause.empty Std.BinomialHeap.empty).toList.map Prod.snd
  trace[Meta.debug] "{l}"
  let proof ← mkProof state l
  assignExprMVar (← getMainGoal) proof -- TODO: List.last?

def collectAssumptions : TacticM (Array (Expr × Expr)) := do
  let mut formulas := #[]
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← getLocalDecl fVarId
    unless ldecl.binderInfo.isAuxDecl ∨ not (← inferType ldecl.type).isProp do
      formulas := formulas.push (← instantiateMVars ldecl.type, ← mkAppM ``eq_true #[mkFVar fVarId])
  return formulas

syntax (name := duper) "duper" : tactic

@[tactic duper]
def evalDuper : Tactic
| `(tactic| duper) => withMainContext do
  let startTime ← IO.monoMsNow
  replaceMainGoal [(← intros (← getMainGoal)).2]
  let mvar ← withMainContext do mkFreshExprMVar (← mkArrow (← mkAppM ``Not #[← getMainTarget]) (mkConst ``False))
  assignExprMVar (← getMainGoal) (mkApp2 (mkConst ``Classical.byContradiction) (← getMainTarget) mvar)
  replaceMainGoal [mvar.mvarId!]
  replaceMainGoal [(← intro (← getMainGoal) `h).2]
  withMainContext do
    let formulas ← collectAssumptions
    trace[Meta.debug] "{formulas}"
    let (_, state) ← ProverM.runWithExprs (s := {lctx := ← getLCtx}) ProverM.saturate formulas
    match state.result with
    | Result.contradiction => do
        logInfo s!"Contradiction found. Time: {(← IO.monoMsNow) - startTime}ms"
        printProof state
        applyProof state
        logInfo s!"Constructed proof. Time: {(← IO.monoMsNow) - startTime}ms"
    | Result.saturated => 
      trace[Prover.debug] "Final Active Set: {state.activeSet.toArray}"
      -- trace[Prover.debug] "supMainPremiseIdx: {state.supMainPremiseIdx}"
      throwError "Prover saturated."
    | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic

