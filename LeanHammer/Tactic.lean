import Lean
import LeanHammer.Saturate
import LeanHammer.Unif

open Lean
open Lean.Meta
open Schroedinger
open ProverM


namespace Lean.Elab.Tactic

syntax (name := prover) "prover" : tactic

partial def printProof (state : ProverM.State) : TacticM Unit := do
  let rec go c : TacticM Unit := do
    let info ← getClauseInfo! c
    let parentInfo ← info.proof.parents.mapM (fun pp => getClauseInfo! pp.clause) 
    let parentIds ← parentInfo.map fun info => info.number
    trace[Prover.debug] "Clause #{info.number} (by {info.proof.ruleName} {parentIds}): {c}"
    for proofParent in info.proof.parents do
      go proofParent.clause
  go Clause.empty
where 
  getClauseInfo! (c : Clause) : TacticM ClauseInfo := do
    let some ci ← state.allClauses.find? c
      | throwError "clause info not found: {c}"
    ci

def getClauseInfo! (state : ProverM.State) (c : Clause) : TacticM ClauseInfo := do
  let some ci ← state.allClauses.find? c
    | throwError "clause info not found: {c}"
  ci

partial def mkList (state : ProverM.State) (c : Clause) (acc : List Clause := []) : TacticM (List Clause) := do
  let info ← getClauseInfo! state c
  let mut acc := acc
  -- recursive calls
  acc := c :: acc
  for proofParent in info.proof.parents do
    acc ← mkList state proofParent.clause acc
  return acc

partial def mkGoals (state : ProverM.State) : List Clause → TacticM (List (MVarId × Expr))
| [] => []
| c :: cs => do
  let info ← getClauseInfo! state c
  let newTarget ← c.toForallExpr
  let mut lctx ← getLCtx
  let mut skGoals : List MVarId := []
  for (fvarId, _) in info.proof.introducedSkolems do
    let ty := (state.lctx.get! fvarId).type
    let userName := (state.lctx.get! fvarId).userName
    let mvar ← mkFreshExprSyntheticOpaqueMVar ty
    skGoals := mvar.mvarId! :: skGoals
    lctx := lctx.mkLetDecl fvarId userName ty mvar
  let (newGoal, otherGoals) ← withLCtx lctx (← getLocalInstances) do
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newTarget (tag := s!"Clause#{info.number}")
    let otherGoals ←
      withLetDecl (Name.mkNum `goal info.number) newTarget newGoal fun g => do
        let otherGoals ← mkGoals state cs
        let otherGoals ← otherGoals.mapM fun (otherGoal, otherProof) => do
          let mut otherProof ← mkLambdaFVars #[g] otherProof
          for (fvarId, _) in info.proof.introducedSkolems do
            otherProof ← mkLambdaFVars #[mkFVar fvarId] otherProof
          return (otherGoal, otherProof)
        otherGoals
    (newGoal, otherGoals)
  return skGoals.map (fun g => (g, mkMVar g)) ++ (newGoal.mvarId!, newGoal) :: otherGoals

partial def applyProof (state : ProverM.State) : TacticM (List MVarId) := do
  let l ← mkList state Clause.empty
  trace[Meta.debug] "{l}"
  let goals ← mkGoals state l
  trace[Meta.debug] "{goals.map (mkMVar $ Prod.fst ·)}"
  trace[Meta.debug] "{goals.map Prod.snd}"
  assignExprMVar (← getMainGoal) goals.reverse.head!.2 -- TODO: List.last?
  return goals.map (Prod.fst ·)

def collectAssumptions : TacticM (Array Expr) := do
  let mut formulas := #[]
  for fVarId in (← getLCtx).getFVarIds do
    let ldecl ← getLocalDecl fVarId
    unless ldecl.binderInfo.isAuxDecl ∨ not (← inferType ldecl.type).isProp do
      formulas := formulas.push ldecl.type
  return formulas

@[tactic prover]
partial def evalProver : Tactic
| `(tactic| prover) => withMainContext do
  let startTime ← IO.monoMsNow
  let formulas ← collectAssumptions
  trace[Meta.debug] "{formulas}"
  let (_, state) ← ProverM.runWithExprs (s := {lctx := ← getLCtx}) ProverM.saturate formulas
  match state.result with
  | Result.contradiction => do
      printProof state
      let goals ← applyProof state
      setGoals $ goals
      trace[Prover.debug] "Time: {(← IO.monoMsNow) - startTime}ms {(← getUnsolvedGoals).length}"
  | Result.saturated => 
    trace[Prover.debug] "Final Active Set: {state.activeSet.toArray}"
    -- trace[Prover.debug] "supMainPremiseIdx: {state.supMainPremiseIdx}"
    throwError "Prover saturated."
  | Result.unknown => throwError "Prover was terminated."
| _ => throwUnsupportedSyntax

end Lean.Elab.Tactic

