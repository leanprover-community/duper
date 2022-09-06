import Duper.ProverM
import Duper.Util.Iterate
import Duper.RuleM
import Duper.MClause
import Duper.Simp
import Duper.Rules.Clausification
import Duper.Rules.ClausifyPropEq
import Duper.Rules.Demodulation
import Duper.Rules.ElimDupLit
import Duper.Rules.ElimResolvedLit
import Duper.Rules.EqualityFactoring
import Duper.Rules.EqualityResolution
import Duper.Rules.IdentBoolFalseElim
import Duper.Rules.IdentPropFalseElim
import Duper.Rules.NaiveClauseSubsumption
import Duper.Rules.Superposition
import Duper.Rules.SyntacticTautologyDeletion1
import Duper.Rules.SyntacticTautologyDeletion2
import Duper.Rules.SyntacticTautologyDeletion3
import Duper.Rules.DestructiveEqualityResolution
import Std.Data.BinomialHeap

namespace Duper

namespace ProverM
open Lean
open Meta
open Lean.Core
open Result
open Std
open ProverM
open RuleM

initialize
  registerTraceClass `Simp
  registerTraceClass `Simp.debug
  registerTraceClass `Timeout.debug

set_option trace.Prover.debug true

set_option maxHeartbeats 10000

open SimpResult

def forwardSimpRules : ProverM (Array SimpRule) := do
  return #[
    -- clausificationStep.toSimpRule "clausification",
    -- syntacticTautologyDeletion1.toSimpRule "syntactic tautology deletion 1",
    -- syntacticTautologyDeletion2.toSimpRule "syntactic tautology deletion 2",
    -- syntacticTautologyDeletion3.toSimpRule "syntactic tautology deletion 3",
    -- elimDupLit.toSimpRule "eliminate duplicate literals",
    -- elimResolvedLit.toSimpRule "eliminate resolved literals",
    -- destructiveEqualityResolution.toSimpRule "destructive equality resolution",
    -- identPropFalseElim.toSimpRule "identity prop false elimination",
    -- identBoolFalseElim.toSimpRule "identity boolean false elimination",
    -- (naiveForwardClauseSubsumption (← getActiveSet)).toSimpRule "forward clause subsumption (naive)",
    -- (forwardDemodulation (← getDemodSidePremiseIdx)).toSimpRule "forward demodulation"
  ]

def backwardSimpRules : ProverM (Array BackwardSimpRule) := do
  return #[
    -- (naiveBackwardClauseSubsumption (← getActiveSet)).toBackwardSimpRule "backward clause subsumption (naive)",
    -- (backwardDemodulation (← getMainPremiseIdx)).toBackwardSimpRule "backward demodulation"
  ]

def applyForwardSimpRules (givenClause : Clause) : ProverM (SimpResult Clause) := do
  for simpRule in ← forwardSimpRules do
    match ← simpRule givenClause with
    | Removed => return Removed
    | Applied c => return Applied c
    | Unapplicable => continue
  return Unapplicable

partial def forwardSimpLoop (givenClause : Clause) : ProverM (Option Clause) := do
  Core.checkMaxHeartbeats "forwardSimpLoop"
  match ← applyForwardSimpRules givenClause with
  | Applied c => forwardSimpLoop c
  | Unapplicable => return some givenClause 
  | Removed => return none

/-- Uses other clauses in the active set to attempt to simplify the given clause. Returns some simplifiedGivenClause if
    forwardSimpLoop is able to use simplification rules to transform givenClause to simplifiedGivenClause. Returns none if
    forwardSimpLoop is able to use simplification rules to show that givenClause is unneeded. -/
def forwardSimplify (givenClause : Clause) : ProverM (Option Clause) := do
  let c := forwardSimpLoop givenClause
  c

/-- Attempts to use givenClause to apply backwards simplification rules (starting from the startIdx's backward simplification rule) on clauses
    in the active set. If any backward simplification rule succeeds, then applyBackwardSimpRules returns the index of that simplification rule.
    Otherwise, applyBackwardSimpRules returns none. -/
def applyBackwardSimpRules (givenClause : Clause) (startIdx : Nat) : ProverM (Option Nat) := do
  let backwardSimpRules ← backwardSimpRules
  for i in [startIdx : backwardSimpRules.size] do
    let simpRule := backwardSimpRules[i]!
    if ← simpRule givenClause then return some i
    else continue
  return none

partial def backwardSimpLoop (givenClause : Clause) (startIdx : Nat) : ProverM Unit := do
  Core.checkMaxHeartbeats "backwardSimpLoop"
  match ← applyBackwardSimpRules givenClause startIdx with
  | some i => backwardSimpLoop givenClause i
  | none => return ()

/-- Uses the givenClause to attempt to simplify other clauses in the active set. For each clause that backwardSimplify is
    able to produce a simplification for, backwardSimplify removes the clause adds any newly simplified clauses to the passive set.
    Additionally, for each clause removed from the active set in this way, all descendents of said clause should also be removed from
    the current state's allClauses and passiveSet -/
def backwardSimplify (givenClause : Clause) : ProverM Unit := backwardSimpLoop givenClause 0

def performInferences (givenClause : Clause) : ProverM Unit := do
  -- performEqualityResolution givenClause
  -- performClausifyPropEq givenClause
  performSuperposition givenClause
  -- performEqualityFactoring givenClause

def replace (e : Expr) (target : Expr) (replacement : Expr) : ProverM Expr := do
  Core.transform e (pre := fun s => do
    if (← instantiateMVars s) == (← instantiateMVars target) then
      return TransformStep.done replacement
    else return TransformStep.visit s)

partial def saturate : ProverM Unit := do
  Core.withCurrHeartbeats do
    let mut myclause? : Option Clause := none
    try do repeat
      Core.checkMaxHeartbeats "saturate"
      let some givenClause ← chooseGivenClause
        | do
          setResult saturated
          return ()
      trace[Prover.saturate] "Given clause: {givenClause}"

      if givenClause.lits[0]!.lhs == givenClause.lits[0]!.rhs ∧ ¬ givenClause.lits[0]!.sign then
        throw <| Exception.internal emptyClauseExceptionId

      if givenClause.lits[0]!.sign then
        myclause? := some givenClause
      else
      
        -- Superposition
        let myclause := myclause?.get!
        let res ← replace givenClause.lits[0]!.lhs myclause.lits[0]!.lhs myclause.lits[0]!.rhs
        if res != givenClause.lits[0]!.lhs then
          let newClause := Clause.mk #[] 
            #[Lit.mk givenClause.lits[0]!.sign givenClause.lits[0]!.lvl givenClause.lits[0]!.ty res givenClause.lits[0]!.rhs]
          addNewToPassive newClause default

      -- performInferences givenClause
      addToActive givenClause
    catch
    | Exception.internal emptyClauseExceptionId _  =>
      setResult ProverM.Result.contradiction
      return ()
    | e =>
      -- trace[Timeout.debug] "Active set at timeout: {(← getActiveSet).toArray}"
      --trace[Timeout.debug] "All clauses at timeout: {Array.map (fun x => x.1) (← getAllClauses).toArray}"
      throw e

end ProverM

end Duper
