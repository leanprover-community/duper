import Lean
import Duper.Util.Misc
import Duper.ProverM
import Duper.Util.ProofReconstruction
import Duper.Simp
import Duper.Rules.Nonempty

namespace Duper

namespace ProverM
open Lean
open Meta
open Lean.Core
open Result
open Std
open ProverM
open RuleM

inductive VarRemovalRes
| Success (res : Clause × Proof) : VarRemovalRes
| PotentiallyVacuous : VarRemovalRes
| NoVanishedVars : VarRemovalRes

open VarRemovalRes

def mkRemoveVanishedVarsProof (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let (_, appliedPremises, _) ← instantiatePremises parents premises xs transferExprs
    let appliedPremise := appliedPremises[0]!
    Meta.mkLambdaFVars xs appliedPremise

/-- Attempts to remove the vanished variables that appear in c, updating verifiedInhabitedTypes and potentiallyUninhabitedTypes as it
    encounters types whose inhabitation status has not previously been checked. -/
def removeVanishedVarsHelper (c : Clause) (verifiedInhabitedTypes : abstractedMVarList) (potentiallyUninhabitedTypes : abstractedMVarList)
  : RuleM (VarRemovalRes × abstractedMVarList × abstractedMVarList) := do
  let (mvars, mclause) ← loadClauseCore c
  let mut verifiedInhabitedTypes := verifiedInhabitedTypes
  let (_, s) := AbstractMVars.abstractExprMVars mclause.toExpr { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  let mut mvarIdsToRemove := #[]
  for mvar in mvars do
    let mvarId := mvar.mvarId!
    if s.emap.contains mvarId then
      continue -- mvar appears in mclause, so it is not vanished and we do not have to check for inhabitation
    else
      let mvarType ← inferType mvar
      let abstractedType ← abstractMVars mvarType
      if verifiedInhabitedTypes.contains abstractedType then
        mvarIdsToRemove := mvarIdsToRemove.push mvarId
        continue
      else if potentiallyUninhabitedTypes.contains abstractedType then
        return (PotentiallyVacuous, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
      else -- This is a type we haven't seen yet. Try to synthesize inhabited
        match ← Meta.tryFindInstance mvarType with
        | none => return (PotentiallyVacuous, verifiedInhabitedTypes, abstractedType :: potentiallyUninhabitedTypes)
        | some _ =>
          verifiedInhabitedTypes := abstractedType :: verifiedInhabitedTypes
          mvarIdsToRemove := mvarIdsToRemove.push mvarId
  if mvarIdsToRemove.size == 0 then
    return (NoVanishedVars, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
  else
    let cp ← yieldClause mclause "removeVanishedVars" (some mkRemoveVanishedVarsProof) (mvarIdsToRemove := mvarIdsToRemove)
    return (Success cp, verifiedInhabitedTypes, potentiallyUninhabitedTypes)

/-- Iterates through c's bVarTypes and removes each bVarType whose bvar does not appear in c. If `removeVanishedVars`
    encounters a bVarType that does not appear in c.lits and has not been verified to be inhabited, then it adds c to the
    set of potentially vacuous clauses and returns none.
    
    Note: removeVanishedVars is not written as a forward simplification rule (even though it functions similarly) because
    it uniquely interacts with ProverM's verifiedInhabitedTypes and potentiallyUninhabitedTypes. -/
def removeVanishedVars (givenClause : Clause) : ProverM (Option Clause) := do
  let (res, verifiedInhabitedTypes, potentiallyUninhabitedTypes) ← runRuleM $
    removeVanishedVarsHelper givenClause (← getVerifiedInhabitedTypes) (← getPotentiallyUninhabitedTypes)
  setVerifiedInhabitedTypes verifiedInhabitedTypes
  setPotentiallyUninhabitedTypes potentiallyUninhabitedTypes
  match res with
  | NoVanishedVars => return givenClause -- Continue the main saturation loop with givenClause
  | PotentiallyVacuous =>
    addPotentiallyVacuousToActive givenClause
    return none
  | Success (c, cProof) =>
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated c
    match (← getAllClauses).find? givenClause with
    | some givenClauseInfo =>
      let generatingAncestors := givenClauseInfo.generatingAncestors
      let ci ← addNewClause c cProof generatingAncestors
      if ci.wasSimplified then return none -- No need to continue working on c because we've already seen previously that it will be simplified away
      return c
    | none => throwError "givenClause {givenClause} was not found"

/-- If givenClause is of the form `Nonempty t = True` or `True = Nonempty t`, then returns `(← abstractMVars t)` -/
def registerNewInhabitedTypesHelper (givenClause : Clause) : RuleM (Option AbstractMVarsResult) := do
  let givenClause ← loadClause givenClause
  let some t := getNonemptyType givenClause
    | return none
  abstractMVars t

/-- If givenClause has the form `Nonempty t = True` or `True = Nonempty t`, then add `t` to verifiedInhabitedTypes and add `givenClause`
    to inhabitedTypeWitnesses -/
def registerNewInhabitedTypes (givenClause : Clause) : ProverM Unit := do
  if givenClause.lits.size != 1 then return
  let some abstractedT ← runRuleM $  registerNewInhabitedTypesHelper givenClause
    | return -- If registerNewInhabitedTypesHelper returns none, then givenClause is not of the appropriate form
  let verifiedInhabitedTypes ← getVerifiedInhabitedTypes
  if verifiedInhabitedTypes.contains abstractedT then return
  else
    setVerifiedInhabitedTypes (abstractedT :: verifiedInhabitedTypes)
    setInhabitedTypeWitnesses ((← getInhabitedTypeWitnesses).insert givenClause)