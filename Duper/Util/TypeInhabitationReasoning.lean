import Lean
import Duper.Util.Misc
import Duper.ProverM
import Duper.Util.ProofReconstruction
import Duper.Simp

namespace Duper

namespace ProverM
open Lean
open Meta
open Lean.Core
open Result
open Std
open ProverM
open RuleM

/-- The inductive return type of `removeVanishedVarsHelper` -/
inductive VarRemovalRes
| Success (res : Clause × Proof) : VarRemovalRes -- Indicates that `res.1` is the same as the input clause with all bvars that don't appear in the body removed
| PotentiallyVacuous : VarRemovalRes -- Indicates that the input clause had bvars that don't appear in the body and couldn't be removed (because their types may be empty)
| NoVanishedVars : VarRemovalRes -- Indicates that the input clause had no bvars that don't appear in the body

open VarRemovalRes

def getNonemptyType (c : MClause) : Option Expr :=
  if c.lits.size != 1 then none
  else
    let lit := c.lits[0]!
    match lit.lhs, lit.rhs with
    | .app (.const ``Nonempty _) t, .const ``True _ => some t
    | .const ``True _, .app (.const ``Nonempty _) t => some t
    | _, _ => none

def mkTypeInhabitationReasoningProof (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let size := appliedPremises.length
    let appliedPremise := appliedPremises[size - 1]!
    Meta.mkLambdaFVars xs $ appliedPremise

/-- Determines if `Nonempty abstractedType` can be derived specifically from `Nonempty t` -/
partial def deriveNonemptyFrom (abstractedType : AbstractMVarsResult) (t : AbstractMVarsResult) : RuleM Bool := do
  if t == abstractedType then return true
  else
    match abstractedType.expr with
    | Expr.forallE _ _ b _ =>
      let b' ← abstractMVars b
      deriveNonemptyFrom b' t
    | _ => return false

/-- Determines if `Nonempty abstractedType` can be derived from any type in `verifiedNonemptyTypes` -/
def deriveNonempty (abstractedType : AbstractMVarsResult) (verifiedNonemptyTypes : abstractedMVarAndClauseList) : RuleM (Option Clause) := do
  match ← verifiedNonemptyTypes.findM? (fun (t, c) => deriveNonemptyFrom abstractedType t) with
  | some (_, c) => return some c
  | none => return none

/-- Attempts to remove the vanished variables that appear in c, updating verifiedInhabitedTypes and potentiallyUninhabitedTypes as it
    encounters types whose inhabitation status has not previously been checked. -/
def removeVanishedVarsHelper (c : Clause) (verifiedInhabitedTypes : abstractedMVarList) (verifiedNonemptyTypes : abstractedMVarAndClauseList)
  (potentiallyUninhabitedTypes : abstractedMVarList) : RuleM (VarRemovalRes × abstractedMVarList × abstractedMVarList) := do
  let (mvars, mclause) ← loadClauseCore c
  let mut verifiedInhabitedTypes := verifiedInhabitedTypes
  let (_, s) := AbstractMVars.abstractExprMVars mclause.toExpr { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  let mut mvarIdsToRemove := #[]
  for mvar in mvars do
    let mvarId := mvar.mvarId!
    if s.emap.contains mvarId then
      continue -- If the clause contains the mvar, then don't worry about it
    else
      let mvarType ← inferType mvar
      let abstractedType ← abstractMVars mvarType
      if verifiedInhabitedTypes.contains abstractedType then
        mvarIdsToRemove := mvarIdsToRemove.push mvarId
        continue
      match ← deriveNonempty abstractedType verifiedNonemptyTypes with
      | some c =>
        let _ ← loadInhabitationClause c  -- Adding c as a parent so that its proof will
                                          -- be reconstructed by proof reconstruction,
                                          -- and we'll be able to obtain the inhabitation
                                          -- proof in `findInstance`
        mvarIdsToRemove := mvarIdsToRemove.push mvarId
      | none =>
        if potentiallyUninhabitedTypes.contains abstractedType then
          return (PotentiallyVacuous, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
        else -- This is a type we haven't seen yet. Try to synthesize inhabited
          match ← Meta.findInstance mvarType with
          | none =>
            return (PotentiallyVacuous, verifiedInhabitedTypes, abstractedType :: potentiallyUninhabitedTypes)
          | some _ =>
            verifiedInhabitedTypes := abstractedType :: verifiedInhabitedTypes
            mvarIdsToRemove := mvarIdsToRemove.push mvarId
  if mvarIdsToRemove.size == 0 then
    return (NoVanishedVars, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
  else
    let cp ← yieldClause mclause "removeVanishedVars" mkTypeInhabitationReasoningProof (mvarIdsToRemove := mvarIdsToRemove)
    return (Success cp, verifiedInhabitedTypes, potentiallyUninhabitedTypes)

/-- Iterates through c's bVarTypes and removes each bVarType whose bvar does not appear in c. If `removeVanishedVars`
    encounters a bVarType that does not appear in c.lits and has not been verified to be inhabited, then it adds c to the
    set of potentially vacuous clauses and returns none.
    
    Note: removeVanishedVars is not written as a forward simplification rule (even though it functions similarly) because
    it uniquely interacts with ProverM's verifiedInhabitedTypes and potentiallyUninhabitedTypes. -/
def removeVanishedVars (givenClause : Clause) : ProverM (Option Clause) := do
  let (res, verifiedInhabitedTypes, potentiallyUninhabitedTypes) ← runRuleM $
    removeVanishedVarsHelper givenClause (← getVerifiedInhabitedTypes) (← getVerifiedNonemptyTypes) (← getPotentiallyUninhabitedTypes)
  setVerifiedInhabitedTypes verifiedInhabitedTypes
  setPotentiallyUninhabitedTypes potentiallyUninhabitedTypes
  match res with
  | NoVanishedVars => return givenClause -- Continue the main saturation loop with givenClause
  | PotentiallyVacuous =>
    addPotentiallyVacuousClause givenClause
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

/-- If givenClause is of the form `Nonempty t = True` or `True = Nonempty t`, then returns `(← abstractMVars t)`. If givenClause has the form
    `∀ x1 : t1, ∀ x2 : t2, ... Nonempty t = True`, then registerNewInhabitedTypesHelper returns `(← abstractMVars (t1 → t2 → ... → t))` -/
def registerNewInhabitedTypesHelper (givenClause : Clause) : RuleM (Option AbstractMVarsResult) := do
  let givenMClause ← loadClause givenClause
  let some t := getNonemptyType givenMClause
    | return none
  abstractMVars $ givenClause.bVarTypes.foldr (fun ty b => mkForall Name.anonymous BinderInfo.default ty b) t

/-- Returns true if any of `c`'s bVarTypes match `abstractedT` or have the form `α1 → α2 → ... abstractedT`. If this is the case, then said clause
    should be returned to the passive set (and removed from the set of potentially vacuous clauses) so that it can be re-evaluated. -/
def clauseHasAbstractedT (c : Clause) (abstractedT : AbstractMVarsResult) : RuleM Bool := do
  let (mvars, _) ← loadClauseCore c
  mvars.anyM
    (fun mvar => do
      let mvarType ← inferType mvar
      let abstractedMVarType ← abstractMVars mvarType
      deriveNonemptyFrom abstractedMVarType abstractedT
    )

/-- If givenClause has the form `Nonempty t = True` or `True = Nonempty t`, then add `t` to verifiedInhabitedTypes and add `givenClause`
    to inhabitedTypeWitnesses -/
def registerNewInhabitedTypes (givenClause : Clause) : ProverM Unit := do
  if givenClause.lits.size != 1 then return
  let some abstractedT ← runRuleM $ registerNewInhabitedTypesHelper givenClause
    | return -- If registerNewInhabitedTypesHelper returns none, then givenClause is not of the appropriate form
  let verifiedInhabitedTypes ← getVerifiedInhabitedTypes
  let verifiedNonemptyTypes ← getVerifiedNonemptyTypes
  if verifiedInhabitedTypes.contains abstractedT then return
  else if verifiedNonemptyTypes.any (fun (t, c) => t == abstractedT) then return
  else
    setVerifiedNonemptyTypes ((abstractedT, givenClause) :: verifiedNonemptyTypes)
    let mut potentiallyVacuousClauses ← getPotentiallyVacuousClauses
    let mut passiveSet ← getPassiveSet
    for c in potentiallyVacuousClauses do
      if ← runRuleM (clauseHasAbstractedT c abstractedT) then
        potentiallyVacuousClauses := potentiallyVacuousClauses.erase c
        let ci ← getClauseInfo! c -- ci definitely exists because c has already been put into potentiallyVacuousClauses
        passiveSet := passiveSet.insert c c.weight ci.number
    setPotentiallyVacuousClauses potentiallyVacuousClauses
    setPassiveSet passiveSet