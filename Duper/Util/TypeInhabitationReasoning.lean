import Lean
import Duper.Util.Misc
import Duper.BackwardSimplification
import Duper.Util.ProofReconstruction

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
| NotVacuous (res : Clause × Proof) : VarRemovalRes -- Indicates that `res.1` has no potentially empty bvar types
| PotentiallyVacuous (res : Clause × Proof) : VarRemovalRes -- Indicates that `res.1` has at least one potentially empty bvar type
| NoChangeNotVacuous : VarRemovalRes -- Indicates that the input clause had no bvars that should be removed
| NoChangePotentiallyVacuous : VarRemovalRes -- Indicates that the input clause has potentially empty bvar types that couldn't or shouldn't be removed

open VarRemovalRes

def getNonemptyType (c : MClause) : Option Expr :=
  if c.lits.size != 1 then none
  else
    let lit := c.lits[0]!
    match lit.lhs, lit.rhs with
    | .app (.const ``Nonempty _) t, .const ``True _ => some t
    | .const ``True _, .app (.const ``Nonempty _) t => some t
    | _, _ => none

def mkRemoveVanishedVarsProof (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let (parentsLits, appliedPremises, transferExprs) ← instantiatePremises parents premises xs transferExprs
    let size := appliedPremises.length
    let appliedPremise := appliedPremises[size - 1]!
    Meta.mkLambdaFVars xs $ appliedPremise

/-- mkDeriveNewNonemptyTypeProof1 expects to receive one parent of the form `Nonempty (t1 → t2) = True` where `t1` is
    a type in verifiedInhabitedTypes (and is therefore a type whose inhabitation status can be confirmed by Lean.Meta.findInstance).
    
    Note: Right now, mkDeriveNewNonemptyTypeProof1 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof1 to support that case. -/
def mkDeriveNewNonemptyTypeProof1 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) (.forallE _ t1 t2 _))) (.const ``True []) =>
      match ← Lean.Meta.findInstance t1 with
      | some t1Inst =>
        let t1ArrowT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
        let t1ArrowT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1ArrowT2Nonempty]
        let t2Inst := Expr.app t1ArrowT2Inst t1Inst
        let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
        Meta.mkAppM ``eq_true #[t2Nonempty]
      | none => throwError "mkDeriveNewNonemptyTypeProof1 received parent: {parents[0]!.clause.toExpr} whose hypothesis could not be instantiated"
    | _ => throwError "mkDeriveNewNonemptyTypeProof1 received invalid parent: {parents[0]!.clause.toExpr}"

/-- mkDeriveNewNonemptyTypeProof2 expects to receive two parents, first a clause that says `Nonempty (t1 → t2) = True` and second
    a clause that says `Nonempty t1 = True`.
    
    Note: Right now, mkDeriveNewNonemptyTypeProof2 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof2 to support that case. -/
def mkDeriveNewNonemptyTypeProof2 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) (.forallE _ t1 t2 _))) (.const ``True []) =>
      match parents[1]!.clause.toForallExpr with
      | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) t1')) (.const ``True []) =>
        if ← Lean.Meta.isDefEq t1 t1' then
          let t1ArrowT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
          let t1ArrowT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1ArrowT2Nonempty]
          let t1'Nonempty ← Meta.mkAppM ``of_eq_true #[premises[1]!]
          let t1'Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1'Nonempty]
          let t2Inst := Expr.app t1ArrowT2Inst t1'Inst
          let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
          Meta.mkAppM ``eq_true #[t2Nonempty]
        else throwError "mkDeriveNewNonemptyTypeProof2 received types that did not align"
      | .forallE _ t1Hyp (.app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) t1Conclusion)) (.const ``True [])) _ =>
        if ← Lean.Meta.isDefEq t1 (.forallE .anonymous t1Hyp t1Conclusion .default) then -- This case should only occur if t1 = t1Hyp → t1Conclusion
          let t1ArrowT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
          let t1ArrowT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1ArrowT2Nonempty]
          let t1Inst := .lam .anonymous t1Hyp (← Meta.mkAppM ``Classical.choice #[← Meta.mkAppM ``of_eq_true #[.app premises[1]! (.bvar 0)]]) .default
          let t2Inst := Expr.app t1ArrowT2Inst t1Inst
          let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
          Meta.mkAppM ``eq_true #[t2Nonempty]
        else throwError "mkDeriveNewNonemptyTypeProof2 received types that did not align"
      | _ => throwError "mkDeriveNewNonemptyTypeProof2 received invalid parent 1: {parents[1]!.clause.toExpr}"
    | .forallE _ t1 (.app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) t2)) (.const ``True [])) _ =>
      match parents[1]!.clause.toForallExpr with
      | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) t1')) (.const ``True []) =>
        if ← Lean.Meta.isDefEq t1 t1' then
          let t1ArrowT2Inst := .lam .anonymous t1 (← Meta.mkAppM ``Classical.choice #[← Meta.mkAppM ``of_eq_true #[.app premises[0]! (.bvar 0)]]) .default
          let t1'Nonempty ← Meta.mkAppM ``of_eq_true #[premises[1]!]
          let t1'Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1'Nonempty]
          let t2Inst := Expr.app t1ArrowT2Inst t1'Inst
          let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
          Meta.mkAppM ``eq_true #[t2Nonempty]
        else throwError "mkDeriveNewNonemptyTypeProof2 received types that did not align"
      | .forallE _ t1Hyp (.app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) t1Conclusion)) (.const ``True [])) _ =>
        if ← Lean.Meta.isDefEq t1 (.forallE .anonymous t1Hyp t1Conclusion .default) then -- This case should only occur if t1 = t1Hyp → t1Conclusion
          let t1ArrowT2Inst := .lam .anonymous t1 (← Meta.mkAppM ``Classical.choice #[← Meta.mkAppM ``of_eq_true #[.app premises[0]! (.bvar 0)]]) .default
          let t1Inst := .lam .anonymous t1Hyp (← Meta.mkAppM ``Classical.choice #[← Meta.mkAppM ``of_eq_true #[.app premises[1]! (.bvar 0)]]) .default
          let t2Inst := Expr.app t1ArrowT2Inst t1Inst
          let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
          Meta.mkAppM ``eq_true #[t2Nonempty]
        else throwError "mkDeriveNewNonemptyTypeProof2 received types that did not align"
      | _ => throwError "mkDeriveNewNonemptyTypeProof2 received invalid parent 1: {parents[1]!.clause.toExpr}"
    | _ => throwError "mkDeriveNewNonemptyTypeProof2 received invalid parent 0: {parents[0]!.clause.toExpr}"

/-- Determines if `Nonempty abstractedType` can be derived specifically from `Nonempty t` -/
partial def deriveNonemptyFrom (abstractedType : AbstractMVarsResult) (t : AbstractMVarsResult) : MetaM Bool := do
  if t == abstractedType then return true
  else
    match abstractedType.expr with
    | Expr.forallE .. =>
      let (_, _, originalType) ← openAbstractMVarsResult abstractedType
      match originalType with
      | Expr.forallE _ _ b _ =>
        let b' ← abstractMVars b
        deriveNonemptyFrom b' t
      | _ => throwError "Inconsistency between original and abstractd type"
    | _ => return false

/-- Determines if `Nonempty abstractedType` can be derived from any type in `verifiedNonemptyTypes` -/
def deriveNonempty (abstractedType : AbstractMVarsResult) (verifiedNonemptyTypes : abstractedMVarAndClauseList) : MetaM (Option Clause) := do
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
  let mut resPotentiallyVacuous := false
  for mvar in mvars do
    let mvarId := mvar.mvarId!
    let mvarType ← inferType mvar
    let abstractedType ← abstractMVars mvarType
    if s.emap.contains mvarId then
      if verifiedInhabitedTypes.contains abstractedType then
        continue -- Don't remove mvarId because it appears in clause body
      match ← deriveNonempty abstractedType verifiedNonemptyTypes with
      | some _ => continue -- Don't remove mvarId because it appears in clause body
      | none =>
        if potentiallyUninhabitedTypes.contains abstractedType then
          resPotentiallyVacuous := true
        else -- This is a type we haven't seen yet. Try to synthesize Inhabited
          match ← Meta.findInstance mvarType with
          | none =>
            resPotentiallyVacuous := true
          | some _ => -- Don't remove mvarId because it appears in clause body
            verifiedInhabitedTypes := abstractedType :: verifiedInhabitedTypes
    else
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
          resPotentiallyVacuous := true
        else -- This is a type we haven't seen yet. Try to synthesize Inhabited
          match ← Meta.findInstance mvarType with
          | none =>
            resPotentiallyVacuous := true
          | some _ =>
            verifiedInhabitedTypes := abstractedType :: verifiedInhabitedTypes
            mvarIdsToRemove := mvarIdsToRemove.push mvarId
  if mvarIdsToRemove.size == 0 then
    if resPotentiallyVacuous then
      return (NoChangePotentiallyVacuous, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
    else
      return (NoChangeNotVacuous, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
  else
    let cp ← yieldClause mclause "removeVanishedVars" mkRemoveVanishedVarsProof (mvarIdsToRemove := mvarIdsToRemove)
    if resPotentiallyVacuous then
      return (PotentiallyVacuous cp, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
    else
      return (NotVacuous cp, verifiedInhabitedTypes, potentiallyUninhabitedTypes)

/-- Iterates through c's bVarTypes and removes each bVarType whose bvar does not appear in c. If `removeVanishedVars`
    encounters a bVarType that has not been verified to be inhabited, then it returns the updated clause and false to indicate
    that the clause should not be used to simplify away any other clauses. Otherwise, `removeVanishedVars` returns the updated
    clause and true. The only case where `removeVanishedVars` will return none is if it generates a clause that has already
    been simplified away (and therefore does not need to be re-evaluated).
    
    Note: removeVanishedVars is not written as a forward simplification rule (even though it functions similarly) because
    it uniquely interacts with ProverM's verifiedInhabitedTypes and potentiallyUninhabitedTypes. -/
def removeVanishedVars (givenClause : Clause) : ProverM (Option (Clause × Bool)) := do
  let (res, verifiedInhabitedTypes, potentiallyUninhabitedTypes) ← runRuleM $
    removeVanishedVarsHelper givenClause (← getVerifiedInhabitedTypes) (← getVerifiedNonemptyTypes) (← getPotentiallyUninhabitedTypes)
  setVerifiedInhabitedTypes verifiedInhabitedTypes
  setPotentiallyUninhabitedTypes potentiallyUninhabitedTypes
  match res with
  | NoChangePotentiallyVacuous => return some (givenClause, false)
  | NoChangeNotVacuous => return some (givenClause, true)
  | PotentiallyVacuous (c, cProof) =>
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated c
    match (← getAllClauses).find? givenClause with
    | some givenClauseInfo =>
      let generatingAncestors := givenClauseInfo.generatingAncestors
      let ci ← addNewClause c cProof generatingAncestors
      if ci.wasSimplified then return none -- No need to continue working on c because we've already seen previously that it will be simplified away
      return some (c, false)
    | none => throwError "givenClause {givenClause} was not found"
  | NotVacuous (c, cProof) =>
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated c
    match (← getAllClauses).find? givenClause with
    | some givenClauseInfo =>
      let generatingAncestors := givenClauseInfo.generatingAncestors
      let ci ← addNewClause c cProof generatingAncestors
      if ci.wasSimplified then return none -- No need to continue working on c because we've already seen previously that it will be simplified away
      return some (c, true)
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

/-- Derives new Nonempty types from the combination of the new Nonempty type `abstractedT` and current
    verifiedInhabitedTypes and verifiedNonemptyTypes. Specifically, deriveNewNonemptyTypes exhaustively applies the rule:
    - If any type in verifiedNonemptyTypes has the form `t1 → t2` and `abstractedT` matches `t1`, then derive `Nonempty t2` -/
def deriveNewNonemptyTypesHelper (abstractedT : AbstractMVarsResult) (givenClause : Clause) : ProverM Unit := do
  let verifiedNonemptyTypes ← getVerifiedNonemptyTypes
  for (t, c) in verifiedNonemptyTypes do
    match t.expr with
    | Expr.forallE .. =>
      let (_, _, originalT) ← openAbstractMVarsResult t
      if originalT.isArrow then -- Only attempt to derive `Nonempty t2 = True` if `t2` does not depend on `t1`
        match originalT with
        | Expr.forallE _ t1 t2 _ =>
          let t1' ← abstractMVars t1
          if abstractedT == t1' then
            /- `t` has the form `t1 → t2` and `t1` is Nonempty as witnessed by `givenClause`. Make the clause `Nonempty t2 = True`,
               and add the clause `Nonempty t2 = True` to the passive set. We specifically don't add `t2` to verifiedNonemptyTypes
               because that would cause `registerNewNonemptyTypes` to think that encountering `Nonempty t2 = True` doesn't warrant
               a re-examination of the potentially vacuous clause set. -/
            let t2NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t2]]
            let (t2NonemptyClause, t2NonemptyProof) ← runRuleM $ do
              let _ ← loadInhabitationClause c
              let _ ← loadInhabitationClause givenClause
              yieldClause t2NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof2
            match (← getAllClauses).find? givenClause with
            | some givenClauseInfo =>
              match (← getAllClauses).find? c with
              | some cInfo =>
                let generatingAncestors := cInfo.generatingAncestors ++ givenClauseInfo.generatingAncestors
                addNewToPassive t2NonemptyClause t2NonemptyProof generatingAncestors
              | none => throwError "{c} from verifiedNonemptyTypes was not found"
            | none => throwError "givenClause {givenClause} was not found"
        | _ => throwError "Inconsistency between original and abstracted type"
    | _ => continue

/-- Derives new Nonempty types from the combination of the new Nonempty type `abstractedT` and current
    verifiedInhabitedTypes and verifiedNonemptyTypes. Specifically, deriveNewNonemptyTypes exhaustively applies two rules:
    - If `abstractedT.expr` has the form `t1 → t2` and `t1` is Inhabited or Nonempty, then derive `Nonempty t2`
    - If any type in verifiedNonemptyTypes has the form `t1 → t2` and `abstractedT` matches `t1`, then derive `Nonempty t2`
    
    Jointly, these rules keep verifiedNonemptyTypes saturated with respect to application in the long run. Temporarily,
    verifiedNonemptyTypes can have a state where `α` `α → β` are both in verifiedNonemptyTypes but `β` is not, but this
    will only occur after `deriveNewNonemptyTypes` returns if either `Nonempty α` or `Nonempty (α → β)` was generated by
    `deriveNewNonemptyTypes`. Since `deriveNewNonemptyTypes` adds clauses it generates to the passive set (using `addNewToPassive`
    rather than `addNewClause`), these clauses that it generates will quickly be selected and sent to `registerNewNonemptyTypes`
    which will cause `Nonempty β` to be generated. -/
def deriveNewNonemptyTypes (abstractedT : AbstractMVarsResult) (givenClause : Clause) : ProverM Unit := do
  let verifiedInhabitedTypes ← getVerifiedInhabitedTypes
  let verifiedNonemptyTypes ← getVerifiedNonemptyTypes
  let potentinallyUninhabitedTypes ← getPotentiallyUninhabitedTypes
  match abstractedT.expr with
  | Expr.forallE .. =>
    let (_, _, originalT) ← openAbstractMVarsResult abstractedT
    match originalT with
    | Expr.forallE _ t1 t2 _ =>
      if originalT.isArrow then -- Only attempt to derive `Nonempty t2 = True` if `t2` does not depend on `t1`
        let t1' ← abstractMVars t1
        if verifiedInhabitedTypes.contains t1' then
          /- `abstractedT` has the form `t1 → t2` and `t1` is an Inhabited type. Make the clause `Nonempty t2 = True`,
             and add the clause `Nonempty t2 = True` to the passive set. We specifically don't add `t2` to verifiedNonemptyTypes
             because that would cause `registerNewNonemptyTypes` to think that encountering `Nonempty t2 = True` doesn't warrant
             a re-examination of the potentially vacuous clause set. -/
          let t2NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t2]]
          let (t2NonemptyClause, t2NonemptyProof) ← runRuleM $ do
            let _ ← loadInhabitationClause givenClause
            yieldClause t2NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof1
          match (← getAllClauses).find? givenClause with
          | some givenClauseInfo =>
            let generatingAncestors := givenClauseInfo.generatingAncestors
            addNewToPassive t2NonemptyClause t2NonemptyProof generatingAncestors
          | none => throwError "givenClause {givenClause} was not found"
        else
          match ← deriveNonempty t1' verifiedNonemptyTypes with
          | some c =>
            /- `abstractedT` has the form `t1 → t2` and `t1` is a Nonempty type. Make the clause `Nonempty t2 = True`,
               and add the clause `Nonempty t2 = True` to the passive set. We specifically don't add `t2` to verifiedNonemptyTypes
               because that would cause `registerNewNonemptyTypes` to think that encountering `Nonempty t2 = True` doesn't warrant
               a re-examination of the potentially vacuous clause set. -/
            let t2NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t2]]
            let (t2NonemptyClause, t2NonemptyProof) ← runRuleM $ do
              let _ ← loadInhabitationClause givenClause
              let _ ← loadInhabitationClause c
              yieldClause t2NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof2
            match (← getAllClauses).find? givenClause with
            | some givenClauseInfo =>
              let generatingAncestors := givenClauseInfo.generatingAncestors
              addNewToPassive t2NonemptyClause t2NonemptyProof generatingAncestors
            | none => throwError "givenClause {givenClause} was not found"
          | none =>
            if potentinallyUninhabitedTypes.contains t1' then pure ()
            else -- This is a type we haven't seen yet. Try to synthesize Inhabited
              match ← Meta.findInstance t1 with
              | some _ => -- We learned that `t1` is an Inhabited type so we updated verifiedInhabitedTypes to include it
                setVerifiedInhabitedTypes (t1' :: verifiedInhabitedTypes)
                /- `abstractedT` has the form `t1 → t2` and `t1` is an Inhabited type. Make the clause `Nonempty t2 = True`,
                   and add the clause `Nonempty t2 = True` to the passive set. We specifically don't add `t2` to verifiedNonemptyTypes
                   because that would cause `registerNewNonemptyTypes` to think that encountering `Nonempty t2 = True` doesn't warrant
                   a re-examination of the potentially vacuous clause set. -/
                let t2NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t2]]
                let (t2NonemptyClause, t2NonemptyProof) ← runRuleM $ do
                  let _ ← loadInhabitationClause givenClause
                  yieldClause t2NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof1
                match (← getAllClauses).find? givenClause with
                | some givenClauseInfo =>
                  let generatingAncestors := givenClauseInfo.generatingAncestors
                  addNewToPassive t2NonemptyClause t2NonemptyProof generatingAncestors
                | none => throwError "givenClause {givenClause} was not found"
              | none => -- We learned that Meta.findInstance can't find an instance for t1 so we update potentinallyUninhabitedTypes
                setPotentiallyUninhabitedTypes (t1' :: potentinallyUninhabitedTypes)
      deriveNewNonemptyTypesHelper abstractedT givenClause
    | _ => throwError "Inconsistency between original and abstracted type"
  | _ => deriveNewNonemptyTypesHelper abstractedT givenClause

/-- If givenClause has the form `Nonempty t = True` or `True = Nonempty t`, then add `t` to verifiedInhabitedTypes and add `givenClause`
    to inhabitedTypeWitnesses. Additionally, from the new Nonempty type fact, this function derives (and produces clauses for) any additional
    derivable Nonempty types. Finally, registerNewNonemptyTypes re-evaluates the set of potentially vacuous clauses to see if any clauses
    previously considered potentially vacuous can now be proven to not be potentially vacuous. -/
def registerNewNonemptyTypes (givenClause : Clause) : ProverM Unit := do
  if givenClause.lits.size != 1 then return
  let some abstractedT ← runRuleM $ registerNewInhabitedTypesHelper givenClause
    | return -- If registerNewInhabitedTypesHelper returns none, then givenClause is not of the appropriate form
  let verifiedNonemptyTypes ← getVerifiedNonemptyTypes
  if (← getVerifiedInhabitedTypes).contains abstractedT then return
  else if verifiedNonemptyTypes.any (fun (t, c) => t == abstractedT) then return
  else
    setVerifiedNonemptyTypes ((abstractedT, givenClause) :: verifiedNonemptyTypes)
    deriveNewNonemptyTypes abstractedT givenClause
    -- Re-evaluate potentially vacuous clauses
    let mut potentiallyVacuousClauses ← getPotentiallyVacuousClauses
    for c in potentiallyVacuousClauses do
      if ← runRuleM (clauseHasAbstractedT c abstractedT) then
        let (res, verifiedInhabitedTypes, potentiallyUninhabitedTypes) ← runRuleM $
          removeVanishedVarsHelper c (← getVerifiedInhabitedTypes) (← getVerifiedNonemptyTypes) (← getPotentiallyUninhabitedTypes)
        setVerifiedInhabitedTypes verifiedInhabitedTypes
        setPotentiallyUninhabitedTypes potentiallyUninhabitedTypes
        match res with
        | NoChangePotentiallyVacuous => continue -- c is still potentially vacuous, so nothing needs to change
        | NoChangeNotVacuous => -- c is no longer potentially vacuous, but has not been simplified into a new clause
          /- Since c is already in the active set, it has been forward simplified and has been added to most of ProverM's
             indices. All that remains is to use c for backward simplification rules and add it to the ProverM indices
             that it's not already in (currently, this is just subsumptionTrie and demodSidePremiseIdx) -/
          backwardSimplify c
          addToSimplifyingIndices c
        | PotentiallyVacuous (newC, newCProof) => -- Running removeVanishedVarsHelper generated a new clause that can directly be added to the passive set
          removeClause c -- We remove c and its descendants before readding newC to the passiveSet because newC makes c redundant
          match (← getAllClauses).find? c with
          | some givenClauseInfo =>
            let generatingAncestors := givenClauseInfo.generatingAncestors
            addNewToPassive newC newCProof generatingAncestors
          | none => throwError "givenClause {givenClause} was not found"
        | NotVacuous (newC, newCProof) => -- Running removeVanishedVarsHelper generated a new clause that can directly be added to the passive set
          removeClause c -- We remove c and its descendants before readding newC to the passiveSet because newC makes c redundant
          match (← getAllClauses).find? c with
          | some givenClauseInfo =>
            let generatingAncestors := givenClauseInfo.generatingAncestors
            addNewToPassive newC newCProof generatingAncestors
          | none => throwError "givenClause {givenClause} was not found"
    setPotentiallyVacuousClauses potentiallyVacuousClauses