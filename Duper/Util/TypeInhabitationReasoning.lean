import Lean
import Duper.Util.Misc
import Duper.BackwardSimplification
import Duper.Util.ProofReconstruction
import Duper.Expr

set_option linter.unusedVariables false

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

/-- mkDeriveNewNonemptyTypeProof3 expects to receive one parent of the form `Nonempty (t1 × t2) = True` and yields a proof
    of `Nonempty t1 = True`.

    Note: Right now, mkDeriveNewNonemptyTypeProof3 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof2 to support that case. -/
def mkDeriveNewNonemptyTypeProof3 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) (Expr.app (Expr.app (Expr.const ``Prod lvls) t1) t2))) (.const ``True []) =>
      let t1ProdT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
      let t1ProdT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1ProdT2Nonempty]
      let t1Inst ← Meta.mkAppM ``Prod.fst #[t1ProdT2Inst]
      let t1Nonempty ← Meta.mkAppM ``Nonempty.intro #[t1Inst]
      Meta.mkAppM ``eq_true #[t1Nonempty]
    | _ => throwError "mkDeriveNewNonemptyTypeProof3 received invalid parent: {parents[0]!.clause.toExpr}"

/-- mkDeriveNewNonemptyTypeProof4 expects to receive one parent of the form `Nonempty (t1 × t2) = True` and yields a proof
    of `Nonempty t2 = True`.

    Note: Right now, mkDeriveNewNonemptyTypeProof4 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof2 to support that case. -/
def mkDeriveNewNonemptyTypeProof4 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) (Expr.app (Expr.app (Expr.const ``Prod lvls) t1) t2))) (.const ``True []) =>
      let t1ProdT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
      let t1ProdT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1ProdT2Nonempty]
      let t2Inst ← Meta.mkAppM ``Prod.snd #[t1ProdT2Inst]
      let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
      Meta.mkAppM ``eq_true #[t2Nonempty]
    | _ => throwError "mkDeriveNewNonemptyTypeProof4 received invalid parent: {parents[0]!.clause.toExpr}"

/-- mkDeriveNewNonemptyTypeProof5 expects to receive one parent of the form `Nonempty (PProd t1 t2) = True` and yields a proof
    of `Nonempty t1 = True`.

    Note: Right now, mkDeriveNewNonemptyTypeProof5 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof2 to support that case. -/
def mkDeriveNewNonemptyTypeProof5 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) (Expr.app (Expr.app (Expr.const ``PProd lvls) t1) t2))) (.const ``True []) =>
      let t1PProdT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
      let t1PProdT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1PProdT2Nonempty]
      let t1Inst ← Meta.mkAppM ``PProd.fst #[t1PProdT2Inst]
      let t1Nonempty ← Meta.mkAppM ``Nonempty.intro #[t1Inst]
      Meta.mkAppM ``eq_true #[t1Nonempty]
    | _ => throwError "mkDeriveNewNonemptyTypeProof5 received invalid parent: {parents[0]!.clause.toExpr}"

/-- mkDeriveNewNonemptyTypeProof6 expects to receive one parent of the form `Nonempty (PProd t1 t2) = True` and yields a proof
    of `Nonempty t2 = True`.

    Note: Right now, mkDeriveNewNonemptyTypeProof6 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof2 to support that case. -/
def mkDeriveNewNonemptyTypeProof6 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) (Expr.app (Expr.app (Expr.const ``PProd lvls) t1) t2))) (.const ``True []) =>
      let t1PProdT2Nonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
      let t1PProdT2Inst ← Meta.mkAppOptM ``Classical.ofNonempty #[none, t1PProdT2Nonempty]
      let t2Inst ← Meta.mkAppM ``PProd.snd #[t1PProdT2Inst]
      let t2Nonempty ← Meta.mkAppM ``Nonempty.intro #[t2Inst]
      Meta.mkAppM ``eq_true #[t2Nonempty]
    | _ => throwError "mkDeriveNewNonemptyTypeProof6 received invalid parent: {parents[0]!.clause.toExpr}"

/-- mkDeriveNewNonemptyTypeProof7 expects to receive one parent of the form `Nonempty p = True` where `p : Prop`.
    mkDeriveNewNonemptyTypeProof6 yields a proof that `p = True`.

    Note: Right now, mkDeriveNewNonemptyTypeProof7 does not support lemmas of the form `True = Nonempty t`, and I think
    this is fine because Duper should never generate clauses of that form. However, if for some reason this ever becomes a problem,
    it should be straightforward to extend mkDeriveNewNonemptyTypeProof2 to support that case. -/
def mkDeriveNewNonemptyTypeProof7 (premises : List Expr) (parents : List ProofParent) (transferExprs : Array Expr)
  (c : Clause) : MetaM Expr :=
  Meta.forallTelescope c.toForallExpr fun xs body => do
    match parents[0]!.clause.toForallExpr with
    | .app (.app (.app (.const ``Eq _) _) (.app (.const ``Nonempty _) p)) (.const ``True []) =>
      if (← inferType p).isProp then
        let pNonempty ← Meta.mkAppM ``of_eq_true #[premises[0]!]
        let pProof ← Meta.mkAppOptM ``Classical.ofNonempty #[none, pNonempty]
        Meta.mkAppM ``eq_true #[pProof]
      else throwError "mkDeriveNewNonemptyTypeProof7 received invalid parent: {parents[0]!.clause.toExpr}"
    | _ => throwError "mkDeriveNewNonemptyTypeProof7 received invalid parent: {parents[0]!.clause.toExpr}"

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
  trace[duper.typeInhabitationReasoning.debug] "Calling removeVanishedVarsHelper on {c}"
  let (mvars, mclause) ← loadClauseCore c
  let mut verifiedInhabitedTypes := verifiedInhabitedTypes
  let mut potentiallyUninhabitedTypes := potentiallyUninhabitedTypes
  let (_, s) := AbstractMVars.abstractExprMVars mclause.toExpr { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  let mut mvarIdsToRemove := []
  let mut resPotentiallyVacuous := false
  let mut preservedMVarTypes : Array Expr := #[] -- The mvarTypes that are to be preserved in the clause. We can't remove any mvars that any of these types depend on
  /- Iterate through each of the mclause's mvars, determining whether the mvar needs to be preserved (in which case, its type is added to `preservedMVarTypes`) or
     whether it can be removed (in which case, its id is added to `mvarIdsToRemove`).

     We iterate through the mclause's mvars in reverse order so that we can handle dependencies between types correctly. For example, if we have
     `∀ x : t, ∀ y : f(x), p(y)`, then we cannot remove `y` because the clause body depends on it, and because we cannot remove `y`, we also cannot remove `x` (since
     `y`'s type depends on it). By iterating through the clause's mvars in reverse order, we ensure that we see `y` and add its type `f(x)` to `preservedMVarTypes`
     before we see `x`, so that when we see `x`, we can identify that it must be kept on the grounds that there is a type in `preservedMVarTypes` that depends on `x`.

     Note that because we have mvarIdsToRemove as a list (and add elements using cons rather than append), the last mvarIds we add to the list will appear first
     in the list which ensures that at the end, mvarIds corresponding to earlier bvars appear before mvarIds corresponding to later bvars. When dependent types are
     at play, preserving this invariant is important to ensure that `Duper.RuleM.neutralizeMClauseInhabitedReasoningOn` processes `mvarIdsToRemove` correctly. -/
  for mvar in mvars.reverse do
    trace[duper.typeInhabitationReasoning.debug] "Looking at {mvar}"
    let mvarId := mvar.mvarId!
    let mvarType ← inferType mvar
    let abstractedType ← abstractMVars mvarType
    if s.emap.contains mvarId || preservedMVarTypes.any (fun preservedType => preservedType.hasAnyMVar (fun m => m == mvarId)) then
      trace[duper.typeInhabitationReasoning.debug] "{mvar} is to be preserved"
      preservedMVarTypes := preservedMVarTypes.push mvarType -- Either the clause body or a later mvarType depends on the current mvar
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
            potentiallyUninhabitedTypes := abstractedType :: potentiallyUninhabitedTypes
            resPotentiallyVacuous := true
          | some _ => -- Don't remove mvarId because it appears in clause body
            let abstractedType ← abstractMVars mvarType -- Need to redefine `abstractedType` because `Meta.findInstance` can modify metavariables that appear in `mvarType`
            trace[duper.typeInhabitationReasoning.debug] "Adding abstractedType {abstractedType.expr} corresponding to {mvarType} to verifiedInhabitedtypes"
            verifiedInhabitedTypes := abstractedType :: verifiedInhabitedTypes
    else
      if verifiedInhabitedTypes.contains abstractedType then
        trace[duper.typeInhabitationReasoning.debug] "{mvar} is to be removed because verifiedInhabitedTypes contains the abstracted version of {mvarType}"
        mvarIdsToRemove := mvarId :: mvarIdsToRemove
        continue
      match ← deriveNonempty abstractedType verifiedNonemptyTypes with
      | some c =>
        trace[duper.typeInhabitationReasoning.debug] "{mvar} is to be removed because deriveNonempty found {c}"
        let _ ← loadInhabitationClause c  -- Adding c as a parent so that its proof will
                                          -- be reconstructed by proof reconstruction,
                                          -- and we'll be able to obtain the inhabitation
                                          -- proof in `findInstance`
        mvarIdsToRemove := mvarId :: mvarIdsToRemove
      | none =>
        if potentiallyUninhabitedTypes.contains abstractedType then
          trace[duper.typeInhabitationReasoning.debug] "{mvar} is to be preserved because the abstracted version of its type {mvarType} is potentially uninhabited"
          preservedMVarTypes := preservedMVarTypes.push mvarType -- Preserve current mvarType because the current mvar could not be removed
          resPotentiallyVacuous := true
        else -- This is a type we haven't seen yet. Try to synthesize Inhabited
          match ← Meta.findInstance mvarType with
          | none =>
            trace[duper.typeInhabitationReasoning.debug] "{mvar} is to be preserved because Meta.findInstance couldn't find an instance for {mvarType}"
            potentiallyUninhabitedTypes := abstractedType :: potentiallyUninhabitedTypes
            preservedMVarTypes := preservedMVarTypes.push mvarType -- Preserve current mvarType because the current mvar could not be removed
            resPotentiallyVacuous := true
          | some _ =>
            trace[duper.typeInhabitationReasoning.debug] "{mvar} is to be removed because Meta.findInstance found an instance for {mvarType}"
            let abstractedType ← abstractMVars mvarType -- Need to redefine `abstractedType` because `Meta.findInstance` can modify metavariables that appear in `mvarType`
            trace[duper.typeInhabitationReasoning.debug] "Adding abstractedType {abstractedType.expr} corresponding to {mvarType} to verifiedInhabitedtypes"
            verifiedInhabitedTypes := abstractedType :: verifiedInhabitedTypes
            mvarIdsToRemove := mvarId :: mvarIdsToRemove
  if mvarIdsToRemove.isEmpty then
    if resPotentiallyVacuous then
      return (NoChangePotentiallyVacuous, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
    else
      return (NoChangeNotVacuous, verifiedInhabitedTypes, potentiallyUninhabitedTypes)
  else
    let cp ← yieldClause mclause "removeVanishedVars" mkRemoveVanishedVarsProof (mvarIdsToRemove := mvarIdsToRemove)
    trace[duper.typeInhabitationReasoning.debug] "mkRemoveVanishedVarsProof: Yielded {cp.1} from {c}"
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
    match (← getAllClauses)[givenClause]? with
    | some givenClauseInfo =>
      let generatingAncestors := givenClauseInfo.generatingAncestors
      let generationNumber := givenClauseInfo.generationNumber
      let goalDistance := givenClauseInfo.goalDistance
      let ci ← addNewClause c cProof goalDistance generationNumber generatingAncestors
      if ci.wasSimplified then return none -- No need to continue working on c because we've already seen previously that it will be simplified away
      return some (c, false)
    | none => throwError "givenClause {givenClause} was not found"
  | NotVacuous (c, cProof) =>
    removeClause givenClause -- It is important that we remove givenClause and its descendants before readding the newly generated c
    match (← getAllClauses)[givenClause]? with
    | some givenClauseInfo =>
      let generatingAncestors := givenClauseInfo.generatingAncestors
      let generationNumber := givenClauseInfo.generationNumber
      let goalDistance := givenClauseInfo.goalDistance
      let ci ← addNewClause c cProof goalDistance generationNumber generatingAncestors
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
            match (← getAllClauses)[givenClause]? with
            | some givenClauseInfo =>
              match (← getAllClauses)[c]? with
              | some cInfo =>
                let generatingAncestors := cInfo.generatingAncestors ++ givenClauseInfo.generatingAncestors
                let generationNumber := givenClauseInfo.generationNumber
                let goalDistance := givenClauseInfo.goalDistance
                addNewToPassive t2NonemptyClause t2NonemptyProof goalDistance generationNumber generatingAncestors
              | none => throwError "{c} from verifiedNonemptyTypes was not found"
            | none => throwError "givenClause {givenClause} was not found"
        | _ => throwError "Inconsistency between original and abstracted type"
    | _ => continue

/-- Derives new Nonempty types from the combination of the new Nonempty type `abstractedT` and current
    verifiedInhabitedTypes and verifiedNonemptyTypes. Specifically, deriveNewNonemptyTypes exhaustively applies three rules:
    - If `abstracted.expr` has the form `t1 × t2` (where `×` denotes either `Prod` or `PProd`) then derive `Nonempty t1` and `Nonempty t2`
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
        match (← getAllClauses)[givenClause]? with
        | some givenClauseInfo =>
          let generatingAncestors := givenClauseInfo.generatingAncestors
          let generationNumber := givenClauseInfo.generationNumber
          let goalDistance := givenClauseInfo.goalDistance
          addNewToPassive t2NonemptyClause t2NonemptyProof goalDistance generationNumber generatingAncestors
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
          match (← getAllClauses)[givenClause]? with
          | some givenClauseInfo =>
            let generatingAncestors := givenClauseInfo.generatingAncestors
            let generationNumber := givenClauseInfo.generationNumber
            let goalDistance := givenClauseInfo.goalDistance
            addNewToPassive t2NonemptyClause t2NonemptyProof goalDistance generationNumber generatingAncestors
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
              match (← getAllClauses)[givenClause]? with
              | some givenClauseInfo =>
                let generatingAncestors := givenClauseInfo.generatingAncestors
                let generationNumber := givenClauseInfo.generationNumber
                let goalDistance := givenClauseInfo.goalDistance
                addNewToPassive t2NonemptyClause t2NonemptyProof goalDistance generationNumber generatingAncestors
              | none => throwError "givenClause {givenClause} was not found"
            | none => -- We learned that Meta.findInstance can't find an instance for t1 so we update potentinallyUninhabitedTypes
              setPotentiallyUninhabitedTypes (t1' :: potentinallyUninhabitedTypes)
    deriveNewNonemptyTypesHelper abstractedT givenClause
  | Expr.app (Expr.app (Expr.const ``Prod lvls) t1) t2 =>
    let t1' ← abstractMVars t1
    if !(verifiedInhabitedTypes.contains t1') && !(verifiedNonemptyTypes.any (fun (t, _) => t == t1')) then
      -- If t1 is not already known to be nonempty, then derive `Nonempty t1 = True`
      let t1NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t1]]
      let (t1NonemptyClause, t1NonemptyProof) ← runRuleM $ do
        let _ ← loadInhabitationClause givenClause
        yieldClause t1NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof3
      match (← getAllClauses)[givenClause]? with
      | some givenClauseInfo =>
        let generatingAncestors := givenClauseInfo.generatingAncestors
        let generationNumber := givenClauseInfo.generationNumber
        let goalDistance := givenClauseInfo.goalDistance
        addNewToPassive t1NonemptyClause t1NonemptyProof goalDistance generationNumber generatingAncestors
      | none => throwError "givenClause {givenClause} was not found"
    let t2' ← abstractMVars t2
    if !(verifiedInhabitedTypes.contains t2') && !(verifiedNonemptyTypes.any (fun (t, _) => t == t2')) then
      -- If t2 is not already known to be nonempty, then derive `Nonempty t2 = True`
      let t2NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t2]]
      let (t2NonemptyClause, t2NonemptyProof) ← runRuleM $ do
        let _ ← loadInhabitationClause givenClause
        yieldClause t2NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof4
      match (← getAllClauses)[givenClause]? with
      | some givenClauseInfo =>
        let generatingAncestors := givenClauseInfo.generatingAncestors
        let generationNumber := givenClauseInfo.generationNumber
        let goalDistance := givenClauseInfo.goalDistance
        addNewToPassive t2NonemptyClause t2NonemptyProof goalDistance generationNumber generatingAncestors
      | none => throwError "givenClause {givenClause} was not found"
    deriveNewNonemptyTypesHelper abstractedT givenClause
  | Expr.app (Expr.app (Expr.const ``PProd lvls) t1) t2 =>
    let t1' ← abstractMVars t1
    if !(verifiedInhabitedTypes.contains t1') && !(verifiedNonemptyTypes.any (fun (t, _) => t == t1')) then
      -- If t1 is not already known to be nonempty, then derive `Nonempty t1 = True`
      let t1NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t1]]
      let (t1NonemptyClause, t1NonemptyProof) ← runRuleM $ do
        let _ ← loadInhabitationClause givenClause
        yieldClause t1NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof5
      match (← getAllClauses)[givenClause]? with
      | some givenClauseInfo =>
        let generatingAncestors := givenClauseInfo.generatingAncestors
        let generationNumber := givenClauseInfo.generationNumber
        let goalDistance := givenClauseInfo.goalDistance
        addNewToPassive t1NonemptyClause t1NonemptyProof goalDistance generationNumber generatingAncestors
      | none => throwError "givenClause {givenClause} was not found"
    let t2' ← abstractMVars t2
    if !(verifiedInhabitedTypes.contains t2') && !(verifiedNonemptyTypes.any (fun (t, _) => t == t2')) then
      -- If t2 is not already known to be nonempty, then derive `Nonempty t2 = True`
      let t2NonemptyMClause := MClause.mk #[Lit.fromSingleExpr $ ← mkAppM ``Nonempty #[t2]]
      let (t2NonemptyClause, t2NonemptyProof) ← runRuleM $ do
        let _ ← loadInhabitationClause givenClause
        yieldClause t2NonemptyMClause "deriveNewNonemptyType" mkDeriveNewNonemptyTypeProof6
      match (← getAllClauses)[givenClause]? with
      | some givenClauseInfo =>
        let generatingAncestors := givenClauseInfo.generatingAncestors
        let generationNumber := givenClauseInfo.generationNumber
        let goalDistance := givenClauseInfo.goalDistance
        addNewToPassive t2NonemptyClause t2NonemptyProof goalDistance generationNumber generatingAncestors
      | none => throwError "givenClause {givenClause} was not found"
    deriveNewNonemptyTypesHelper abstractedT givenClause
  | _ =>
    if (← inferType originalT).isProp then
      -- Derive `p = True` from `Nonempty p = True` if `p : Prop`
      let originalTEqTrueMClause := MClause.mk #[Lit.fromSingleExpr originalT]
      let (originalTEqTrueClause, originalTEqTrueProof) ← runRuleM $ do
        let _ ← loadInhabitationClause givenClause
        yieldClause originalTEqTrueMClause "deriveFactFromNonempty" mkDeriveNewNonemptyTypeProof7
      match (← getAllClauses)[givenClause]? with
      | some givenClauseInfo =>
        let generatingAncestors := givenClauseInfo.generatingAncestors
        let generationNumber := givenClauseInfo.generationNumber
        let goalDistance := givenClauseInfo.goalDistance
        addNewToPassive originalTEqTrueClause originalTEqTrueProof goalDistance generationNumber generatingAncestors
      | none => throwError "givenClause {givenClause} was not found"
    deriveNewNonemptyTypesHelper abstractedT givenClause

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
          match (← getAllClauses)[c]? with
          | some givenClauseInfo =>
            let generatingAncestors := givenClauseInfo.generatingAncestors
            let generationNumber := givenClauseInfo.generationNumber
            let goalDistance := givenClauseInfo.goalDistance
            addNewToPassive newC newCProof goalDistance generationNumber generatingAncestors
          | none => throwError "givenClause {givenClause} was not found"
        | NotVacuous (newC, newCProof) => -- Running removeVanishedVarsHelper generated a new clause that can directly be added to the passive set
          removeClause c -- We remove c and its descendants before readding newC to the passiveSet because newC makes c redundant
          match (← getAllClauses)[c]? with
          | some givenClauseInfo =>
            let generatingAncestors := givenClauseInfo.generatingAncestors
            let generationNumber := givenClauseInfo.generationNumber
            let goalDistance := givenClauseInfo.goalDistance
            addNewToPassive newC newCProof goalDistance generationNumber generatingAncestors
          | none => throwError "givenClause {givenClause} was not found"
    setPotentiallyVacuousClauses potentiallyVacuousClauses
