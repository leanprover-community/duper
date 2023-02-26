import Lean
import Duper.Unif
import Duper.MClause
import Duper.Match
import Duper.DUnif.UnifRules
import Duper.Util.IdStrategyHeap

namespace Duper

namespace RuleM
open Lean
open Lean.Core

structure Context where
  order : Expr → Expr → MetaM Comparison
deriving Inhabited

structure ProofParent where
  expr : Expr
  clause : Clause

/-- Takes: Proofs of the parent clauses, ProofParent information, the indices of new variables
    (which will be turned into bvars in the clause) introduced by the rule, and the target clause -/
abbrev ProofReconstructor := List Expr → List ProofParent → List Nat → Clause → MetaM Expr

structure Proof where
  parents : List ProofParent := []
  ruleName : String := "unknown"
  introducedSkolems : Array (FVarId × (Array Expr → MetaM Expr)) := #[]
  mkProof : ProofReconstructor
  newVarIndices : List Nat := []
deriving Inhabited

structure State where
  mctx : MetavarContext := {}
  lctx : LocalContext := {}
  loadedClauses : List (Clause × Array MVarId) := []
deriving Inhabited

abbrev RuleM := ReaderT Context $ StateRefT State CoreM

end RuleM

-- The `postUnification` has an `Option` within it
--   because there may be post-unification checks,
--   which might fail.
structure ClauseStream where
  ug                    : DUnif.UnifierGenerator
  simplifiedGivenClause : Clause
  postUnification       : RuleM.RuleM (Option (Clause × RuleM.Proof))

namespace RuleM
open Lean
open Lean.Core

initialize
  registerTraceClass `Rule
  registerTraceClass `Rule.debug

instance : MonadLCtx RuleM where
  getLCtx := return (← get).lctx

instance : MonadMCtx RuleM where
  getMCtx    := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

@[inline] def RuleM.run (x : RuleM α) (ctx : Context) (s : State := {}) : CoreM (α × State) :=
  x ctx |>.run s

@[inline] def RuleM.run' (x : RuleM α) (ctx : Context) (s : State := {}) : CoreM α :=
  Prod.fst <$> x.run ctx s

@[inline] def RuleM.toIO (x : RuleM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context) (s : State := {}) : IO (α × Core.State × State) := do
  let ((a, s), sCore) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, sCore, s)

def getOrder : RuleM (Expr → Expr → MetaM Comparison) :=
  return (← read).order

def getContext : RuleM Context :=
  return {order := ← getOrder}

def getMCtx : RuleM MetavarContext :=
  return (← get).mctx

def getLoadedClauses : RuleM (List (Clause × Array MVarId)) :=
  return (← get).loadedClauses

def setMCtx (mctx : MetavarContext) : RuleM Unit :=
  modify fun s => { s with mctx := mctx }

def setLCtx (lctx : LocalContext) : RuleM Unit :=
  modify fun s => { s with lctx := lctx }

def setLoadedClauses (loadedClauses : List (Clause × Array MVarId)) : RuleM Unit :=
  modify fun s => { s with loadedClauses := loadedClauses }

def setState (s : State) : RuleM Unit :=
  modify fun _ => s

def withoutModifyingMCtx (x : RuleM α) : RuleM α := do
  let s ← getMCtx
  try
    x
  finally
    setMCtx s

/-- Runs x and only modifes the MCtx if the first argument returned by x is true (on failure, does not modify MCtx) -/
def conditionallyModifyingMCtx (x : RuleM (Bool × α)) : RuleM α := do
  let s ← getMCtx
  try
    let (shouldModifyMCtx, res) ← x
    if shouldModifyMCtx then
      return res
    else
      setMCtx s
      return res
  catch e =>
    setMCtx s
    throw e

-- TODO: Reset `introducedSkolems`?
def withoutModifyingLoadedClauses (x : RuleM α) : RuleM α := do
  let s ← getLoadedClauses
  try
    withoutModifyingMCtx x
  finally
    setLoadedClauses s

/-- Runs x and only modifies loadedClauses if the first argument returned by x is true (on failure, does not modify loadedClauses) -/
def conditionallyModifyingLoadedClauses (x : RuleM (Bool × α)) : RuleM α := do
  let s ← getLoadedClauses
  try
    let (shouldModifyLoadedClauses, res) ← x
    if shouldModifyLoadedClauses then
      return res
    else
      setLoadedClauses s
      return res
  catch e =>
    setLoadedClauses s
    throw e

instance : AddMessageContext RuleM where
  addMessageContext := addMessageContextFull

-- TODO: MonadLift
def runMetaAsRuleM (x : MetaM α) : RuleM α := do
  let lctx ← getLCtx
  let mctx ← getMCtx
  let (res, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) do
    x
  setMCtx state.mctx
  return res

def mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural) (userName := Name.anonymous) : RuleM Expr := do
  runMetaAsRuleM $ Meta.mkFreshExprMVar type? kind userName

def mkAppM (constName : Name) (xs : Array Expr) :=
  runMetaAsRuleM $ Meta.mkAppM constName xs

def mkAppOptM (constName : Name) (xs : Array (Option Expr)) :=
  runMetaAsRuleM $ Meta.mkAppOptM constName xs

def getMVarType (mvarId : MVarId) : RuleM Expr := do
  runMetaAsRuleM $ Lean.MVarId.getType mvarId

def forallMetaTelescope (e : Expr) (kind := MetavarKind.natural) : RuleM (Array Expr × Array BinderInfo × Expr) :=
  runMetaAsRuleM $ Meta.forallMetaTelescope e kind

def forallMetaTelescopeReducing (e : Expr) (maxMVars? : Option Nat := none) (kind := MetavarKind.natural) : RuleM (Array Expr × Array BinderInfo × Expr) :=
  runMetaAsRuleM $ Meta.forallMetaTelescopeReducing e maxMVars? kind

def mkFreshSkolem (name : Name) (type : Expr) (mkProof : Array Expr → MetaM Expr) : RuleM (Expr × (FVarId × (Array Expr → MetaM Expr))) := do
  let name := Name.mkNum name (← getLCtx).decls.size
  let (lctx, res) ← runMetaAsRuleM $ do
    Meta.withLocalDeclD name type fun x => do
      return (← getLCtx, x)
  setLCtx lctx
  return (res, (res.fvarId!, mkProof))

def mkForallFVars (xs : Array Expr) (e : Expr) (usedOnly : Bool := false) (usedLetOnly : Bool := true) : RuleM Expr :=
  runMetaAsRuleM $ Meta.mkForallFVars xs e usedOnly usedLetOnly

def inferType (e : Expr) : RuleM Expr :=
  runMetaAsRuleM $ Meta.inferType e

def instantiateMVars (e : Expr) : RuleM Expr :=
  runMetaAsRuleM $ Lean.instantiateMVars e

-- TODO : Delete this
-- Why we use unify in simplification rules?
def fastUnify (l : Array (Expr × Expr)) : RuleM Bool :=
  runMetaAsRuleM $ Meta.fastUnify l

def unifierGenerator (l : Array (Expr × Expr)) : RuleM DUnif.UnifierGenerator :=
  runMetaAsRuleM $ DUnif.UnifierGenerator.fromExprPairs l

/-- Given an array of expression pairs (match_target, e), attempts to assign mvars in e to make e equal to match_target.
    Returns true and performs mvar assignments if successful, returns false and does not perform any mvar assignments otherwise -/
def performMatch (l : Array (Expr × Expr)) (protected_mvars : Array MVarId) : RuleM Bool := do
  runMetaAsRuleM $ Meta.performMatch l protected_mvars

def isProof (e : Expr) : RuleM Bool := do
  runMetaAsRuleM $ Meta.isProof e

def isType (e : Expr) : RuleM Bool := do
  runMetaAsRuleM $ Meta.isType e

def getFunInfoNArgs (fn : Expr) (nargs : Nat) : RuleM Meta.FunInfo := do
  runMetaAsRuleM $ Meta.getFunInfoNArgs fn nargs

def replace (e : Expr) (target : Expr) (replacement : Expr) : RuleM Expr := do
  Core.transform e (pre := fun s => do
    if (← instantiateMVars s) == (← instantiateMVars target) then
      return TransformStep.done replacement
    else return TransformStep.continue s)

-- Suppose `c : Clause = ⟨bs, ls⟩`, `(mVars, m) ← loadClauseCore c`
-- then
-- `m = c.instantiateRev mVars`
-- `m ≝ mkAppN c.toForallExpr mVars`
def loadClauseCore (c : Clause) : RuleM (Array Expr × MClause) := do
  let (mVars, bis, e) ← forallMetaTelescope c.toForallExpr
  setLoadedClauses ((c, mVars.map Expr.mvarId!) :: (← getLoadedClauses))
  return (mVars, .fromExpr e)

def loadClause (c : Clause) : RuleM MClause := do
  let (_, mclause) ← loadClauseCore c
  return mclause

/-- Returns the MClause that would be returned by calling `loadClause c` and the Clause × Array MVarId pair that
    would be added to loadedClauses if `loadClause c` were called, but does not actually change the set of
    loaded clauses. The purpose of this function is to process a clause and turn it into an MClause while delaying
    the decision of whether to actually load it -/
def prepLoadClause (c : Clause) : RuleM (MClause × (Clause × Array MVarId)) := do
  let (mVars, bis, e) ← forallMetaTelescope c.toForallExpr
  return (.fromExpr e, (c, mVars.map Expr.mvarId!))

open Lean.Meta.AbstractMVars in
open Lean.Meta in
def neutralizeMClause (c : MClause) (loadedClauses : List (Clause × Array MVarId)) (freshMVarIds : List MVarId := []) :
  M (Clause × List ProofParent × List Nat) := do
  -- process c, `umvars` stands for "uninstantiated mvars"
  -- `ec = concl[umvars]`
  let ec := c.toExpr
  -- `fec = concl[fvars]`
  let fec ← AbstractMVars.abstractExprMVars ec
  let cst ← get
  -- `abstec = ∀ [fvars], concl[fvars] = ∀ [umvars], concl[umvars]`
  let abstec := cst.lctx.mkForall cst.fvars fec
  let c := Clause.fromForallExpr abstec
  -- process loadedClause
  let mut proofParents : List ProofParent := []
  for (loadedClause, mvarIds) in loadedClauses do
    set cst
    -- Add `mdata` to protect the body from `getAppArgs`
    -- The inner part will no longer be used, it is almost dummy, except that it makes the type check
    -- `mprotectedparent = fun [vars] => parent[vars]`
    let mprotectedparent := Expr.mdata .empty loadedClause.toLambdaExpr
    -- `minstantiatedparent = (fun [vars] => parent[vars]) mvars[umvars] ≝ parent[mvars[umvars]]`
    let minstantiatedparent := mkAppN mprotectedparent (mvarIds.map mkMVar)
    -- `finstantiatedparent = (fun [vars] => parent[vars]) mvars[fvars]`
    let finstantiatedparent ← AbstractMVars.abstractExprMVars minstantiatedparent
    let lst ← get
    -- `instantiatedparent = fun fvars => ((fun [vars] => parent[vars]) mvars[fvars])`
    let instantiatedparent := lst.lctx.mkForall lst.fvars finstantiatedparent
    proofParents := ⟨instantiatedparent, loadedClause⟩ :: proofParents
  -- Also return the bvars (represented as Nats) that correspond to the freshMVars
  let mvarMap := cst.emap -- cst.emap maps MVarIds to the free variables they have been replaced with
  let freshFVars := freshMVarIds.map (fun freshMVarId => mvarMap.find! freshMVarId)
  let newVarIndices := freshFVars.map (fun freshFVar => Option.get! $ cst.fvars.getIdx? freshFVar)
  return (c, proofParents, newVarIndices)

def yieldClause (mc : MClause) (ruleName : String) (mkProof : Option ProofReconstructor)
  (isk : Array (FVarId × (Array Expr → MetaM Expr)) := #[]) (freshMVarIds : List MVarId := []) : RuleM (Clause × Proof) := do
  -- Refer to `Lean.Meta.abstractMVars`
  let ((c, proofParents, newVarIndices), st) :=
    neutralizeMClause mc (← getLoadedClauses) freshMVarIds { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen st.ngen
  setMCtx st.mctx
  
  let mkProof := match mkProof with
  | some mkProof => mkProof
  | none => fun _ _ _ _ =>
    -- TODO: Remove sorry!?
    Lean.Meta.mkSorry c.toForallExpr (synthetic := true)
  let proof := {
    parents := proofParents,  
    ruleName := ruleName,
    introducedSkolems := isk,
    mkProof := mkProof,
    newVarIndices := newVarIndices
  }
  return (c, proof)

def compare (s t : Expr) : RuleM Comparison := do
  let ord ← getOrder
  runMetaAsRuleM do ord s t

end RuleM

end Duper