import Lean
import Duper.Unif
import Duper.MClause
import Duper.Match
import Duper.DUnif.UnifRules
import Duper.Util.IdStrategyHeap
import Duper.Util.AbstractMVars

namespace Duper

namespace RuleM
open Lean

register_option inhabitationReasoning : Bool := {
  defValue := true
  descr := "Whether to enable type inhabitation reasoning"
}

def getInhabitationReasoning (opts : Options) : Bool :=
  inhabitationReasoning.get opts

def getInhabitationReasoningM : CoreM Bool := do
  let opts ← getOptions
  return getInhabitationReasoning opts

structure Context where
  order : Expr → Expr → Bool → MetaM Comparison
  skolemSorryName : Name
deriving Inhabited

structure ProofParent where
  -- Instantiated parent
  expr : Expr
  -- Loaded clause
  clause : Clause
  paramSubst : Array Level
deriving Inhabited

structure SkolemInfo where
  -- The `proof` of the skolem constant
  expr   : Expr
  -- Universe levels of the skolem constant
  params : Array Name
deriving Inhabited

/-- Takes: Proofs of the parent clauses, ProofParent information, the transported Expressions
    (which will be turned into bvars in the clause) introduced by the rule, and the target clause -/
abbrev ProofReconstructor := List Expr → List ProofParent → Array Expr → Clause → MetaM Expr

structure Proof where
  parents : Array ProofParent
  ruleName : String := "unknown"
  mkProof : ProofReconstructor
  transferExprs : Array Expr := #[]
deriving Inhabited

structure LoadedClause where
  -- The loaded clause
  clause   : Clause
  -- Level MVars
  lmVarIds : Array LMVarId
  -- MVars
  mVarIds  : Array MVarId

structure State where
  loadedClauses : Array LoadedClause := #[]
  skolemMap : HashMap Nat SkolemInfo
deriving Inhabited

abbrev RuleM := ReaderT Context $ StateRefT State MetaM

end RuleM

-- The `postUnification` has an `Option` within it
--   because there may be post-unification checks,
--   which might fail.
structure ClauseStream where
  ug                    : DUnif.UnifierGenerator
  simplifiedGivenClause : Clause
  postUnification       : RuleM.RuleM (Option (Clause × RuleM.Proof))
  ruleName              : String

namespace RuleM
open Lean
open Lean.Core

initialize registerTraceClass `Rule

@[inline] def RuleM.run (x : RuleM α) (ctx : Context) (s : State) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def RuleM.run' (x : RuleM α) (ctx : Context) (s : State) : MetaM α :=
  Prod.fst <$> x.run ctx s

def getOrder : RuleM (Expr → Expr → Bool → MetaM Comparison) :=
  return (← read).order

def getSkolemSorryName : RuleM Name :=
  return (← read).skolemSorryName

def getLoadedClauses : RuleM (Array LoadedClause) :=
  return (← get).loadedClauses

def getSkolemMap : RuleM (HashMap Nat SkolemInfo) :=
  return (← get).skolemMap

def setLoadedClauses (loadedClauses : Array LoadedClause) : RuleM Unit :=
  modify fun s => { s with loadedClauses := loadedClauses }

def setState (s : State) : RuleM Unit :=
  modify fun _ => s

def setSkolemMap (skmap : HashMap Nat SkolemInfo) : RuleM Unit :=
  modify fun s => {s with skolemMap := skmap}

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

-- Easy to switch between first-order unification and higher-order unification
def unifierGenerator (l : Array (Expr × Expr)) : MetaM DUnif.UnifierGenerator :=
  DUnif.UnifierGenerator.fromExprPairs l

def replace (e : Expr) (target : Expr) (replacement : Expr) : RuleM Expr := do
  Core.transform e (pre := fun s => do
    if s == target then
      return TransformStep.done replacement
    else return TransformStep.continue s)

-- Support for skolems with universe levels
def wrapSort (paramNames : Array Name) : RuleM Expr := do
  let mut expr := Expr.sort (.succ .zero)
  let nameRev := paramNames.reverse
  for name in nameRev do
    expr := Expr.forallE `_ (.sort (Level.param name)) expr .default
  return expr

def unWrapSort (e : Expr) : MetaM (Array Level) := do
  Meta.forallTelescope e fun xs _ => do
    let tys ← xs.mapM Meta.inferType
    return tys.map Expr.sortLevel!

open Lean.Meta

-- Suppose `c : Clause = ⟨bs, ls⟩`, `(mVars, m) ← loadClauseCore c`
-- then
-- `m = c.instantiateRev mVars`
-- `m ≝ mkAppN c.toForallExpr mVars`
def loadClauseCore (c : Clause) : RuleM (Array Expr × MClause) := do
  let us ← c.paramNames.mapM fun _ => mkFreshLevelMVar
  let e := c.toForallExpr.instantiateLevelParamsArray c.paramNames us
  let (mvars, bis, e) ← forallMetaTelescope e
  setLoadedClauses ((← getLoadedClauses).push ⟨c, us.map Level.mvarId!, mvars.map Expr.mvarId!⟩)
  return (mvars, .fromExpr e)

def loadClause (c : Clause) : RuleM MClause := do
  let (_, mclause) ← loadClauseCore c
  return mclause

/-- Returns the MClause that would be returned by calling `loadClause c` and the Clause × Array MVarId pair that
    would be added to loadedClauses if `loadClause c` were called, but does not actually change the set of
    loaded clauses. The purpose of this function is to process a clause and turn it into an MClause while delaying
    the decision of whether to actually load it -/
def prepLoadClause (c : Clause) : RuleM (MClause × LoadedClause) := do
  let us ← c.paramNames.mapM fun _ => mkFreshLevelMVar
  let e := c.toForallExpr.instantiateLevelParamsArray c.paramNames us
  let (mvars, bis, e) ← forallMetaTelescope e
  return (.fromExpr e, ⟨c, us.map Level.mvarId!, mvars.map Expr.mvarId!⟩)

open Duper.AbstractMVars in
def neutralizeMClause (c : MClause) (loadedClauses : Array LoadedClause) (transferExprs : Array Expr) :
  M (Clause × Array ProofParent × Array Expr) := do
  -- process c, `umvars` stands for "uninstantiated mvars"
  -- `ec = concl[umvars]`
  let ec := c.toExpr
  -- `fec = concl[fvars]`
  let fec ← Duper.AbstractMVars.abstractExprMVars ec
  -- Abstract metavariables in expressions to be transported to proof reconstruction
  let ftransferExprs ← transferExprs.mapM Duper.AbstractMVars.abstractExprMVars
  let cst ← get
  -- `abstec = ∀ [fvars], concl[fvars] = ∀ [umvars], concl[umvars]`
  let abstec := cst.lctx.mkForall cst.fvars fec
  let transferExprs := ftransferExprs.map (cst.lctx.mkLambda cst.fvars)
  -- process loadedClause
  let mut proofParents : Array ProofParent := #[]
  for ⟨loadedClause, lmvarIds, mvarIds⟩ in loadedClauses do
    -- Restore exprmvars, but does not restore level mvars
    set {(← get) with lctx := cst.lctx, mctx := cst.mctx, fvars := cst.fvars, emap := cst.emap}
    -- Add `mdata` to protect the body from `getAppArgs`
    -- The inner part will no longer be used, it is almost dummy, except that it makes the type check
    -- `mprotectedparent = fun [vars] => parent[vars]`
    let mprotectedparent := Expr.mdata .empty loadedClause.toLambdaExpr
    -- `minstantiatedparent = (fun [vars] => parent[vars]) mvars[umvars] ≝ parent[mvars[umvars]]`
    let minstantiatedparent := mkAppN mprotectedparent (mvarIds.map mkMVar)
    -- `finstantiatedparent = (fun [vars] => parent[vars]) mvars[fvars]`
    -- In this following `AbstractMVars`, there are no universe metavariables
    let finstantiatedparent ← Duper.AbstractMVars.abstractExprMVars minstantiatedparent
    let lst ← get
    -- `instantiatedparent = fun fvars => ((fun [vars] => parent[vars]) mvars[fvars])`
    let instantiatedparent := lst.lctx.mkForall lst.fvars finstantiatedparent
    -- Make sure that levels are abstracted
    let lmvars := lmvarIds.map Level.mvar
    let lvarSubstWithExpr ← Duper.AbstractMVars.abstractExprMVars (Expr.const `_ <| lmvars.data)
    let paramSubst := Array.mk lvarSubstWithExpr.constLevels!
    proofParents := proofParents.push ⟨instantiatedparent, loadedClause, paramSubst⟩
  -- Deal with universe variables differently from metavariables :
  --   Vanished mvars are not put into clause, while vanished level
  --   variables are put into the clause. This is because mvars vanish
  --   frequently, and if we put all vanished mvars into clauses, it will
  --   make an unbearably long list of binders.
  let cst ← get
  let c := Clause.fromForallExpr cst.paramNames abstec
  return (c, proofParents, transferExprs)

open Duper.AbstractMVars in
-- Note: It is expected that no mvarId that appears in mvarIdsToRemove appears in c or transferExprs
def neutralizeMClauseInhabitedReasoningOn (c : MClause) (loadedClauses : Array LoadedClause) (transferExprs : Array Expr)
  (mvarIdsToRemove : Array MVarId) : M (Clause × Array ProofParent × Array Expr) := do
  -- process c, `umvars` stands for "uninstantiated mvars"
  -- `ec = concl[umvars]`
  let ec := c.toExpr
  -- `fec = concl[fvars]`
  let fec ← Duper.AbstractMVars.abstractExprMVars ec
  -- Abstract metavariables in expressions to be transported to proof reconstruction
  let ftransferExprs ← transferExprs.mapM Duper.AbstractMVars.abstractExprMVars
  -- process loadedClause
  let mut proofParentsPre : Array ProofParent := #[]
  for ⟨loadedClause, lmvarIds, mvarIds⟩ in loadedClauses do
    -- Add `mdata` to protect the body from `getAppArgs`
    -- The inner part will no longer be used, it is almost dummy, except that it makes the type check
    -- `mprotectedparent = fun [vars] => parent[vars]`
    let mprotectedparent := Expr.mdata .empty loadedClause.toLambdaExpr
    -- `minstantiatedparent = (fun [vars] => parent[vars]) mvars[umvars] ≝ parent[mvars[umvars]]`
    let minstantiatedparent := mkAppN mprotectedparent (mvarIds.map mkMVar)
    -- `finstantiatedparent = (fun [vars] => parent[vars]) mvars[fvars]`
    -- In this following `AbstractMVars`, there are no universe metavariables
    let finstantiatedparent ← Duper.AbstractMVars.abstractExprMVars minstantiatedparent
    -- Make sure that levels are abstracted
    let lmvars := lmvarIds.map Level.mvar
    let lvarSubstWithExpr ← Duper.AbstractMVars.abstractExprMVars (Expr.const `_ <| lmvars.data)
    let paramSubst := Array.mk lvarSubstWithExpr.constLevels!
    proofParentsPre := proofParentsPre.push ⟨finstantiatedparent, loadedClause, paramSubst⟩
  let cst ← get
  let lctx := cst.lctx
  -- Before building abstec, we want to process cst.lctx and cst.fvars to remove redundant abstractions
  -- An abstraction is redundant if it does not appear in fec or any transfer expression and has a type
  -- which has already been abstracted
  -- Ex: `∀ x : t, ∀ y : t, ∀ z : t, ∀ a : Nat, ∀ b : Nat, f a b` should become `∀ x : t, ∀ a : Nat, ∀ b : Nat, f a b`
  let mut fvars := cst.fvars
  let mut erasedFVars := #[]
  let mut abstractedTypes := HashSet.empty
  for fvar in cst.fvars do
    let fvarId := fvar.fvarId!
    let fvarDecl := lctx.getFVar! fvar
    let fvarType := fvarDecl.type
    if abstractedTypes.contains fvarType then
      if !fec.containsFVar fvarId && ftransferExprs.all (fun transferExpr => !transferExpr.containsFVar fvarId) then
        -- fvar is redundant
        fvars := fvars.erase fvar
        erasedFVars := erasedFVars.push fvar
    else
      abstractedTypes := abstractedTypes.insert fvarDecl.type
  -- In addition to removing redundant abstractions, we want to remove fvars that correspond to mvars that are in mvarsToRemove
  for mvarId in mvarIdsToRemove do
    let fvar := cst.emap.find! mvarId
    fvars := fvars.erase fvar
    erasedFVars := erasedFVars.push fvar
  -- `abstec = ∀ [fvars], concl[fvars] = ∀ [umvars], concl[umvars]`
  let abstec := lctx.mkForall fvars fec
  let transferExprs := ftransferExprs.map (lctx.mkLambda fvars)
  let c := Clause.fromForallExpr cst.paramNames abstec
  let proofParents := proofParentsPre.map (fun x =>
    -- `instantiatedparent = fun fvars => ((fun [vars] => parent[vars]) mvars[fvars])`
    let instantiatedparent := lctx.mkForall (fvars ++ erasedFVars) x.expr
    {x with expr := instantiatedparent})
  return (c, proofParents, transferExprs)

def yieldClause (mc : MClause) (ruleName : String) (mkProof : Option ProofReconstructor)
  (transferExprs : Array Expr := #[]) (mvarIdsToRemove : Array MVarId := #[]) : RuleM (Clause × Proof) := do
  -- Refer to `Lean.Meta.abstractMVars`
  let ((c, proofParents, transferExprs), st) :=
    if ← getInhabitationReasoningM then
      neutralizeMClauseInhabitedReasoningOn mc (← getLoadedClauses) transferExprs mvarIdsToRemove
        { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
    else
      neutralizeMClause mc (← getLoadedClauses) transferExprs { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  setNGen st.ngen
  -- This is redundant because the `mctx` won't change
  -- We should not reset `lctx` because fvars introduced by
  --   `AbstractMVars` are local to it
  setMCtx st.mctx
  
  let mkProof := match mkProof with
  | some mkProof => mkProof
  | none => fun _ _ _ _ =>
    -- TODO: Remove sorry!?
    Lean.Meta.mkSorry c.toForallExpr (synthetic := true)
  let proof := {
    parents := proofParents,  
    ruleName := ruleName,
    mkProof := mkProof,
    transferExprs := transferExprs
  }
  return (c, proof)

def compare (s t : Expr) (alreadyReduced : Bool) : RuleM Comparison := do
  let ord ← getOrder
  ord s t alreadyReduced

end RuleM

end Duper