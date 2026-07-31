module

public import Duper.ProofReconstruction

public section

open Lean
open Lean.Meta

namespace Duper

/-! Duper options and prover-setup utilities that are needed both at run time (by the
    standalone `duper` executable, see `Main.lean`) and at compile time (by the `duper`
    tactic, whose portfolio instances are `meta` definitions because they call `meta`
    definitions of `lean-auto`).

    Under the module system a `meta` definition may not refer to a non-`meta` definition of
    the same module, so these declarations live in their own module: `Duper.Interface`
    imports it both plainly and with `meta`, which makes them usable from either phase. -/

register_option duper.printPortfolioInstance : Bool := {
  defValue := false
  descr := "Whether to print the portfolio instance that solved the proof"
}

register_option duper.throwPortfolioErrors : Bool := {
  defValue := false
  descr := "Whether to halt portfolio mode and throw an error if a subinstance throws an error"
}

register_option duper.collectDatatypes : Bool := {
  defValue := false
  descr := "Whether to collect inductive datatypes for the purpose of generating datatype exhaustiveness facts"
}

def getPrintPortfolioInstance (opts : Options) : Bool :=
  duper.printPortfolioInstance.get opts

def getThrowPortfolioErrors (opts : Options) : Bool :=
  duper.throwPortfolioErrors.get opts

def getCollectDataTypes (opts : Options) : Bool :=
  duper.collectDatatypes.get opts

def getPrintPortfolioInstanceM : CoreM Bool := do
  let opts ← getOptions
  return getPrintPortfolioInstance opts

def getThrowPortfolioErrorsM : CoreM Bool := do
  let opts ← getOptions
  return getThrowPortfolioErrors opts

def getCollectDataTypesM : CoreM Bool := do
  let opts ← getOptions
  return getCollectDataTypes opts

/-- We save the `CoreM` state. This is because we will add a constant `skolemSorry` to the environment to support skolem constants with
    universe levels. We want to erase this constant after the saturation procedure ends -/
def withoutModifyingCoreEnv (m : MetaM α) : MetaM α :=
  try
    let env := (← liftM (get : CoreM Core.State)).env
    let ret ← m
    liftM (modify fun s => {s with env := env} : CoreM Unit)
    return ret
  catch e =>
    throwError e.toMessageData

/-- `skSorryAx` has essentially the same type as `sorryAx`, but does not trigger a `sorry` warning in `Lean.addAndCompile`. We want
    to deliberately bypass the warning in `Lean.addAndCompile` because the `skolemSorry` constant that Duper adds to the environment
    is only temporary and will be removed from the actual proof that should be checked by the kernel. -/
axiom skSorryAx : ∀ {α : Sort u}, α

/-- Add the constant `skolemSorry` to the environment and add suitable postfix to avoid name conflict. -/
def addSkolemSorry : CoreM Name := do
  let nameS := "skS"
  let env := (← get).env
  let mut cnt := 0
  let currNameSpace := (← read).currNamespace
  while true do
    let name :=
      match env.asyncPrefix? with
      | some p => Name.num (Name.str p nameS) cnt
      | none => Name.num (Name.str currNameSpace nameS) cnt
    if env.constants.contains name then
      cnt := cnt + 1
    else
      break
  let name :=
    match env.asyncPrefix? with
    | some p => Name.num (Name.str p nameS) cnt
    | none => Name.num (Name.str currNameSpace nameS) cnt
  trace[Meta.debug] "Created Skolem Sorry, name = {name}"
  let vlvlName := `v
  let vlvl := Level.param vlvlName
  let ulvlName := `u
  let ulvl := Level.param ulvlName
  -- Type = ∀ (p : Sort v) (n : Nat) (α : Sort u), α
  -- The preceeding ```Sort v``` is needed for recording level parameters.
  --   We'll show how it is used using the following example:
  -- Suppose we are clausifying
  --   ``∃ (x : Nat), f (Type u) x = g (Type v) x``
  -- Then the skolem constant should be
  --   ``Skolem.some (fun x => f (Type u) x = g (Type v) x)``
  -- In the ``skolemSorry`` approach without the ```Prop```, the skolem
  --   constant is stored as ```SkolemSorry <id> Nat```, which makes it
  --   difficult to keep track of ``u`` and ``v``. For example, sometimes
  --   superposition can cause a literal to contain two skolem constants
  --   with the same id and different levels. It's cumbersome to
  --   recover the levels, as we have to identify for each skolem constant
  --   in the result clause which parent it's from, and backtrack all the
  --   way to the clause where the skolem was created.
  -- To solve this problem, we record the levels within the ``p`` argument.
  --   In the above example, it will be recorded as ```Type u → Type v → Type```.
  let type := Expr.forallE `p (Expr.sort vlvl) (Expr.forallE `n (Expr.const ``Nat []) (
    Expr.forallE `α (Expr.sort ulvl) (.bvar 0) .implicit
  ) .default) .implicit
  -- Term = fun (p : Nat) (n : Nat) (α : Sort u) => skSorryAx.{u} α
  let term := Expr.lam `p (Expr.sort vlvl) (Expr.lam `n (Expr.const ``Nat []) (
    Expr.lam `α (Expr.sort ulvl) (
      Expr.app (Expr.const ``skSorryAx [ulvl]) (.bvar 0)
    ) .implicit
  ) .default) .implicit
  let opaqueVal : OpaqueVal := {name := name, levelParams := [vlvlName, ulvlName],
                                type := type, value := term, isUnsafe := true, all := [name]}
  let decl : Declaration := (.opaqueDecl opaqueVal)
  addDecl decl
  return name

def unfoldDefinitions (formulas : List (Expr × Expr × Array Name × Bool × Bool)) : MetaM (List (Expr × Expr × Array Name × Bool × Bool)) := do
  withTransparency .reducible do
    let mut newFormulas := formulas
    for (e, proof, paramNames, isFromGoal, includeInSetOfSupport) in formulas do
      let update (ty lhs rhs : Expr) newFormulas (containedIn : Expr → Bool) : MetaM _ := do
        if containedIn rhs then pure newFormulas else
          newFormulas.mapM fun (f, fproof, fparamNames, fIsFromGoal, _) => do
            if !containedIn f then
              return (f, fproof, fparamNames, fIsFromGoal, includeInSetOfSupport)
            else
              let us ← paramNames.mapM fun _ => mkFreshLevelMVar
              let lhs'   := lhs.instantiateLevelParamsArray paramNames us
              let ty'    := ty.instantiateLevelParamsArray paramNames us
              let rhs'   := rhs.instantiateLevelParamsArray paramNames us
              -- proof has the form: `eq_true h : fact = True` where `h : fact`
              let proof' ← Meta.mkAppM ``of_eq_true #[proof.instantiateLevelParamsArray paramNames us]
              let abstracted ← Meta.kabstract f lhs'
              let f := abstracted.instantiate1 rhs'
              let fproof ← withTransparency .default do mkAppOptM ``Eq.ndrec #[none,
                some lhs,
                some (← Meta.withLocalDeclD `_ ty' fun fvar => do
                  Meta.mkLambdaFVars #[fvar] $ ← Meta.mkAppM ``Eq #[abstracted.instantiate1 fvar, mkConst ``True]),
                some fproof,
                rhs',
                proof']
              return (f, ← instantiateMVars $ fproof, fparamNames, isFromGoal || fIsFromGoal, includeInSetOfSupport)
      match e with
      | .app ( .app ( .app (.const ``Eq _) ty) (.fvar fid)) rhs =>
        let containedIn := fun e => (e.find? (· == .fvar fid)).isSome
        newFormulas ← update ty (.fvar fid) rhs newFormulas containedIn
      | .app ( .app ( .app (.const ``Eq _) ty) (.const cname lvls)) rhs =>
        let containedIn := fun e => (e.find? (·.isConstOf cname)).isSome
        newFormulas ← update ty (.const cname lvls) rhs newFormulas containedIn
      | _ => pure ()
    return newFormulas

end Duper
