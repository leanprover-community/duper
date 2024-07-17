import Duper.RuleM
import Duper.Util.ProofReconstruction

namespace Duper
open ProverM RuleM Lean Meta

initialize Lean.registerTraceClass `duper.rule.datatypeExhaustiveness

/-- Given an expression `∀ x1 : t1, x2 : t2, ... xn : tn, b`, returns `[t1, t2, ..., tn]`. If the given expression is not
    a forall expression, then `getForallArgumentTypes` just returns the empty list -/
partial def getForallArgumentTypes (e : Expr) : List Expr :=
  match e.consumeMData with
  | Expr.forallE _ t b _ => t :: (getForallArgumentTypes b)
  | _ => []

def mkEmptyDatatypeExhaustivenessProof (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let emptyTypeFVar := xs[xs.size - 1]!
    let emptyType ← inferType emptyTypeFVar
    let some (emptyTypeName, lvls) ← matchConstInduct emptyType.getAppFn' (fun _ => pure none) (fun ival lvls => pure (some (ival.name, lvls)))
      | throwError "mkEmptyDatatypeExhaustivenessProof :: {emptyType} is not an inductive datatype"
    let motive := .lam `_ emptyType (mkConst ``False) .default -- motive is `fun _ : emptyType => False`
    mkLambdaFVars xs $ ← mkAppM' (mkConst (.str emptyTypeName "casesOn") (0 :: lvls)) #[motive, emptyTypeFVar]

def mkDatatypeExhaustivenessProof (premises : List Expr) (parents: List ProofParent) (transferExprs : Array Expr) (c : Clause) : MetaM Expr := do
  Meta.forallTelescope c.toForallExpr fun xs body => do
    let cLits := c.lits.map (fun l => l.map (fun e => e.instantiateRev xs))
    let idtFVar := xs[xs.size - 1]!
    let idt ← inferType idtFVar
    let some (idtIndVal, lvls) ← matchConstInduct idt.getAppFn' (fun _ => pure none) (fun ival lvls => pure (some (ival, lvls)))
      | throwError "mkDatatypeExhaustivenessProof :: {idt} is not an inductive datatype"
    let idtArgs := idt.getAppArgs.map some -- Mapping `some` to each element so it can be passed into `mkAppOptM'`
    let constructors ← idtIndVal.ctors.mapM getConstInfoCtor
    let motive ← mkLambdaFVars #[idtFVar] body
    let mut casesOnArgs := #[] -- Each of these is an expression of type `∀ ctorFields, motive (ctor ctorFields)`
    for ctor in constructors do
      let orIdx := idtIndVal.numCtors - ctor.cidx - 1
      let ctorBeforeFields ← mkAppOptM' (mkConst ctor.name lvls) idtArgs
      let ctorType ← inferType ctorBeforeFields
      let ctorArgTypes := getForallArgumentTypes ctorType
      let curCasesOnArg ←
        if ctorArgTypes.isEmpty then
          let rflProof ← mkAppM ``Eq.refl #[ctorBeforeFields]
          let idtFVarSubst := {map := AssocList.cons idtFVar.fvarId! ctorBeforeFields AssocList.nil}
          let cLits := cLits.map (fun l => l.map (fun e => e.applyFVarSubst idtFVarSubst))
          orIntro (cLits.map Lit.toExpr) orIdx rflProof
        else
          withLocalDeclsD (ctorArgTypes.map fun ty => (`_, fun _ => pure ty)).toArray fun ctorArgs => do
            let fullyAppliedCtor ← mkAppM' ctorBeforeFields ctorArgs
            let existsProof ←
              withLocalDeclsD (ctorArgTypes.map fun ty => (`_, fun _ => pure ty)).toArray fun ctorArgs' => do
                /-  Suppose ctorArgs = #[ctorArg0, ctorArg1] and ctorArgs' = #[ctorArg0', ctorArg1']
                    Then we need to build:
                    - @Exists.intro _ p1 ctorArg1 $ @Exists.intro _ p0 ctorArg0 $ Eq.refl (ctor ctorArg0 ctorArg1)
                    Where:
                    - p0 = `fun x => ctor ctorArg0 ctorArg1 = ctor x ctorArg1` (made via mkLambdaFVars #[ctorArg0']...)
                    - p1 = `fun y => ∃ x : ctorArg1Type, ctor ctorArg0 ctorArg1 = ctor x y` -/
                let mut rhsCtorArgs := ctorArgs
                rhsCtorArgs := rhsCtorArgs.set! 0 ctorArgs'[0]!
                let baseEquality ← mkAppM ``Eq #[fullyAppliedCtor, ← mkAppM' ctorBeforeFields rhsCtorArgs]
                let existsIntroArg ← mkLambdaFVars #[ctorArgs'[0]!] baseEquality
                let baseRflProof ← mkAppM ``Eq.refl #[fullyAppliedCtor]
                let mut existsProof ← mkAppOptM ``Exists.intro #[none, some existsIntroArg, some ctorArgs[0]!, some baseRflProof]
                let mut ctorArgNum := 0
                for (ctorArg, ctorArg') in ctorArgs.zip ctorArgs' do
                  if ctorArgNum = 0 then
                    ctorArgNum := 1
                    continue
                  rhsCtorArgs := rhsCtorArgs.set! ctorArgNum ctorArgs'[ctorArgNum]!
                  let innerExistsProp ← do
                    let mut innerExistsProp ← mkAppM ``Eq #[fullyAppliedCtor, ← mkAppM' ctorBeforeFields rhsCtorArgs]
                    for i in [0:ctorArgNum] do
                      innerExistsProp ← mkLambdaFVars #[ctorArgs'[i]!] innerExistsProp
                      innerExistsProp ← mkAppM ``Exists #[innerExistsProp]
                    pure innerExistsProp
                  let existsIntroArg ← mkLambdaFVars #[ctorArg'] innerExistsProp
                  existsProof ← mkAppOptM ``Exists.intro #[none, some existsIntroArg, some ctorArg, some existsProof]
                  ctorArgNum := ctorArgNum + 1
                pure existsProof
            let existsProof ← mkAppM ``eq_true #[existsProof]
            let idtFVarSubst := {map := AssocList.cons idtFVar.fvarId! fullyAppliedCtor AssocList.nil}
            let cLits := cLits.map (fun l => l.map (fun e => e.applyFVarSubst idtFVarSubst))
            let orProof ← orIntro (cLits.map Lit.toExpr) orIdx existsProof
            mkLambdaFVars ctorArgs orProof
      casesOnArgs := casesOnArgs.push $ some curCasesOnArg
    mkLambdaFVars xs $ ← mkAppOptM' (mkConst (.str idtIndVal.name "casesOn") (0 :: lvls)) (idtArgs ++ #[some motive, some idtFVar] ++ casesOnArgs)

/-- Creates the expression `(∃ fields, e = ctor.{lvls} params fields) = True` where `params` are the inductive datatype's parameters
    and `fields` are arguments that need to be passed into `ctor` for the resulting expression to have the correct inductive type -/
def makeConstructorEquality (e : Expr) (ctor : ConstructorVal) (lvls : List Level) (params : Array Expr) : MetaM Expr := do
  if ctor.numFields = 0 then mkAppM ``Eq #[e, ← mkAppOptM' (mkConst ctor.name lvls) (params.map some)]
  else
    let ctorBeforeFields ← mkAppOptM' (mkConst ctor.name lvls) (params.map some)
    let ctorType ← inferType ctorBeforeFields
    let ctorArgTypes := getForallArgumentTypes ctorType
    withLocalDeclsD (ctorArgTypes.map fun ty => (`_, fun _ => pure ty)).toArray fun ctorArgs => do
      let mut res ← mkAppM ``Eq #[e, ← mkAppM' ctorBeforeFields ctorArgs]
      for ctorArg in ctorArgs do
        res ← mkLambdaFVars #[ctorArg] res
        res ← mkAppM ``Exists #[res]
      mkAppM ``Eq #[res, mkConst ``True]

/-- Given an inductive datatype `idt`, with constructors `ctor₁, ctor₂, ... ctorₙ`, generates a fact of the form
    `∀ x : idt, x = ctor₁ ∨ x = ctor₂ ∨ ... x = ctorₙ` and adds it to the passive set. For example, if `idt = List Nat`,
    then `generateDatatypeExhaustivenessFact` generates `∀ l : List Nat, l = [] ∨ ∃ n : Nat, ∃ l' : List Nat, l = n :: l'`

    Polymorphic inductive datatypes are represented as universally quantified types paired with an array of parameters
    that can appear in the inductive datatype. For example, the polymorphic list datatype `List α` of where `α : Type u`
    is represented via `idt` `∀ (α : Type u), List α` and `paramNames` `#[u]` -/
def generateDatatypeExhaustivenessFact (idt : Expr) (paramNames : Array Name) : ProverM Unit := do
  forallTelescope idt fun idtParams idtBody => do
    let some (idtIndVal, lvls) ← matchConstInduct idtBody.getAppFn' (fun _ => pure none) (fun ival lvls => pure (some (ival, lvls)))
      | throwError "generateDatatypeExhaustivenessFact :: {idt} is not an inductive datatype"
    let idtArgs := idtBody.getAppArgs
    let constructors ← idtIndVal.ctors.mapM getConstInfoCtor
    withLocalDeclD `_ idtBody fun idtFVar => do
      match constructors with
      | [] => -- `idtBody` is an inductive datatype with no constructors. This means that there cannot exist any elements of type `idtBody`
        let cExp ← mkForallFVars (idtParams.push idtFVar) $ mkConst ``False
        let c := Clause.fromForallExpr paramNames cExp
        addNewToPassive c {parents := #[], ruleName := "datatypeExhaustiveness (empty inductive datatype)", mkProof := mkEmptyDatatypeExhaustivenessProof} maxGoalDistance 0 #[]
      | ctor1 :: restConstructors =>
        let mut cBody ← makeConstructorEquality idtFVar ctor1 lvls idtArgs
        for ctor in restConstructors do
          let ctorEquality ← makeConstructorEquality idtFVar ctor lvls idtArgs
          cBody ← mkAppM ``Or #[ctorEquality, cBody]
        let cExp ← mkForallFVars (idtParams.push idtFVar) cBody
        let c := Clause.fromForallExpr paramNames cExp
        trace[duper.rule.datatypeExhaustiveness] "About to add {c} to passive set"
        addNewToPassive c {parents := #[], ruleName := "datatypeExhaustiveness", mkProof := mkDatatypeExhaustivenessProof} maxGoalDistance 0 #[]

/-- For each inductive datatype in `inductiveDataTypes`, generates an exhaustiveness lemma
    (e.g. `∀ l : List Nat, l = [] ∨ ∃ n : Nat, ∃ l' : List Nat, l = n :: l'`) and adds it to the passive set -/
partial def generateDatatypeExhaustivenessFacts (inductiveDataTypes : List (Expr × Array Name)) : ProverM Unit :=
  inductiveDataTypes.forM (fun x => generateDatatypeExhaustivenessFact x.1 x.2)
