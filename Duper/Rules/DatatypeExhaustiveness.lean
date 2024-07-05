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
      trace[duper.rule.datatypeExhaustiveness] "makeConstructorEquality :: Returning {res} from e {e} and ctor {ctor.name}"
      mkAppM ``Eq #[res, mkConst ``True]

/-- Given an inductive datatype `idt`, with constructors `ctor₁, ctor₂, ... ctorₙ`, generates a fact of the form
    `∀ x : idt, x = ctor₁ ∨ x = ctor₂ ∨ ... x = ctorₙ` and adds it to the passive set. For example, if `idt = List Nat`,
    then `generateDatatypeExhaustivenessFact` generates `∀ l : List Nat, l = [] ∨ ∃ n : Nat, ∃ l' : List Nat, l = n :: l'`

    Note: This code does not currently support polymorphic inductive datatypes, both because the arguments are not presently
    collected properly, and because this code assumes that the generated clause has no parameters (which is not necessarily true
    when `idt` is universe polymorphic) -/
def generateDatatypeExhaustivenessFact (idt : Expr) : ProverM Unit := do
  let some (idtIndVal, lvls) ← matchConstInduct idt.getAppFn' (fun _ => pure none) (fun ival lvls => pure (some (ival, lvls)))
    | throwError "generateDatatypeExhaustivenessFact :: {idt} is not an inductive datatype"
  let idtArgs := idt.getAppArgs
  let constructors ← idtIndVal.ctors.mapM getConstInfoCtor
  trace[duper.rule.datatypeExhaustiveness] "Inductive datatype {idt} with args {idtArgs} has constructors {constructors.map (fun x => x.name)}"
  withLocalDeclD `_ idt fun idtFVar => do
    match constructors with
    | [] => -- `idt` is an inductive datatype with no constructors. This means that there cannot exist any elements of type `idt`
      let cExp ← mkForallFVars #[idtFVar] $ mkConst ``False
      let paramNames := #[] -- Assuming this is empty temporarily; This assumption does not hold if `idt` is universe polymorphic
      let c := Clause.fromForallExpr paramNames cExp
      let mkProof := fun _ _ _ _ => Lean.Meta.mkSorry cExp (synthetic := true)
      addNewToPassive c {parents := #[], ruleName := "datatypeExhaustiveness (empty inductive datatype)", mkProof := mkProof} maxGoalDistance 0 #[]
    | ctor1 :: restConstructors =>
      let mut cBody ← makeConstructorEquality idtFVar ctor1 lvls idtArgs
      for ctor in restConstructors do
        let ctorEquality ← makeConstructorEquality idtFVar ctor lvls idtArgs
        cBody ← mkAppM ``Or #[ctorEquality, cBody]
      let cExp ← mkForallFVars #[idtFVar] cBody
      let paramNames := #[] -- Assuming this is empty temporarily; This assumption does not hold if `idt` is universe polymorphic
      let c := Clause.fromForallExpr paramNames cExp
      let mkProof := fun _ _ _ _ => Lean.Meta.mkSorry cExp (synthetic := true)
      addNewToPassive c {parents := #[], ruleName := "datatypeExhaustiveness", mkProof := mkProof} maxGoalDistance 0 #[]

/-- For each inductive datatype in `inductiveDataTypes`, generates an exhaustiveness lemma
    (e.g. `∀ l : List Nat, l = [] ∨ ∃ n : Nat, ∃ l' : List Nat, l = n :: l'`) and adds it to the passive set -/
partial def generateDatatypeExhaustivenessFacts (inductiveDataTypes : List Expr) : ProverM Unit :=
  inductiveDataTypes.forM generateDatatypeExhaustivenessFact
