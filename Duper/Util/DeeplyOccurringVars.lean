import Lean
import Duper.Util.Misc
import Duper.Order
import Duper.MClause
import Duper.Expr

set_option linter.unusedVariables false

namespace Duper
open Lean

/-- Note: This function currently excludes lambdas that appear in forallE, lam, or letE types. -/
def occursInLambdaNotDirectlyBelowQuantifier (c : MClause) (t : Expr) : Bool :=
  -- For the visit function, inLambda is only set to true if the lambda visit is currently in is not directly below a quantifier
  let rec @[specialize] visit (e : Expr) (directlyBelowQuantifier : Bool) (inLambda : Bool) :=
    if inLambda && e == t then true else
    match e with
    | Expr.forallE _ ty b _ => visit b true inLambda
    | Expr.lam _ ty b _ =>
      if directlyBelowQuantifier then visit b false false
      else visit b false true
    | Expr.mdata _ e => visit e directlyBelowQuantifier inLambda
    | Expr.letE _ t v b _ =>
      -- Not sure if this is the best way to handle letE expressions
      -- For example, in `∃ x : ty, let y := s; t`, `t` is sort of directly below the quantifier even though it's technically under the letE expression
      visit v false inLambda || visit b false inLambda
    | Expr.app f a => visit f false inLambda || visit a false inLambda
    | Expr.proj _ _ e => visit e false inLambda
    | _ => false
  c.fold (fun b e => b || visit e false false) false

def occursInArgumentOfAppliedVariable (c : MClause) (t : Expr) : Bool :=
  let rec @[specialize] visit (e : Expr) (inArgumentOfAppliedVariable : Bool) :=
    if inArgumentOfAppliedVariable && e == t then true else
    match e with
    | Expr.forallE _ d b _ => visit d inArgumentOfAppliedVariable || visit b inArgumentOfAppliedVariable
    | Expr.lam _ d b _ => visit d inArgumentOfAppliedVariable || visit b inArgumentOfAppliedVariable
    | Expr.mdata _ e => visit e inArgumentOfAppliedVariable
    | Expr.letE _ t v b _ => visit t inArgumentOfAppliedVariable || visit v inArgumentOfAppliedVariable || visit b inArgumentOfAppliedVariable
    | Expr.app f a =>
      if visit f inArgumentOfAppliedVariable then true
      else if f.getAppFn.isMVar' then visit a true
      else visit a inArgumentOfAppliedVariable
    | Expr.proj _ _ e => visit e inArgumentOfAppliedVariable
    | _ => false
  c.fold (fun b e => b || visit e false) false

/-- Returns true if `t` is an mvar that occurs deeply in MClause `c`.

    A variable occurs deeply in an mclause `c` if it occurs inside an argument of an applied
    variable or inside a λ-expression that is not directly below a quantifier. -/
def isDeep (c : MClause) (t : Expr) : Bool :=
  t.isMVar' && (occursInArgumentOfAppliedVariable c t || occursInLambdaNotDirectlyBelowQuantifier c t)

/-- A syntactic overapproximation of fluid or deep terms -/
def isFluidOrDeep (c : MClause) (t : Expr) : Bool := Order.isFluid t || isDeep c t
