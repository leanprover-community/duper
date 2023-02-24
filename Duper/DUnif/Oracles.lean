import Lean
import Duper.DUnif.UnifProblem

open Lean
namespace Duper

register_option oracleInstOn : Bool := {
  defValue := true
  descr := "Whether to use instantiation oracle, which attempts to " ++
           "instantiate a side of the equation if it's a metavariable"
}

def getOracleInstOn (opts : Options) : Bool :=
  oracleInstOn.get opts

def oracleInst (p : UnifProblem) (eq : UnifEq) : MetaM (Option UnifProblem) := do
  setMCtx p.mctx
  let opts ← getOptions
  let mut mvarId : MVarId := Inhabited.default
  if ¬ getOracleInstOn opts then
    return none
  setMCtx p.mctx
  let mut eq := eq
  if let .mvar id := eq.rhs.eta then
    eq := eq.swapSide
    mvarId := id
  else
    if let .mvar id := eq.lhs.eta then
      mvarId := id
    else
      return none
  let (_, s) := Lean.Meta.AbstractMVars.abstractExprMVars eq.rhs { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  if s.emap.contains mvarId then
    return none
  else
    mvarId.assign eq.rhs
    return some {p.pushParentRule (.OracleInst eq) with checked := false, mctx := ← getMCtx}