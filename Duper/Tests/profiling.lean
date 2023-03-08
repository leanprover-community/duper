import Lean

open Lean Core Meta
open Elab.Tactic

-- Trying to see whether monad stack is more efficient than
-- building two monads on top of the same base monad.
namespace MonadStackPerformance

structure State1 where
  mctx : MetavarContext := {}
  lctx : LocalContext := {}
  extra : Nat := 0

abbrev RuleM1 := StateRefT State1 CoreM

def runMetaAsRuleM1 (m : MetaM α) : RuleM1 α := do
  let lctx := (← get).lctx
  let mctx := (← get).mctx
  let (ret, state) ← Meta.MetaM.run (ctx := {lctx := lctx}) (s := {mctx := mctx}) m
  modify (fun s => {s with mctx := state.mctx})
  return ret

def ruleM1InferType : RuleM1 Unit :=
  for _ in [:1000000] do
    let _ ← runMetaAsRuleM1 (inferType (.const ``Nat []))

def runRuleM1 (m : RuleM1 α) : TacticM α := do
  let (ret, state) ← m.run {lctx := ← getLCtx, mctx := ← getMCtx}
  setMCtx state.mctx
  return ret

structure State2 where
  extra : Nat := 0

abbrev RuleM2 := StateRefT State2 MetaM

def ruleM2InferType : RuleM2 Unit :=
  for _ in [:1000000] do
    let _ ← inferType (.const ``Nat [])

def runRuleM2 (m : RuleM2 α) : TacticM α := do
  let (ret, _) ← m.run {}
  return ret

syntax (name := ruleM1Test) "ruleMTest" num : tactic

@[tactic ruleM1Test]
def runM1Test : Tactic
|`(tactic| ruleMTest $n) =>
  if n.getNat == 1 then
    runRuleM1 ruleM1InferType
  else
    runRuleM2 ruleM2InferType
| _ => throwError "Unsupported Syntax"

def foo : Nat := by
  ruleMTest 1; -- Change to ```ruleMTest 1``` to see difference
  exact 1

end MonadStackPerformance