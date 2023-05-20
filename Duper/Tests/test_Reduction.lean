import Lean
import Duper.Util.Reduction

open Duper
open Lean
open Elab
open Command
open Term

-- Test preprocessingFact
syntax (name := ppf) "#ppf" term : command

@[command_elab ppf]
def elabPpf : CommandElab
  | `(#ppf%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← preprocessFact e
      logInfoAt tk e
  | _ => throwUnsupportedSyntax

@[reducible]
def reducible_def : Nat := 2

-- Let expressions should be reduced
#ppf let x := 2; (x + x)
-- Instances should be reduced
#ppf (fun (x y : Nat) => x + y)
#ppf ((fun (x y : Nat) => x + y) = (fun (x y : Nat) => x + y) → False)
-- NE should not be reduced
#ppf ((fun (x y : Nat) => x + y) ≠ (fun (x y : Nat) => x + y))
#ppf (2 + (Nat.add 2 1))

-- Should not reduce definitions of transparency .default, because reducing
--   them will make the term unacceptably large, for example
#reduce Nat.add
-- These constants should be supplied as facts to Duper, and duper will
--   automatically fetch the required definitional equations for these
--   constants.
#ppf Nat.add

-- Should not reduce theorems
#ppf Nat.add_assoc
-- Should reduce reducible defs
#ppf (2 + reducible_def)


-- Test etaReduction
syntax (name := etared) "#etared" term : command

@[command_elab etared]
def elabEtared : CommandElab
  | `(#etared%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
      let e ← etaReduce e
      logInfoAt tk e
  | _ => throwUnsupportedSyntax

#etared (fun (x : Nat) => Nat.add 1 x)
#etared (fun (x y : Nat) => Nat.add x y)