import Duper
import Duper.TPTP -- Note: this import is needed to make sure that TPTP is compiled for the github actions
import Duper.TPTPParser.PrattParser

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Duper
open ProverM

/-- Entry point for calling a single instance of duper using the options determined by (← getOptions).

    Formulas should consist of lemmas supplied by the user (to see how to obtain formulas from duper's input syntax, see `collectAssumptions`).
    InstanceMaxHeartbeats should indicate how many heartbeats duper should run for before timing out (if instanceMaxHeartbeats is set to 0,
    then duper will run until it is timed out by the Core `maxHeartbeats` option). If Duper succeeds in deriving a contradiction and constructing
    a proof for it, then `runDuper` returns that proof as an expression. Otherwise, Duper will throw an error. -/
def runDuperOnTPTP (fileName : String) (formulas : List (Expr × Expr × Array Name × Bool)) (instanceMaxHeartbeats : Nat) : MetaM Unit := do
  let state ←
    withNewMCtxDepth do
      let formulas ← unfoldDefinitions formulas
      /- `collectAssumptions` should not be wrapped by `withoutModifyingCoreEnv` because new definitional equations might be
          generated during `collectAssumptions` -/
      withoutModifyingCoreEnv <| do
        -- Add the constant `skolemSorry` to the environment
        let skSorryName ← addSkolemSorry
        let (_, state) ←
          ProverM.runWithExprs (ctx := {}) (s := {instanceMaxHeartbeats := instanceMaxHeartbeats, skolemSorryName := skSorryName})
            ProverM.saturateNoPreprocessingClausification
            formulas
        pure state
  match state.result with
  | Result.contradiction => IO.println s!"SZS status Theorem for {fileName}"
  | Result.saturated => IO.println s!"SZS status GaveUp for {fileName}"
  | Result.unknown => IO.println s!"SZS status Timeout for {fileName}"

def run (path : String) (github : Bool) : MetaM Unit := do
  let env ← getEnv
  let prop := mkSort levelZero
  let type := mkSort levelOne
  let sortu := mkSort (.param `u)
  let sortu1 := mkSort (.param `u1)
  let sortu2 := mkSort (.param `u2)
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Nat, levelParams := [], type := type, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Iota, levelParams := [], type := type, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Bool, levelParams := [], type := type, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Bool.false, levelParams := [], type := mkConst `Bool, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `sorryAx, levelParams := [`u], type := mkForall `α .default sortu $ mkForall `synthetic .default (mkConst `Bool) $ mkBVar 1, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Eq, levelParams := [`u], type := mkForall `α .implicit sortu $ ← mkArrow (mkBVar 0) $ ← mkArrow (mkBVar 1) $ prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Ne, levelParams := [`u], type := mkForall `α .implicit sortu $ ← mkArrow (mkBVar 0) $ ← mkArrow (mkBVar 1) $ prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `True, levelParams := [], type := prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `False, levelParams := [], type := prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Or, levelParams := [], type := ← mkArrow prop (← mkArrow prop prop), isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `And, levelParams := [], type := ← mkArrow prop (← mkArrow prop prop), isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Iff, levelParams := [], type := ← mkArrow prop (← mkArrow prop prop), isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Not, levelParams := [], type := ← mkArrow prop prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Exists, levelParams := [`u], type := mkForall `α .implicit sortu $ ← mkArrow (← mkArrow (mkBVar 0) prop) prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Duper.Skolem.some, levelParams := [`u], type := mkForall `α .implicit sortu $ ← mkArrow (← mkArrow (mkBVar 0) prop) $ ← mkArrow (mkBVar 1) (mkBVar 2), isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Nonempty, levelParams := [`u], type := mkForall `α .default sortu prop, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl
    { name := `Eq.ndrec, levelParams := [`u1, `u2],
      type :=
        mkForall `α .implicit sortu2 $
        mkForall `a .implicit (.bvar 0) $
        mkForall `motive .implicit (mkForall `x .default (.bvar 1) sortu1) $
        mkForall `m .default (mkApp (.bvar 0) (.bvar 1)) $
        mkForall `b .implicit (.bvar 3) $
        mkForall `h .default (mkApp3 (mkConst ``Eq [.param `u2]) (.bvar 4) (.bvar 3) (.bvar 0)) $
        (mkApp (.bvar 3) (.bvar 1)),
      isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl
    { name := `eq_true, levelParams := [],
      type :=
        mkForall `p .implicit prop $
        mkForall `h .default (.bvar 0) $
        (mkApp3 (mkConst ``Eq [levelOne]) prop (.bvar 1) (mkConst ``True [])),
      isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl
    { name := `of_eq_true, levelParams := [],
      type :=
        mkForall `p .implicit prop $
        mkForall `h .default (mkApp3 (mkConst ``Eq [levelOne]) prop (.bvar 0) (mkConst ``True [])) $
        (.bvar 1),
      isUnsafe := false})

  setEnv env

  TPTP.compileFile path fun formulas => do
    let formulas := Array.toList formulas
    let fileName := (path : System.FilePath).fileName.get!
    /- Going to try without Auto's preprocessing first. Although Duper performs better with Auto's preprocessing generally speaking, it's very plausible that Auto's preprocessing
       won't be particularly helpful for TPTP problems (though I should test it both ways, because it's possible that the preprocessing steps Auto performs aside from monomorphization
       are still helpful) -/

    /- Using the options from Duper instance 9:
       - preprocessing = no_preprocessing
       - inhabitationReasoning = false
       - selFunction = 4 (which corresponds to Zipperposition's default selection function)
       - includeExpensiveRules = false

       Additionally, we set maxHeartbeats to 0 so that Duper will run until the bash script terminates Duper -/
    withOptions (fun o => (((o.set `inhabitationReasoning false).set `selFunction 4).set `includeExpensiveRules false).set `maxHeartbeats 0) $
      runDuperOnTPTP fileName formulas 0

def main : List String → IO UInt32 := fun args => do
  if args.length == 0 then
    println! "Please provide problem file."
    return 1
  else
    let env ← mkEmptyEnvironment
    let github := (args.length > 1 && args[1]! == "--github")
    let maxHeartbeats := if github then 50 * 1000 * 1000 else 0
    let _ ← Meta.MetaM.toIO
      (ctxCore := {fileName := "none", fileMap := .ofString "", maxRecDepth := 10000, maxHeartbeats := maxHeartbeats}) (sCore := {env})
      (ctx := {}) (s := {}) (run args[0]! github)
    return 0
