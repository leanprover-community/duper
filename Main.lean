import Duper.Tactic
import Duper.TPTP -- Note: this import is needed to make sure that TPTP is compiled for the github actions
import Duper.TPTPParser.PrattParser


open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Duper
open ProverM

#check Ne
def run (input : String) : MetaM Unit := do


  let env ← getEnv
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Nat, levelParams := [], type := mkSort levelOne, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Bool, levelParams := [], type := mkSort levelOne, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Bool.false, levelParams := [], type := mkConst `Bool, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `sorryAx, levelParams := [`u], type := mkForall `α .default (mkSort (.param `u)) $ mkForall `synthetic .default (mkConst `Bool) $ mkBVar 1, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Eq, levelParams := [`u], type := mkForall `α .implicit (mkSort (.param `u)) $ ← mkArrow (mkBVar 0) $ ← mkArrow (mkBVar 1) $ mkSort levelZero, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `Ne, levelParams := [`u], type := mkForall `α .implicit (mkSort (.param `u)) $ ← mkArrow (mkBVar 0) $ ← mkArrow (mkBVar 1) $ mkSort levelZero, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `True, levelParams := [], type := mkSort levelZero, isUnsafe := false})
  let env ← ofExceptKernelException $ env.addDecl (.axiomDecl {name := `False, levelParams := [], type := mkSort levelZero, isUnsafe := false})
  setEnv env


  let e ← TPTP.toLeanExpr input
  
  let formulas := [(e, ← mkAppM `sorryAx #[mkSort levelZero, mkConst `Bool.false],#[])]
  --[(← mkAppM `Ne #[mkConst `Bool.false, mkConst `Bool.false], ← mkAppM `sorryAx #[mkSort levelZero, mkConst `Bool.false],#[])]

  let skSorryName ← addSkolemSorry
    let (_, state) ←
      ProverM.runWithExprs (ctx := {}) (s := {skolemSorryName := skSorryName})
        ProverM.saturateNoPreprocessingClausification
        formulas
    match state.result with
    | .contradiction => IO.println "SZS status Unsatisfiable"
    | _ => IO.println "SZS status Unknown"

def main : List String → IO UInt32 := fun args => do
  let env ← mkEmptyEnvironment
  let _ ← Meta.MetaM.toIO
    (ctxCore := {fileName := "none", fileMap := .ofString ""}) (sCore := {env})
    (ctx := {}) (s := {}) (run args[0]!)

  -- let _ ← Core.CoreM.toIO (ctx := {fileName := "none", fileMap := .ofString ""}) (s := {env := ← mkEmptyEnvironment}) do

  return 0