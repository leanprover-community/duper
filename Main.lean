import Duper.Tactic
import Duper.TPTP -- Note: this import is needed to make sure that TPTP is compiled for the github actions
import Duper.TPTPParser.PrattParser


open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Duper
open ProverM

def run (path : String) : MetaM Unit := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => ¬ l.startsWith "%"
  let code := String.join lines.toList

  let env ← getEnv
  let prop := mkSort levelZero
  let type := mkSort levelOne
  let sortu := mkSort (.param `u)
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
  
  setEnv env

  TPTP.compile code fun formulas => do
    let skSorryName ← addSkolemSorry
    let (_, state) ←
      ProverM.runWithExprs (ctx := {}) (s := {skolemSorryName := skSorryName})
        ProverM.saturateNoPreprocessingClausification
        (Array.toList formulas)
    match state.result with
    | .contradiction => IO.println "SZS status Unsatisfiable"
    | _ => IO.println "SZS status Unknown"

def main : List String → IO UInt32 := fun args => do
  if args.length == 0 then 
    println! "Please provide problem file."
    return 1
  else
    let env ← mkEmptyEnvironment
    let _ ← Meta.MetaM.toIO
      (ctxCore := {fileName := "none", fileMap := .ofString ""}) (sCore := {env})
      (ctx := {}) (s := {}) (run args[0]!)
    return 0