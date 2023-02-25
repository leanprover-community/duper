import Lean
import Duper.TPTPParser.MacroDecl

open Lean
open Lean.Parser
open TSyntax.Compat
open Lean.Elab.Command

namespace TPTP

partial def parseMyType (s : String) : CommandElabM Syntax := do
  match runParserCategory (← getEnv) `TPTP_file s with
  | Except.error e => throwError e
  | Except.ok r => return r

def loadTptp (path : System.FilePath) : CommandElabM Syntax := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => ¬ l.startsWith "%"
  let s := String.join lines.toList
  trace[Meta.debug] "{s}"
  parseMyType s

syntax (name := tptpKind) "tptp " ident strLit term : command

@[command_elab tptpKind] def elabResolve : CommandElab := fun stx => do
  match stx with
  | `(tptp $name $file $proof) =>
    match Syntax.isStrLit? file with
    | some file =>
        let fstx ← loadTptp file
        elabCommand (← `(BEGIN_TPTP $name $fstx END_TPTP $proof))
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse tptp command"