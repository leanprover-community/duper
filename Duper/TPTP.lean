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
  let s := s.replace "$" "🍉"
  trace[Meta.debug] "{s}"
  parseMyType s

partial def resolveInclude (leadingPath : System.FilePath) : Syntax → CommandElabM Syntax
|`(TPTP_file| $[$f]*) => do
  let mut result := #[]
  for stx in f do
    match ← resolveInclude leadingPath stx with
    |`(TPTP_file| $[$g]*) => result := result.append g
    |`(TPTP_input| include( $ ).) => throwError "resolveInclude :: include is not resolved in {stx}"
    | other => result := result.push other
  `(TPTP_file| $[$result]*)
|`(TPTP_input| include( $sqstr ).) => do
  let path := leadingPath / (Lean.Syntax.getSingleQuotedStr sqstr)
  loadTptp path
| other => return other

syntax (name := tptpKind) "tptp " ident strLit term : command

@[command_elab tptpKind] def elabResolve : CommandElab := fun stx => do
  match stx with
  | `(tptp $name $file $proof) =>
    match Syntax.isStrLit? file with
    | some file =>
        let fstx ← loadTptp file
        let components := (⟨file⟩ : System.FilePath).components
        let leadingPath := System.mkFilePath (components.take (components.length - 3))
        let fstxResolved ← resolveInclude leadingPath fstx
        elabCommand (← `(BEGIN_TPTP $name $fstxResolved END_TPTP $proof))
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse tptp command"