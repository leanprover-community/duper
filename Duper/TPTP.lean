import Lean
import Duper.TPTPParser.MacroDecl

open Lean
open Lean.Parser
open TSyntax.Compat
open Lean.Elab.Command

namespace TPTP

register_option maxTPTPProblemLines : Nat := {
  defValue := 10000
  descr := "Line number limit (with comments stripped) for TPTP problems"
}

def getMaxTPTPProblemLines (opts : Options) : Nat :=
  maxTPTPProblemLines.get opts

def checkMaxTPTPProblemLines (lines : Nat) : CommandElabM Unit := do
  let opts ← getOptions
  let max := getMaxTPTPProblemLines opts
  if max < lines then
    let msg := s!"Number of lines {lines} in TPTP problem exceeded line number limit {max}"
    throw <| Exception.error (← getRef) (MessageData.ofFormat (Std.Format.text msg))

partial def parseTPTPInput (s : String) : CommandElabM Syntax := do
  match runParserCategory (← getEnv) `TPTP_input s with
  | Except.error e => throwError e
  | Except.ok r => return r

def splitOnOutermostPeriod (s : String) : Array String := Id.run <| do
  let mut ret := #[]
  let mut last : String.Pos := ⟨0⟩
  let mut curr : String.Pos := ⟨0⟩
  let mut depth := 0
  while true do
    match s.get? curr with
    | some ch =>
      curr := curr + ch
      if ch == '(' then
        depth := depth + 1
      if ch == ')' then
        depth := depth - 1
      if ch == '.' && depth == 0 then
        ret := ret.push (s.extract last curr)
        last := curr
    | none => break
  return ret

def loadTptp (path : System.FilePath) : CommandElabM (Syntax × Nat) := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => ¬ l.startsWith "%"
  let s := String.join lines.toList
  -- Replace `$` with `🍉` so that it won't conflict with Lean's antiquot
  let s := s.replace "$" "🍉"
  let sarr := splitOnOutermostPeriod s
  let mut stxarr : Array (TSyntax `TPTP_file) := #[]
  -- Parse input-by-input so that the parser is easier to debug
  for s in sarr do
    stxarr := stxarr.push ⟨← parseTPTPInput s⟩
  return (← `(TPTP_file| $[$stxarr]*), lines.size)

partial def resolveInclude (leadingPath : System.FilePath) : Syntax → CommandElabM (Syntax × Nat)
|`(TPTP_file| $[$f]*) => do
  let mut result := #[]
  let mut lines := 0
  for stx in f do
    let (stx, lineno) ← resolveInclude leadingPath stx
    lines := lines + lineno
    match stx with
    |`(TPTP_file| $[$g]*) => result := result.append g
    |`(TPTP_input| include( $ ).) => throwError "resolveInclude :: include is not resolved in {stx}"
    | other => result := result.push other
  let stx ← `(TPTP_file| $[$result]*)
  return (stx, lines)
|`(TPTP_input| include( $sqstr ).) => do
  let path := leadingPath / (Lean.Syntax.getSingleQuotedStr sqstr)
  loadTptp path
| other => return (other, 0)

syntax (name := tptpKind) "tptp " ident strLit term : command

@[command_elab tptpKind] def elabResolve : CommandElab := fun stx => do
  match stx with
  | `(tptp $name $file $proof) =>
    match Syntax.isStrLit? file with
    | some file =>
        let (fstx, lines) ← loadTptp file
        let components := (⟨file⟩ : System.FilePath).components
        let leadingPath := System.mkFilePath (components.take (components.length - 3))
        let (fstxResolved, extraLines) ← resolveInclude leadingPath fstx
        checkMaxTPTPProblemLines (lines + extraLines)
        elabCommand (← `(BEGIN_TPTP $name $fstxResolved END_TPTP $proof))
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse tptp command"