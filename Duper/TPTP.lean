module

public import Lean
public import Duper.TPTPParser.MacroDecl

public section

open Lean
open Lean.Parser
open TSyntax.Compat
open Lean.Elab.Command

namespace TPTP

-- The `tptp` command is elaborated at compile time, so this option is `meta`.
meta register_option maxTPTPProblemLines : Nat := {
  defValue := 10000
  descr := "Line number limit (with comments stripped) for TPTP problems"
}

meta def getMaxTPTPProblemLines (opts : Options) : Nat :=
  maxTPTPProblemLines.get opts

meta def checkMaxTPTPProblemLines (lines : Nat) : CommandElabM Unit := do
  let opts ← getOptions
  let max := getMaxTPTPProblemLines opts
  if max < lines then
    let msg := s!"Number of lines {lines} in TPTP problem exceeded line number limit {max}"
    throw <| Exception.error (← getRef) (MessageData.ofFormat (Std.Format.text msg))

meta partial def parseTPTPInput (s : String) : CommandElabM Syntax := do
  match runParserCategory (← getEnv) `TPTP_input s with
  | Except.error e => throwError e
  | Except.ok r => return r

meta def sqstrToIdent (s : String) : String := Id.run <| do
  let mut ret := ""
  let mut curr : String.Pos.Raw := ⟨0⟩
  let mut sqcnt := 0
  while true do
    match String.Pos.Raw.get? s curr with
    | some ch =>
      if ch == '\'' then
        if sqcnt == 0 then
          ret := ret.push '«'
        else
          ret := ret.push '»'
        sqcnt := (sqcnt + 1) % 2
      else
        ret := ret.push ch
      curr := curr + ch
    | none => break
  return ret

meta def splitOnOutermostPeriod (s : String) : Array String := Id.run <| do
  let mut ret := #[]
  let mut last : String.Pos.Raw := ⟨0⟩
  let mut curr : String.Pos.Raw := ⟨0⟩
  let mut depth := 0
  while true do
    match String.Pos.Raw.get? s curr with
    | some ch =>
      curr := curr + ch
      if ch == '(' then
        depth := depth + 1
      if ch == ')' then
        depth := depth - 1
      if ch == '.' && depth == 0 then
        ret := ret.push (String.Pos.Raw.extract s last curr)
        last := curr
    | none => break
  return ret

meta def loadTptp (path : System.FilePath) : CommandElabM (Syntax × Nat) := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => ¬ l.startsWith "%"
  let s := String.join lines.toList
  -- Replace `$` with `🍉` so that it won't conflict with Lean's antiquot
  let s := s.replace "$" "🍉"
  let sarr := (splitOnOutermostPeriod s).map sqstrToIdent
  let mut stxarr : Array (TSyntax `TPTP_file) := #[]
  -- Parse input-by-input so that the parser is easier to debug
  for s in sarr do
    stxarr := stxarr.push ⟨← parseTPTPInput s⟩
  return (← `(TPTP_file| $[$stxarr]*), lines.size)

meta partial def resolveInclude (leadingPath : System.FilePath) : Syntax → CommandElabM (Syntax × Nat)
|`(TPTP_file| $[$f]*) => do
  let mut result := #[]
  let mut lines := 0
  for stx in f do
    let (stx, lineno) ← resolveInclude leadingPath stx
    lines := lines + lineno
    match stx with
    |`(TPTP_file| $[$g]*) => result := result.append g
    |`(TPTP_input| include( $_ ).) => throwError "resolveInclude :: include is not resolved in {stx}"
    | other => result := result.push other
  let stx ← `(TPTP_file| $[$result]*)
  return (stx, lines)
|`(TPTP_input| include( $ri ).) => do
  let path := leadingPath / (Lean.Syntax.getId ri.raw).getString!
  loadTptp path
| other => return (other, 0)

syntax (name := tptpKind) "tptp " ident strLit term : command

@[command_elab tptpKind] meta def elabResolve : CommandElab := fun stx => do
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
