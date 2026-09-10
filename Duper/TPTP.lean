module

public import Lean
public import Duper.TPTPParser.MacroDecl
public import Duper.TPTPParser.PrattParser
/- The `tptp'` command elaborator runs the Pratt parser at compile time, so it has to be
   available at compile time as well. -/
public meta import Duper.TPTPParser.PrattParser

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

/-! The `tptp'` command behaves like the `tptp` command but parses the problem file with
    `TPTP.compileFile` (the Pratt parser in `Duper.TPTPParser.PrattParser`, which is also used
    by duper's compiled executable in `Main.lean`) rather than with the syntax-based parser
    used by the `tptp` command. -/

/-- If `ty` has the form `T₁ → ... → Tₙ → Type` (i.e. `fvar` is a newly declared type or type
    constructor), returns the hypothesis `∀ (a₁ : T₁) ... (aₙ : Tₙ), Inhabited (fvar a₁ ... aₙ)`.
    Otherwise, returns `none`. This mirrors the `Inhabited` binders that the `BEGIN_TPTP` macro
    adds for the symbols that the problem declares to be types. -/
meta def mkInhabitedHyp (fvar : Expr) (ty : Expr) : MetaM (Option Expr) :=
  Meta.forallTelescope ty fun xs body => do
    if body == mkSort Level.one then
      let inhab ← Meta.mkAppM ``Inhabited #[mkAppN fvar xs]
      return some (← Meta.mkForallFVars xs inhab)
    else
      return none

syntax (name := tptpPrattKind) "tptp' " ident strLit term : command

@[command_elab tptpPrattKind] meta def elabTptpPratt : CommandElab := fun stx => do
  match stx with
  | `(tptp' $name $file $proof) =>
    match Syntax.isStrLit? file with
    | some path =>
      let lines ← IO.FS.lines path
      let lines := lines.filter fun l => ¬ l.startsWith "%"
      -- Note: unlike the `tptp` command, this count does not include the lines of included files
      checkMaxTPTPProblemLines lines.size
      let declName := (← getCurrNamespace) ++ name.getId
      liftTermElabM <| Elab.Term.withDeclName declName do
        /- `compileFile` introduces a free variable for each symbol and each formula of the
           problem, so capture the local context it builds in order to elaborate the proof in it -/
        let (lctx, localInsts) ← compileFile path fun _ =>
          return ((← getLCtx), (← Meta.getLocalInstances))
        Meta.withLCtx lctx localInsts do
          let fvars := lctx.foldl (init := #[]) fun acc decl =>
            if decl.isImplementationDetail then acc else acc.push decl.toExpr
          let mut inhabHyps : Array (Name × (Array Expr → Elab.TermElabM Expr)) := #[]
          for fvar in fvars do
            if let some hyp ← mkInhabitedHyp fvar (← Meta.inferType fvar) then
              inhabHyps := inhabHyps.push (Name.mkSimple s!"_inhab{inhabHyps.size}", fun _ => pure hyp)
          Meta.withLocalDeclsD inhabHyps fun inhabFVars => do
            let fvars := fvars ++ inhabFVars
            let proofExpr ← Elab.Term.elabTermEnsuringType proof (mkConst ``False)
            Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let type ← instantiateMVars (← Meta.mkForallFVars fvars (mkConst ``False))
            let value ← instantiateMVars (← Meta.mkLambdaFVars fvars proofExpr)
            addDecl <| .thmDecl { name := declName, levelParams := [], type := type, value := value }
      Elab.addDeclarationRangesFromSyntax declName stx name
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse tptp' command"
