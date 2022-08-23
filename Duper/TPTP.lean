import Lean

namespace TPTP
open Lean
open Lean.Parser
open TSyntax.Compat

declare_syntax_cat TPTP_file

declare_syntax_cat tff_type
declare_syntax_cat tff_term
declare_syntax_cat tff_atomic_type

syntax tff_arguments := "(" tff_term,* ")"
syntax rawIdent tff_arguments ? : tff_term
syntax:max "(" tff_term ")" : tff_term

syntax binary_connective := "|" <|> "&" <|> "<=>" <|> "=>" <|> "<=" <|> "=" <|> "!="
syntax:60 tff_term binary_connective tff_term : tff_term
syntax:70 "~" tff_term:70 : tff_term

syntax tff_annotation := "," rawIdent

syntax defined_type := "$" noWs ident
syntax defined_type : tff_atomic_type
syntax rawIdent : tff_atomic_type
syntax tff_atomic_type : tff_type
syntax:max "(" tff_type ")" : tff_type

def tffXProdArgsParser := sepBy1 (categoryParser `tff_atomic_type 0) "*"
syntax tff_xprod_args := tffXProdArgsParser

--tff_mapping_type
/-
  Note: In real TPTP syntax, the below line should be: tff_atomic_type > tff_atomic_type : tff_type.
  However, this is infeasible because Lean's parser can't reliably identify tff_atomic_types due
  to an issue with how Lean's built-in antiquotations and our defined_type category conflict with each
  other. So writing the below syntax is a workaround.
-/
syntax tff_type ">" tff_type : tff_type
syntax "(" tff_xprod_args ")" ">" tff_atomic_type : tff_type

--tff_type_arguments are needed because <type_functor>(<tff_type_arguments>) is a tff_atomic_type
syntax tff_type_arguments := "(" tff_atomic_type,* ")"
syntax rawIdent tff_type_arguments : tff_atomic_type

syntax fof_quantifier := "!" <|> "?"
syntax tff_variable := rawIdent (":" tff_atomic_type) ?
syntax:70 fof_quantifier "[" tff_variable,* "]" ":" tff_term : tff_term

syntax tf1_quantifier := "!>"
syntax tf1_quantifier "[" tff_variable,* "]" ":" tff_type : tff_type --tf1_quantified_type

declare_syntax_cat TPTP_input
syntax "tff" "(" rawIdent "," rawIdent "," tff_term tff_annotation ? ")" "." : TPTP_input
syntax "tff" "(" rawIdent "," &"type" "," rawIdent ":" tff_type tff_annotation ? ")" "." : TPTP_input

syntax TPTP_input* : TPTP_file

def explicitBinder : Parser := Term.explicitBinder false

axiom iota : Type

def processTffDefinedType (ty : Syntax) : MacroM Syntax := do
  if ty.isAntiquot then
    match ty.getAntiquotTerm.getId with
    | `i => return ← `(TPTP.iota)
    | `o => return ← `(Prop)
    | `tType => return ← `(Type)
    | _ => Macro.throwError s!"Unsupported tff_defined_type: {ty}"
  else Macro.throwError s!"{ty} is not a defined type"

partial def processTffAtomicType (stx : Syntax) : MacroM Syntax := do
  if stx.isAntiquot then processTffDefinedType stx
  else
    match stx with
    | `(tff_type| $ty:tff_atomic_type) => processTffAtomicType ty
    | `(tff_atomic_type| $ty:ident) => pure ty
    | `(tff_atomic_type| $ty:defined_type) => processTffDefinedType ty
    | `(tff_atomic_type| $f:ident $args:tff_type_arguments) => do
      let ts ←
        pure $ ← ((@Syntax.SepArray.mk "," args.raw[1].getArgs) : Array Syntax).mapM
                  fun arg => processTffAtomicType arg
      let ts := mkNode ``many ts
      let ts := mkNode ``Term.app #[f, ts]
      return ← `($ts)
    | _ => Macro.throwError s!"Unsupported tff_atomic_type: {stx}"

partial def processTffTerm (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_term| ( $t:tff_term ) ) => processTffTerm t
  | `(tff_term| ~ $t:tff_term ) =>
    let t ← processTffTerm t
    `(¬ $t)
  | `(tff_term| $t₁:tff_term $conn:binary_connective $t₂:tff_term ) => do
    let t₁ ← processTffTerm t₁
    let t₂ ← processTffTerm t₂
    match conn.raw[0].getKind with
    | `«&» => `($t₁ ∧ $t₂)
    | `«=>» => `($t₁ → $t₂)
    | `«|» => `($t₁ ∨ $t₂)
    | `«=» => `($t₁ = $t₂)
    | `«!=» => `($t₁ ≠ $t₂)
    | `«<=>» => `($t₁ ↔ $t₂)
    | _ => Macro.throwError s!"Unsupported binary_connective: {conn.raw[0].getKind}"
  | `(tff_term| $f:ident $args:tff_arguments ?) => do
    let ts : Array Syntax ← match args with
    | some args =>
      pure $ ← ((@Syntax.SepArray.mk "," args.raw[1].getArgs) : Array Syntax).mapM
                fun arg => processTffTerm arg
    | none => pure #[]
    let ts := mkNode ``many ts
    let ts := mkNode ``Term.app #[f, ts]
    return ← `($ts)
  | `(tff_term| $q:fof_quantifier [ $vs,* ] : $body) => do
    let body ← processTffTerm body
    let vs : Array Syntax := vs
    return ← vs.foldrM
      fun v acc => do
        let (v, ty) ← match v with
        | `(tff_variable| $v:ident) => 
          pure (v, (← `(_) : Syntax))
        | `(tff_variable| $v:ident : $ty:tff_atomic_type) =>
          pure (v, ← processTffAtomicType ty)
        | _ => Macro.throwError s!"Unsupported tff_variable: {v}"
        match q.raw[0].getKind with
        | `«!» => `(∀ ($v : $ty), $acc)
        | `«?» => `(Exists fun ($v : $ty) => $acc)
        | _ => Macro.throwError s!"Unsupported fof_quantifier: {q.raw[0].getKind}"
      body
  | _ => Macro.throwError s!"Unsupported tff_term: {stx}"

partial def processTffType (stx : Syntax) : MacroM Syntax := do
  if stx.isAntiquot then processTffAtomicType stx
  else
    match stx with
    | `(tff_type| ( $t:tff_type ) ) => processTffType t
    | `(tff_type| $ty:tff_atomic_type) =>
      processTffAtomicType ty
    | `(tff_type| $arg:tff_type > $ret:tff_type) =>
      -- Although the current parser syntax has tff_type > tff_type, this pattern should
      -- only appear in TPTP files when both arg and ret are of the category tff_atomic_type
      let ret ← processTffAtomicType ret
      let arg ← processTffAtomicType arg
      return ← `($arg → $ret)
    | `(tff_type| ( $args:tff_xprod_args ) > $ret:tff_atomic_type) =>
      let ret ← processTffAtomicType ret
      let args : Array Syntax := @Syntax.SepArray.mk "*" args.raw[0].getArgs
      let stx ← args.foldrM (fun (a acc : Syntax) => do
        let a ← processTffAtomicType a
        `($a → $acc)) ret
      return stx
    | `(tff_type| $q:tf1_quantifier [ $vs,* ] : $ty) =>
      let ty ← processTffType ty
      let vs : Array Syntax := vs
      return ← vs.foldrM
        fun v acc => do
          let (v, v_ty) ← match v with
          | `(tff_variable| $v:ident) =>
            pure (v, (← `(_) : Syntax))
          | `(tff_variable| $v:ident : $v_ty:tff_atomic_type) =>
            pure (v, ← processTffAtomicType v_ty)
          | _ => Macro.throwError s!"Unsupported tff_variable: {v} when trying to process a tf1_quantified_type"
          match q.raw[0].getKind with
          | `«!>» => `(∀ ($v : $v_ty), $acc)
          | _ => Macro.throwError s!"Unsupported tf1_quantifier: {q.raw[0].getKind}"
        ty
    | _ => Macro.throwError s!"Unsupported tff_type: {stx}"

macro "BEGIN_TPTP" name:ident s:TPTP_file "END_TPTP" proof:term : command => do
  let hyps ← s.raw[0].getArgs.mapM fun input => do
    match input with
    | `(TPTP_input| tff($name:ident,$role,$term:tff_term $annotation:tff_annotation ?).) =>
      let term ← processTffTerm term
      let name := (mkIdent $ name.getId.appendBefore "h")
      if role.getId == `conjecture then
        return ← `(explicitBinder| ($name : ¬ $term))
      else
        return ← `(explicitBinder| ($name : $term))
    | `(TPTP_input| tff($n:ident,type,$name:ident : $ty:tff_type $annotation:tff_annotation ?).) =>
      let ty ← processTffType ty
      return ← `(explicitBinder| ($name : $ty))
    | _ => Macro.throwError s!"Unsupported TPTP_input: {input}"
  let hyps := mkNode ``many hyps
  let spec ← `(Term.typeSpec| : False)
  let sig := mkNode ``Command.declSig #[hyps,spec]
  return ← `(theorem $name $sig := $proof)

open Lean.Elab.Command

partial def parseMyType (s : String) : CommandElabM Syntax := do
  match runParserCategory (← getEnv) `TPTP_file s with
  | Except.error e => throwError e
  | Except.ok r => return r

def loadTptp (path : System.FilePath) : CommandElabM Syntax := do
  let lines ← IO.FS.lines path
  let lines := lines.filter fun l => ¬ l.startsWith "%"
  let s := String.join lines.toList
  parseMyType s

syntax (name := tptpKind) "tptp " ident strLit term : command

@[commandElab tptpKind] def elabResolve : CommandElab := fun stx => do
  match stx with
  | `(tptp $name $file $proof) =>
    match Syntax.isStrLit? file with
    | some file =>
        let fstx ← loadTptp file
        elabCommand (← `(BEGIN_TPTP $name $fstx END_TPTP $proof))
    | _ => throwError "Expected strLit: {file}"
  | _ => throwError "Failed to parse tptp command"