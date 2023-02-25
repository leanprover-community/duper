import Lean
import Duper.TPTPParser.Hooks

open Lean
open Lean.Parser
open TSyntax.Compat

namespace TPTP

declare_syntax_cat TPTP_file

declare_syntax_cat tff_type
declare_syntax_cat tff_term
declare_syntax_cat tff_atomic_type

syntax tff_arguments := "(" tff_term,* ")"
syntax rawIdent tff_arguments ? : tff_term
syntax:max "(" tff_term ")" : tff_term

syntax prop_binary_connective := "|" <|> "&" <|> "<=>" <|> "=>" <|> "<="
syntax:60 tff_term:60 prop_binary_connective tff_term:60 : tff_term
syntax non_prop_binary_connective := "=" <|> "!="
syntax:65 tff_term:65 non_prop_binary_connective tff_term:65 : tff_term
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
syntax:70 fof_quantifier "[" tff_variable,* "]" ":" tff_term:70 : tff_term

syntax tf1_quantifier := "!>"
syntax tf1_quantifier "[" tff_variable,* "]" ":" tff_type : tff_type --tf1_quantified_type

declare_syntax_cat TPTP_input
syntax "tff" "(" rawIdent "," rawIdent "," tff_term tff_annotation ? ")" "." : TPTP_input
syntax "tff" "(" rawIdent "," &"type" "," rawIdent ":" tff_type tff_annotation ? ")" "." : TPTP_input

syntax "cnf" "(" rawIdent "," rawIdent "," tff_term tff_annotation ? ")" "." : TPTP_input
syntax "fof" "(" rawIdent "," rawIdent "," tff_term tff_annotation ? ")" "." : TPTP_input
syntax "include" "(" sqstr ")" "." : TPTP_input

syntax TPTP_input * : TPTP_file