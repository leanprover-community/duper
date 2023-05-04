import Lean
import Duper.TPTPParser.Hooks

open Lean
open Lean.Parser
open TSyntax.Compat

namespace TPTP

declare_syntax_cat TPTP_file

declare_syntax_cat thf_type
declare_syntax_cat thf_term
declare_syntax_cat thf_atomic_type

syntax thf_arguments := "(" thf_term,* ")"
syntax:120 rawIdent thf_arguments ? : thf_term
syntax:max "(" thf_term ")" : thf_term

-- Higher-order Application
syntax defined_term := "🍉" noWs ident
syntax:max defined_term : thf_term
syntax:60 thf_term:60 "@" thf_term:61 : thf_term
syntax bexpOp := "|" <|> "&" <|> "<=>" <|> "=>" <|> "<=" <|> "<~>" <|> "~|" <|> "~&"
syntax:60 thf_term:60 bexpOp thf_term:61 : thf_term
-- Approximation of `thf_binary_type`
syntax:60 thf_term:61 ">" thf_term:60 : thf_term

-- <infix_equality>       ::= =
-- <infix_inequality>     ::= !=
-- <defined_infix_pred>   ::= <infix_equality>
-- <thf_infix_unary>      ::= <thf_unitary_term> <infix_inequality>
--                            <thf_unitary_term>
-- <thf_defined_infix>    ::= <thf_unitary_term> <defined_infix_pred>
--                            <thf_unitary_term>

syntax eqOp := "=" <|> "!="
syntax:75 thf_term:90 eqOp thf_term:90 : thf_term
syntax:70 "~" thf_term:70 : thf_term

syntax annotation := "," rawIdent

syntax defined_type := "🍉" noWs ident
syntax:max defined_type : thf_atomic_type
syntax rawIdent : thf_atomic_type
syntax thf_atomic_type : thf_type
syntax:max "(" thf_type ")" : thf_type

def thfXProdArgsParser := sepBy1 (categoryParser `thf_atomic_type 0) "*"
syntax thf_xprod_args := thfXProdArgsParser

--thf_mapping_type
/-
  Note: In real TPTP syntax, the below line should be: tff_atomic_type > tff_atomic_type : thf_type.
  However, this is infeasible because Lean's parser can't reliably identify thf_atomic_types due
  to an issue with how Lean's built-in antiquotations and our defined_type category conflict with each
  other. So writing the below syntax is a workaround.
-/
syntax:120 thf_type:121 ">" thf_type:120 : thf_type
syntax "(" thf_xprod_args ")" ">" thf_atomic_type : thf_type

--thf_type_arguments are needed because <type_functor>(<thf_type_arguments>) is a thf_atomic_type
syntax thf_type_arguments := "(" thf_atomic_type,* ")"
syntax rawIdent thf_type_arguments : thf_atomic_type

--thf_apply_type
syntax:130 thf_type:130 "@" thf_type:131 : thf_type

syntax quantifier := "!" <|> "?" <|> "^"
syntax thf_variable := rawIdent (":" thf_type) ?
syntax:70 quantifier "[" thf_variable,* "]" ":" thf_term:70 : thf_term

syntax th1_quantifier := "!>"
syntax th1_quantifier "[" thf_variable,* "]" ":" thf_type : thf_type --tf1_quantified_type

declare_syntax_cat TPTP_input
syntax "tff" "(" rawIdent "," rawIdent "," thf_term annotation ? ")" "." : TPTP_input
syntax "tff" "(" rawIdent "," &"type" "," rawIdent ":" thf_type annotation ? ")" "." : TPTP_input
syntax "thf" "(" rawIdent "," rawIdent "," thf_term annotation ? ")" "." : TPTP_input
syntax "thf" "(" rawIdent "," &"type" "," rawIdent ":" thf_type annotation ? ")" "." : TPTP_input
syntax "cnf" "(" rawIdent "," rawIdent "," thf_term annotation ? ")" "." : TPTP_input
syntax "fof" "(" rawIdent "," rawIdent "," thf_term annotation ? ")" "." : TPTP_input
syntax "include" "(" sqstr ")" "." : TPTP_input

syntax TPTP_input * : TPTP_file