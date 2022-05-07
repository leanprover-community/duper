import Lean

namespace TPTP
open Lean.Parser

----v8.0.0.0 (TPTP version.internal development number)

----Files. Empty file is OK.
declare_syntax_cat TPTP_file
declare_syntax_cat TPTP_input

----Formula records
declare_syntax_cat annotated_formula
----Future languages may include ...  english | efof | tfof | mathml | ...
declare_syntax_cat tpi_annotated
declare_syntax_cat tpi_formula
declare_syntax_cat thf_annotated
declare_syntax_cat tff_annotated
declare_syntax_cat tcf_annotated
declare_syntax_cat fof_annotated
declare_syntax_cat cnf_annotated
declare_syntax_cat annotations

----Types for problems.
declare_syntax_cat formula_role
----THF formulae.
declare_syntax_cat thf_formula
declare_syntax_cat thf_logic_formula
declare_syntax_cat thf_binary_formula
----There's no precedence among binary connectives
declare_syntax_cat thf_binary_nonassoc
declare_syntax_cat thf_binary_assoc
declare_syntax_cat thf_or_formula
declare_syntax_cat thf_and_formula
declare_syntax_cat thf_apply_formula
declare_syntax_cat thf_unit_formula
declare_syntax_cat thf_preunit_formula
declare_syntax_cat thf_unitary_formula
----All variables must be quantified
declare_syntax_cat thf_quantified_formula
declare_syntax_cat thf_quantification
declare_syntax_cat thf_variable_list
declare_syntax_cat thf_typed_variable
declare_syntax_cat thf_unary_formula
declare_syntax_cat thf_prefix_unary
declare_syntax_cat thf_infix_unary
declare_syntax_cat thf_atomic_formula
declare_syntax_cat thf_plain_atomic
declare_syntax_cat thf_defined_atomic
declare_syntax_cat thf_defined_term
declare_syntax_cat thf_defined_infix
declare_syntax_cat thf_system_atomic

declare_syntax_cat thf_let
declare_syntax_cat thf_let_types
declare_syntax_cat thf_atom_typing_list
declare_syntax_cat thf_let_defns
declare_syntax_cat thf_let_defn
declare_syntax_cat thf_let_defn_list

declare_syntax_cat thf_unitary_term
declare_syntax_cat thf_conn_term
declare_syntax_cat thf_tuple

----Allows first-order style in THF.
declare_syntax_cat thf_fof_function
----Arguments recurse back up to formulae (this is the THF world here)
declare_syntax_cat thf_arguments

declare_syntax_cat thf_formula_list

declare_syntax_cat thf_atom_typing
declare_syntax_cat thf_top_level_type
declare_syntax_cat thf_unitary_type
declare_syntax_cat thf_atomic_type
declare_syntax_cat th1_quantified_type

declare_syntax_cat thf_apply_type
declare_syntax_cat thf_binary_type
declare_syntax_cat thf_mapping_type
declare_syntax_cat thf_xprod_type
declare_syntax_cat thf_union_type
declare_syntax_cat thf_subtype

declare_syntax_cat thf_definition
declare_syntax_cat thf_sequent

----TFF formulae.
declare_syntax_cat tff_formula
declare_syntax_cat tff_logic_formula

declare_syntax_cat tff_binary_formula
declare_syntax_cat tff_binary_nonassoc
declare_syntax_cat tff_binary_assoc
declare_syntax_cat tff_or_formula
declare_syntax_cat tff_and_formula
declare_syntax_cat tff_unit_formula
declare_syntax_cat tff_preunit_formula
declare_syntax_cat tff_unitary_formula
declare_syntax_cat tfx_unitary_formula
declare_syntax_cat tff_quantified_formula

declare_syntax_cat tff_variable_list
declare_syntax_cat tff_variable
declare_syntax_cat tff_typed_variable
declare_syntax_cat tff_unary_formula
declare_syntax_cat tff_prefix_unary
declare_syntax_cat tff_infix_unary

declare_syntax_cat tff_atomic_formula
declare_syntax_cat tff_plain_atomic
declare_syntax_cat tff_defined_atomic
declare_syntax_cat tff_defined_plain
declare_syntax_cat tff_defined_infix
declare_syntax_cat tff_system_atomic
declare_syntax_cat tfx_conditional
declare_syntax_cat tfx_let
declare_syntax_cat tfx_let_types
declare_syntax_cat tff_atom_typing_list
declare_syntax_cat tfx_let_defns
declare_syntax_cat tfx_let_defn
declare_syntax_cat tfx_let_LHS
declare_syntax_cat tfx_let_defn_list
declare_syntax_cat tfx_tnc_atom

declare_syntax_cat tff_term
declare_syntax_cat tff_unitary_term
declare_syntax_cat tfx_tuple

declare_syntax_cat tff_arguments

declare_syntax_cat tff_atom_typing
declare_syntax_cat tff_top_level_type
declare_syntax_cat tff_non_atomic_type
declare_syntax_cat tf1_quantified_type
declare_syntax_cat tff_monotype
declare_syntax_cat tff_unitary_type
declare_syntax_cat tff_atomic_type
declare_syntax_cat tff_type_arguments
declare_syntax_cat tff_mapping_type
declare_syntax_cat tff_xprod_type
----For TFX only
declare_syntax_cat tfx_tuple_type
declare_syntax_cat tff_type_list

declare_syntax_cat tff_subtype

declare_syntax_cat tfx_definition
declare_syntax_cat tfx_sequent

----Typed non-classical here
declare_syntax_cat tnc_connective
declare_syntax_cat tnc_short_connective
declare_syntax_cat tnc_long_connective
declare_syntax_cat tnc_connective_name
declare_syntax_cat tnc_parameter_list
declare_syntax_cat tnc_parameter
declare_syntax_cat tnc_index
declare_syntax_cat tnc_key_pair

----Non-classical logic semantic specifications. Currently not linked in.
declare_syntax_cat logic_defn_rule
declare_syntax_cat logic_defn_LHS
declare_syntax_cat logic_defn_RHS

----TCF formulae.
declare_syntax_cat tcf_formula
declare_syntax_cat tcf_logic_formula
declare_syntax_cat tcf_quantified_formula

----FOF formulae.
declare_syntax_cat fof_formula
declare_syntax_cat fof_logic_formula
declare_syntax_cat fof_binary_formula
declare_syntax_cat fof_binary_nonassoc
declare_syntax_cat fof_binary_assoc
declare_syntax_cat fof_or_formula
declare_syntax_cat fof_and_formula
declare_syntax_cat fof_unary_formula
declare_syntax_cat fof_infix_unary
declare_syntax_cat fof_unit_formula
declare_syntax_cat fof_unitary_formula
declare_syntax_cat fof_quantified_formula
declare_syntax_cat fof_variable_list
declare_syntax_cat fof_atomic_formula
declare_syntax_cat fof_plain_atomic_formula
declare_syntax_cat fof_defined_atomic_formula
declare_syntax_cat fof_defined_plain_formula
declare_syntax_cat fof_defined_infix_formula
declare_syntax_cat fof_system_atomic_formula

----FOF terms.
declare_syntax_cat fof_plain_term
declare_syntax_cat fof_defined_term
declare_syntax_cat fof_defined_atomic_term
declare_syntax_cat fof_defined_plain_term
declare_syntax_cat fof_system_term
declare_syntax_cat fof_arguments
declare_syntax_cat fof_term
declare_syntax_cat fof_function_term

----This section is the FOFX syntax. Not yet in use.
declare_syntax_cat fof_sequent

declare_syntax_cat fof_formula_tuple
declare_syntax_cat fof_formula_tuple_list

----CNF formulae (variables implicitly universally quantified)
declare_syntax_cat cnf_formula
declare_syntax_cat disjunction
declare_syntax_cat literal

----Connectives - THF
declare_syntax_cat thf_quantifier
declare_syntax_cat th1_quantifier
declare_syntax_cat th0_quantifier
declare_syntax_cat subtype_sign
declare_syntax_cat fof_quantifier
declare_syntax_cat nonassoc_connective
declare_syntax_cat assoc_connective
declare_syntax_cat unary_connective
declare_syntax_cat gentzen_arrow
declare_syntax_cat assignment
declare_syntax_cat identical

----Types for THF and TFF
declare_syntax_cat type_constant
declare_syntax_cat type_functor
declare_syntax_cat defined_type
declare_syntax_cat system_type

----For all language types
declare_syntax_cat atom
declare_syntax_cat untyped_atom

declare_syntax_cat proposition
declare_syntax_cat predicate
declare_syntax_cat defined_proposition
declare_syntax_cat defined_predicate
declare_syntax_cat defined_infix_pred
declare_syntax_cat system_proposition
declare_syntax_cat system_predicate
declare_syntax_cat infix_equality
declare_syntax_cat infix_inequality

declare_syntax_cat «constant»
declare_syntax_cat functor
declare_syntax_cat defined_constant
declare_syntax_cat defined_functor
declare_syntax_cat system_constant
declare_syntax_cat system_functor
declare_syntax_cat def_or_sys_constant
declare_syntax_cat th1_defined_term
declare_syntax_cat defined_term
declare_syntax_cat «variable»

----Formula sources
declare_syntax_cat source
declare_syntax_cat sources
declare_syntax_cat dag_source
declare_syntax_cat inference_record
declare_syntax_cat inference_rule
declare_syntax_cat inference_parents
declare_syntax_cat parent_list
declare_syntax_cat parent_info
declare_syntax_cat parent_details
declare_syntax_cat internal_source
declare_syntax_cat intro_type
declare_syntax_cat external_source
declare_syntax_cat file_source
declare_syntax_cat file_info
declare_syntax_cat theory
declare_syntax_cat theory_name
declare_syntax_cat creator_source
declare_syntax_cat creator_name

----Useful info fields
declare_syntax_cat optional_info
declare_syntax_cat useful_info
declare_syntax_cat info_items
declare_syntax_cat info_item
----Useful info for formula records
declare_syntax_cat formula_item
declare_syntax_cat description_item
declare_syntax_cat iquote_item
declare_syntax_cat inference_item
declare_syntax_cat inference_status
declare_syntax_cat status_value
declare_syntax_cat inference_info
declare_syntax_cat assumptions_record
declare_syntax_cat refutation
declare_syntax_cat new_symbol_record
declare_syntax_cat new_symbol_list
declare_syntax_cat principal_symbol

----Include directives
declare_syntax_cat include
declare_syntax_cat formula_selection
declare_syntax_cat name_list

----Non-logical data
declare_syntax_cat general_term
declare_syntax_cat general_data
declare_syntax_cat general_function
declare_syntax_cat bound_type
declare_syntax_cat formula_data
declare_syntax_cat general_list
declare_syntax_cat general_terms

----General purpose
declare_syntax_cat name
declare_syntax_cat atomic_word
declare_syntax_cat atomic_defined_word
declare_syntax_cat atomic_system_word
declare_syntax_cat number
declare_syntax_cat file_name
declare_syntax_cat null
declare_syntax_cat comment
declare_syntax_cat comment_line
declare_syntax_cat comment_block
declare_syntax_cat not_star_slash

declare_syntax_cat single_quoted

declare_syntax_cat distinct_object
----Space and visible characters upto ~, except " and \
declare_syntax_cat dollar_word
declare_syntax_cat dollar_dollar_word
declare_syntax_cat upper_word
declare_syntax_cat lower_word

----Tokens used in syntax, and cannot be character classes
declare_syntax_cat vline
declare_syntax_cat star
declare_syntax_cat plus
declare_syntax_cat arrow
declare_syntax_cat less_sign
declare_syntax_cat hash

----Numbers. Signs are made part of the same token here.
declare_syntax_cat real
declare_syntax_cat signed_real
declare_syntax_cat unsigned_real
declare_syntax_cat rational
declare_syntax_cat signed_rational
declare_syntax_cat unsigned_rational
declare_syntax_cat integer
declare_syntax_cat signed_integer
declare_syntax_cat unsigned_integer
declare_syntax_cat decimal
declare_syntax_cat positive_decimal
declare_syntax_cat decimal_exponent
declare_syntax_cat decimal_fraction
declare_syntax_cat dot_decimal
declare_syntax_cat exp_integer
declare_syntax_cat signed_exp_integer
declare_syntax_cat unsigned_exp_integer

declare_syntax_cat slash
declare_syntax_cat slosh

----Character classes
declare_syntax_cat percentage_sign
declare_syntax_cat double_quote
declare_syntax_cat do_char
declare_syntax_cat single_quote
----Space and visible characters upto ~, except ' and \
declare_syntax_cat sq_char
declare_syntax_cat sign
declare_syntax_cat dot
declare_syntax_cat exponent
declare_syntax_cat slash_char
declare_syntax_cat slosh_char
declare_syntax_cat zero_numeric
declare_syntax_cat non_zero_numeric
declare_syntax_cat numeric
declare_syntax_cat lower_alpha
declare_syntax_cat upper_alpha
declare_syntax_cat alpha_numeric
declare_syntax_cat dollar
declare_syntax_cat printable_char
declare_syntax_cat viewable_char
 

----Files. Empty file is OK.
syntax TPTP_input* : TPTP_file
syntax annotated_formula : TPTP_input
syntax include : TPTP_input
 
----Formula records
syntax thf_annotated : annotated_formula
syntax tff_annotated : annotated_formula
syntax tcf_annotated : annotated_formula
syntax fof_annotated : annotated_formula
syntax cnf_annotated : annotated_formula
syntax tpi_annotated : annotated_formula
----Future languages may include ...  english | efof | tfof | mathml | ...
syntax (name := tpi) "tpi" "(" name "," formula_role "," tpi_formula annotations ")" "." : tpi_annotated
syntax fof_formula : tpi_formula
syntax "thf" "(" name "," formula_role "," thf_formula annotations ")" "." : thf_annotated
syntax (name := tff) "tff" "(" name "," formula_role "," tff_formula annotations ")" "." : tff_annotated
syntax (name := tcf) "tcf" "(" name "," formula_role "," tcf_formula annotations ")" "." : tcf_annotated
syntax (name := fof) "fof" "(" name "," formula_role "," fof_formula annotations ")" "." : fof_annotated
syntax (name := cnf) "cnf" "(" name "," formula_role "," cnf_formula annotations "." : cnf_annotated
syntax "," source optional_info : annotations
syntax null : annotations

----Types for problems.
syntax lower_word : formula_role
syntax lower_word "-" general_term : formula_role

----TFF formulae.
syntax tff_logic_formula : tff_formula
syntax tff_atom_typing : tff_formula
syntax tff_subtype : tff_formula
syntax tff_unitary_formula : tff_logic_formula
syntax tff_unary_formula : tff_logic_formula
syntax tff_binary_formula : tff_logic_formula
syntax tff_defined_infix : tff_logic_formula
syntax tfx_definition : tff_logic_formula
syntax tfx_sequent : tff_logic_formula
----tff_defined_infix up here to avoid confusion in a = b | p, for TFX.
----For plain TFF it can be in tff_defined_atomic

syntax tff_binary_nonassoc : tff_binary_formula
syntax tff_binary_assoc : tff_binary_formula
syntax tff_unit_formula nonassoc_connective tff_unit_formula : tff_binary_nonassoc
syntax tff_or_formula : tff_binary_assoc
syntax tff_and_formula : tff_binary_assoc
syntax tff_unit_formula vline tff_unit_formula : tff_binary_assoc
syntax tff_or_formula vline tff_unit_formula : tff_or_formula
syntax tff_unit_formula "&" tff_unit_formula : tff_and_formula
syntax tff_and_formula "&" tff_unit_formula : tff_and_formula
syntax tff_unitary_formula : tff_unit_formula
syntax tff_unary_formula : tff_unit_formula
syntax tff_defined_infix : tff_unit_formula
syntax tff_unitary_formula : tff_preunit_formula
syntax tff_prefix_unary : tff_preunit_formula
syntax tff_quantified_formula : tff_unitary_formula
syntax tff_atomic_formula : tff_unitary_formula
syntax tfx_unitary_formula : tff_unitary_formula
syntax "(" tff_logic_formula ")" : tff_unitary_formula
syntax «variable» : tfx_unitary_formula
syntax fof_quantifier "[" tff_variable_list "]" ":" tff_unit_formula : tff_quantified_formula
----Quantified formulae bind tightly, so cannot include infix formulae

syntax tff_variable : tff_variable_list
syntax tff_variable "," tff_variable_list : tff_variable_list
syntax tff_typed_variable : tff_variable 
syntax «variable» : tff_variable
syntax «variable» ":" tff_atomic_type : tff_typed_variable
syntax tff_prefix_unary : tff_unary_formula
syntax tff_infix_unary : tff_unary_formula
--FOR PLAIN TFF fof_infix_unary
syntax unary_connective tff_preunit_formula : tff_prefix_unary
syntax tff_unitary_term infix_inequality tff_unitary_term : tff_infix_unary

-- %FOR PLAIN TFF tff_atomic_formula   ::= fof_atomic_formula
syntax tff_plain_atomic : tff_atomic_formula
syntax tff_defined_atomic : tff_atomic_formula
syntax tff_system_atomic : tff_atomic_formula
syntax «constant» : tff_plain_atomic
syntax functor "(" tff_arguments ")" : tff_plain_atomic
----tnc_connective allowed as formulae for logic specifications
syntax tff_defined_plain : tff_defined_atomic
syntax tnc_connective : tff_defined_atomic
---To avoid confusion in TFX mode a = b | p   | tff_defined_infix
syntax defined_constant : tff_defined_plain
syntax defined_functor "(" tff_arguments ")" : tff_defined_plain
syntax tfx_tnc_atom : tff_defined_plain
syntax tfx_let : tff_defined_plain
-- % tfx_conditional 
----tfx_conditional is omitted from tff_defined_plain because $ite is
----read simply as a tff_atomic_formula
syntax defined_proposition : tff_defined_plain
syntax defined_predicate "(" tff_arguments ")" : tff_defined_plain
syntax tfx_conditional : tff_defined_plain
syntax tfx_let : tff_defined_plain
-- syntax tfx_tnc : tff_defined_plain
----This is the only one that is strictly a formula, type $o. In TFX, if the
----LHS/RHS is a formula that does not look like a term, then it must be ()ed
----per tff_unitary_term. If you put an un()ed formula that looks like a term
----it will be interpreted as a term.
syntax tff_unitary_term defined_infix_pred tff_unitary_term : tff_defined_infix
syntax system_constant : tff_system_atomic
syntax system_functor "(" tff_arguments ")" : tff_system_atomic
-- syntax system_proposition : tff_system_atomic
--                            system_predicate(tff_arguments)
----tfx_conditional is written and read as a tff_defined_atomic
syntax "$ite" "(" tff_logic_formula "," tff_term "," tff_term ")" : tfx_conditional
syntax "$let" "(" tfx_let_types "," tfx_let_defns "," tff_term ")" : tfx_let
syntax tff_atom_typing : tfx_let_types
syntax "[" tff_atom_typing_list "]" : tfx_let_types
syntax tff_atom_typing : tff_atom_typing_list
syntax tff_atom_typing "," tff_atom_typing_list : tff_atom_typing_list
syntax tfx_let_defn : tfx_let_defns
syntax "[" tfx_let_defn_list "]" : tfx_let_defns
syntax tfx_let_LHS assignment tff_term : tfx_let_defn
syntax tff_plain_atomic : tfx_let_LHS
syntax tfx_tuple : tfx_let_LHS
syntax tfx_let_defn : tfx_let_defn_list
syntax tfx_let_defn "," tfx_let_defn_list : tfx_let_defn_list
syntax tnc_connective "(" tff_arguments ")" : tfx_tnc_atom

syntax tff_logic_formula : tff_term
syntax defined_term : tff_term
syntax tfx_tuple : tff_term
syntax tnc_key_pair : tff_term
syntax tff_atomic_formula : tff_unitary_term
syntax defined_term : tff_unitary_term
syntax tfx_tuple : tff_unitary_term
syntax «variable» : tff_unitary_term
syntax "(" tff_logic_formula ")" : tff_unitary_term
syntax "[]" : tfx_tuple
syntax "[" tff_arguments "]" : tfx_tuple

syntax tff_term : tff_arguments
syntax tff_term "," tff_arguments : tff_arguments

----tff_atom_typing can appear only at top level.
syntax untyped_atom ":" tff_top_level_type : tff_atom_typing
syntax "(" tff_atom_typing ")" : tff_atom_typing
syntax tff_atomic_type : tff_top_level_type
syntax tff_non_atomic_type : tff_top_level_type
syntax tff_mapping_type : tff_non_atomic_type
syntax tf1_quantified_type : tff_non_atomic_type
syntax "(" tff_non_atomic_type ")" : tff_non_atomic_type
syntax "!>" "[" tff_variable_list "]" ":" tff_monotype : tf1_quantified_type
syntax tff_atomic_type : tff_monotype
syntax "(" tff_mapping_type ")" : tff_monotype
syntax tf1_quantified_type : tff_monotype
syntax tff_atomic_type : tff_unitary_type
syntax "(" tff_xprod_type ")" : tff_unitary_type
syntax type_constant : tff_atomic_type
syntax defined_type : tff_atomic_type
syntax «variable» : tff_atomic_type
syntax type_functor "(" tff_type_arguments ")" : tff_atomic_type
syntax "(" tff_atomic_type ")" : tff_atomic_type
syntax tfx_tuple_type : tff_atomic_type
syntax tff_atomic_type : tff_type_arguments
syntax tff_atomic_type "," tff_type_arguments : tff_type_arguments
syntax tff_unitary_type arrow tff_atomic_type : tff_mapping_type
syntax tff_unitary_type star tff_atomic_type : tff_xprod_type
syntax tff_xprod_type star tff_atomic_type : tff_xprod_type

----Connectives - THF
syntax fof_quantifier : thf_quantifier
syntax th0_quantifier : thf_quantifier
syntax th1_quantifier : thf_quantifier
----TH0 quantifiers are also available in TH1
syntax "!>" : th1_quantifier 
syntax "?*" : th1_quantifier
syntax "^" : th0_quantifier
syntax "@+" : th0_quantifier
syntax "@-" : th0_quantifier
----Connectives - THF and TFF
syntax "<<" : subtype_sign
----Connectives - TFF
----Connectives - FOF
syntax "!" : fof_quantifier
syntax "?" : fof_quantifier
syntax "<=>" : nonassoc_connective
syntax "=>" : nonassoc_connective
syntax "<=" : nonassoc_connective
syntax "<~>" : nonassoc_connective
syntax "~" vline : nonassoc_connective
syntax "~&" : nonassoc_connective
syntax vline : nonassoc_connective
syntax "&" : nonassoc_connective
syntax "~" : unary_connective
----The seqent arrow
syntax "-->" : gentzen_arrow
syntax ":=" : assignment
syntax "==" : identical

----Types for THF and TFF
syntax type_functor : type_constant
syntax atomic_word : type_functor
syntax atomic_defined_word : defined_type
syntax "$oType" : defined_type
syntax "$o" : defined_type
syntax "$iType" : defined_type
syntax "$i" : defined_type 
syntax "$tType" : defined_type
syntax "$real" : defined_type
syntax "$rat" : defined_type
syntax "$int" : defined_type
----$oType/$o is the Boolean type, i.e., the type of $true and $false.
----$iType/$i is non-empty type of individuals, which may be finite or
----infinite. $tType is the type of all types. $real is the type of <real>s.
----$rat is the type of <rational>s. $int is the type of <signed_integer>s
----and <unsigned_integer>s.
syntax atomic_system_word : system_type

----For all language types
syntax untyped_atom : atom
syntax defined_constant : atom
syntax «constant» : untyped_atom
syntax system_constant : untyped_atom

syntax predicate : proposition
syntax (name := predicate) atomic_word : predicate
syntax defined_predicate : defined_proposition
syntax "$true" : defined_proposition
syntax "$false" : defined_proposition
syntax atomic_defined_word : defined_predicate
syntax "$distinct" : defined_predicate
syntax "$less" : defined_predicate
syntax "$lesseq" : defined_predicate
syntax "$greater" : defined_predicate
syntax "$greatereq" : defined_predicate
syntax "$is_int" : defined_predicate
syntax "$is_rat" : defined_predicate
syntax "$box_P" : defined_predicate
syntax "$box_i" : defined_predicate
syntax "$box_int" : defined_predicate
syntax "$box" : defined_predicate
syntax "$dia_P" : defined_predicate
syntax "$dia_i" : defined_predicate
syntax "$dia_int" : defined_predicate
syntax "$dia" : defined_predicate
----$distinct means that each of it's constant arguments are pairwise !=. It
----is part of the TFF syntax. It can be used only as a fact in an axiom (not
----a conjecture), and not under any connective.
syntax infix_equality : defined_infix_pred
syntax system_predicate : system_proposition
syntax atomic_system_word : system_predicate
syntax "=" : infix_equality
syntax "!=" : infix_inequality

syntax functor : «constant»
syntax atomic_word : functor
syntax defined_functor : defined_constant
syntax atomic_defined_word : defined_functor
syntax "$uminus" : defined_functor
syntax "$sum" : defined_functor
syntax "$difference" : defined_functor
syntax "$product" : defined_functor
syntax "$quotient" : defined_functor
syntax "$quotient_e" : defined_functor
syntax "$quotient_t" : defined_functor
syntax "$quotient_f" : defined_functor
syntax "$remainder_e" : defined_functor
syntax "$remainder_t" : defined_functor
syntax "$remainder_f" : defined_functor
syntax "$floor" : defined_functor
syntax "$ceiling" : defined_functor
syntax "$truncate" : defined_functor
syntax "$round" : defined_functor
syntax "$to_int" : defined_functor
syntax "$to_rat" : defined_functor
syntax "$to_real" : defined_functor
syntax system_functor : system_constant
syntax atomic_system_word : system_functor
syntax defined_constant : def_or_sys_constant
syntax system_constant : def_or_sys_constant
syntax "!!" : th1_defined_term
syntax "??" : th1_defined_term
syntax "@@+" : th1_defined_term
syntax "@@-" : th1_defined_term
syntax "@=" : th1_defined_term
syntax number : defined_term
syntax distinct_object : defined_term
syntax upper_word : «variable»


----General purpose
-- syntax atomic_word : name
syntax integer : name
----Integer names are expected to be unsigned
syntax lower_word : atomic_word
syntax single_quoted : atomic_word
----<single_quoted> tokens do not include their outer quotes, therefore the
----<lower_word> <atomic_word> cat and the <single_quoted> <atomic_word> 'cat'
----are the same. Quotes must be removed from a <single_quoted> <atomic_word>
----if doing so produces a <lower_word> <atomic_word>. Note that <numbers>s
----and <variable>s are not <lower_word>s, so '123' and 123, and 'X' and X,
----are different.
syntax dollar_word : atomic_defined_word
syntax dollar_dollar_word : atomic_system_word
syntax integer : number
syntax rational : number
syntax real : number
----Numbers are always interpreted as themselves, and are thus implicitly
----distinct if they have different values, e.g., 1 != 2 is an implicit axiom.
----All numbers are base 10 at the moment.
syntax single_quoted : file_name
syntax skip : null

syntax ident : upper_word
syntax ident : name
syntax ident : lower_word
syntax &"axiom" : lower_word
syntax ">" : arrow
syntax "*" : star
syntax "|" : vline

open Lean
open Lean.Parser

#check Syntax

def explicitBinder : Parser := Term.explicitBinder false

partial def processTffTerm (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_term| $c:ident) => return c
  | `(tff_term| $f:functor ( $args )) => do
    let f ← match f with
    | `(functor| $f:ident) => pure f
    | _ => Macro.throwError s!"Unsupported functor: {f}"
    let ts ← match args with
    | `(tff_arguments| $t:tff_term) =>
      let t ← processTffTerm t
      pure #[t]
    | _ => Macro.throwError s!"Unsupported tff_arguments: {args}"
    let ts := mkNode ``many ts
    let ts := mkNode ``Term.app #[f, ts]
    return ← `($ts)
  | _ => Macro.throwError s!"Unsupported tff_term: {stx}"

#check Term.app

def processTffFormula (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_formula| $p:ident) => return p
  | `(tff_formula| $p:functor ( $args )) => 
    let p ← match p with
    | `(functor| $p:ident) => pure p
    | _ => Macro.throwError s!"Unsupported predicate: {p}"
    let ts ← match args with
    | `(tff_arguments| $t:tff_term) =>
      let t ← processTffTerm t
      pure #[t]
    | _ => Macro.throwError s!"Unsupported tff_arguments: {args}"
    let ts := mkNode ``many ts
    let ts := mkNode ``Term.app #[p, ts]
    return ← `($ts)
  | _ => Macro.throwError s!"Unsupported tff_formula: {stx}"

constant iota : Type

def processTffAtomicType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_atomic_type| $ty:defined_type) =>
    match ty[0].getKind with
    | `«$tType» => return ← `(Type)
    | `«$o» => return ← `(Prop)
    | `«$i» => return ← `(TPTP.iota)
    | _ => Macro.throwError s!"Unsupported defined_type: {ty[0].getKind.toString}"
  | `(tff_atomic_type| $ty:ident) => `($ty)
  | _ => Macro.throwError s!"Unsupported tff_atomic_type: {stx}"

mutual
partial def processTffXProdType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_xprod_type| $ty₁:tff_xprod_type * $ty₂:tff_atomic_type) =>
    let ty₁ ← processTffXProdType ty₁
    let ty₂ ← processTffAtomicType ty₂
    return ← `($ty₁ × $ty₂)
  | `(tff_xprod_type| $ty₁:tff_unitary_type * $ty₂:tff_atomic_type) =>
    let ty₁ ← processTffUnitaryType ty₁
    let ty₂ ← processTffAtomicType ty₂
    return ← `($ty₁ × $ty₂)
  | _ => Macro.throwError s!"Unsupported tff_xprod_type: {stx}"

partial def processTffUnitaryType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_unitary_type| $ty:tff_atomic_type) =>
    processTffAtomicType ty
  | `(tff_unitary_type| ($ty:tff_xprod_type)) =>
    processTffXProdType ty
  | _ => Macro.throwError s!"Unsupported tff_unitary_type: {stx}"
end

def processTffTopLevelType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_top_level_type| $ty:tff_atomic_type) =>
    processTffAtomicType ty
  | `(tff_top_level_type| $ty₁:tff_unitary_type > $ty₂:tff_atomic_type) =>
    let ty₁ ← processTffUnitaryType ty₁
    let ty₂ ← processTffAtomicType ty₂
    return ← `($ty₁ → $ty₂)
  | _ => Macro.throwError s!"Unsupported tff_top_level_type: {stx}"

macro "BEGIN_TPTP" name:ident s:TPTP_file "END_TPTP" proof:term : command => do
  let hyps ← s[0].getArgs.mapM fun input => do
    match input with
    | `(TPTP_input| tff($n, type, $name:untyped_atom : $ty:tff_top_level_type ).) =>
      let ty ← processTffTopLevelType ty
      let name ← match name with
      | `(untyped_atom| $name:ident) => pure name
      | _ => Macro.throwError s!"Unsupported name: {name}"
      return ← `(explicitBinder| ($name : $ty))
    | `(TPTP_input| tff($name:name,$role,$formula:tff_formula $ann).) =>
      let formula ← processTffFormula formula
      let name ← match name with
      | `(name| $name:ident) => pure name
      | _ => Macro.throwError s!"Unsupported name: {name}"
      return ← `(explicitBinder| ($name : $formula))
    | _ => Macro.throwError s!"Unsupported TPTP_input: {input}"
  let hyps := mkNode ``many hyps
  let spec ← `(Term.typeSpec| : False)
  let sig := mkNode ``Command.declSig #[hyps,spec]
  return ← `(theorem $name $sig := $proof)

BEGIN_TPTP my_problem
tff(wolf_type, type, wolf: $tType ).
tff(q_type, type, q: $o ).
tff(c_type, type, c: $i ).
tff(c_type, type, p: $i > $o).
tff(c_type, type, f: $i > $i).

tff(eats_type,type,
    eats: ( animal * edible ) > $o ).
tff(x,axiom,p(f(f(c)))).
-- tff(pel47_7,axiom,
--     ! [X: animal] :
--       ( ! [Y: plant] : eats(X,plant_to_edible(Y))
--       | ! [Y1: animal] :
--           q ) ).

END_TPTP
sorry


-- BEGIN_TPTP my_problem
-- tff(animal_type,type,
--     animal: $tType ).

-- tff(wolf_type,type,
--     wolf: $tType ).

-- tff(wolf_is_animal,type,
--     wolf_to_animal: wolf > animal ).

-- tff(fox_type,type,
--     fox: $tType ).

-- tff(fox_is_animal,type,
--     fox_to_animal: fox > animal ).

-- tff(bird_type,type,
--     bird: $tType ).

-- tff(bird_is_animal,type,
--     bird_to_animal: bird > animal ).

-- tff(caterpillar_type,type,
--     caterpillar: $tType ).

-- tff(caterpillar_is_animal,type,
--     caterpillar_to_animal: caterpillar > animal ).

-- tff(snail_type,type,
--     snail: $tType ).

-- tff(snail_is_animal,type,
--     snail_to_animal: snail > animal ).

-- tff(plant_type,type,
--     plant: $tType ).

-- tff(grain_type,type,
--     grain: $tType ).

-- tff(grain_is_plant,type,
--     grain_to_plant: grain > plant ).

-- tff(edible_type,type,
--     edible: $tType ).

-- tff(animal_is_edible,type,
--     animal_to_edible: animal > edible ).

-- tff(plant_is_edible,type,
--     plant_to_edible: plant > edible ).

-- tff(eats_type,type,
--     eats: ( animal * edible ) > $o ).

-- tff(much_smaller_type,type,
--     much_smaller: ( animal * animal ) > $o ).

-- tff(pel47_7,axiom,
--     ! [X: animal] :
--       ( ! [Y: plant] : eats(X,plant_to_edible(Y))
--       | ! [Y1: animal] :
--           ( ( much_smaller(Y1,X)
--             & ? [Z: plant] : eats(Y1,plant_to_edible(Z)) )
--          => eats(X,animal_to_edible(Y1)) ) ) ).

-- tff(pel47_8,axiom,
--     ! [X: snail,Y: bird] : much_smaller(snail_to_animal(X),bird_to_animal(Y)) ).

-- tff(pel47_8a,axiom,
--     ! [X: caterpillar,Y: bird] : much_smaller(caterpillar_to_animal(X),bird_to_animal(Y)) ).

-- tff(pel47_9,axiom,
--     ! [X: bird,Y: fox] : much_smaller(bird_to_animal(X),fox_to_animal(Y)) ).

-- tff(pel47_10,axiom,
--     ! [X: fox,Y: wolf] : much_smaller(fox_to_animal(X),wolf_to_animal(Y)) ).

-- tff(pel47_11,axiom,
--     ! [X: wolf,Y: fox] : ~ eats(wolf_to_animal(X),animal_to_edible(fox_to_animal(Y))) ).

-- tff(pel47_11a,axiom,
--     ! [X: wolf,Y: grain] : ~ eats(wolf_to_animal(X),plant_to_edible(grain_to_plant(Y))) ).

-- tff(pel47_12,axiom,
--     ! [X: bird,Y: caterpillar] : eats(bird_to_animal(X),animal_to_edible(caterpillar_to_animal(Y))) ).

-- tff(pel47_13,axiom,
--     ! [X: bird,Y: snail] : ~ eats(bird_to_animal(X),animal_to_edible(snail_to_animal(Y))) ).

-- tff(pel47_14,axiom,
--     ! [X: caterpillar] :
--     ? [Y: plant] : eats(caterpillar_to_animal(X),plant_to_edible(Y)) ).

-- tff(pel47_14a,axiom,
--     ! [X: snail] :
--     ? [Y: plant] : eats(snail_to_animal(X),plant_to_edible(Y)) ).

-- tff(pel47,conjecture,
--     ? [X: animal,Y: animal,Z: grain] :
--       ( eats(Y,plant_to_edible(grain_to_plant(Z)))
--       & eats(X,animal_to_edible(Y)) ) ).

-- END_TPTP
-- sorry

-- #check my_problem

-- partial def parseMyType (env : Environment) (s : String) : CoreM String := do
--   match runParserCategory env `term s with
--   | Except.error e => throwError e
--   | Except.ok r => return s!"{r}"

-- set_option trace.Meta.debug true
-- #eval show CoreM _ from return ← parseMyType (← getEnv) "Nat.succ c d e"


 

 



-- partial def parseMyType (env : Environment) (s : String) : CoreM String := do
--   match runParserCategory env `TPTP_file s with
--   | Except.error e => throwError e
--   | Except.ok r => return s!"{r}"

-- set_option trace.Meta.debug true
-- #eval show CoreM _ from return ← parseMyType (← getEnv) "tff(a,axiom,q)."


 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 