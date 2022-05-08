import Lean

namespace TPTP
open Lean
open Lean.Parser

declare_syntax_cat TPTP_file

declare_syntax_cat tff_type
declare_syntax_cat tff_term
declare_syntax_cat tff_formula
declare_syntax_cat tff_atomic_type

syntax tff_arguments := "(" tff_term,* ")"
syntax ident tff_arguments ? : tff_term
syntax "(" tff_term ")" : tff_term

syntax binary_connective := "|" <|> "&" <|> "<=>" <|> "=>" <|> "<=" <|> "=" <|> "!="
syntax tff_term binary_connective tff_term : tff_term
syntax "~" tff_term : tff_term

syntax tff_annotation := "," ident

syntax tff_term : tff_formula
syntax ident ":" tff_type : tff_formula

syntax defined_type := "$" noWs ident
syntax defined_type : tff_atomic_type
syntax ident : tff_atomic_type
syntax tff_atomic_type : tff_type

def tffXProdArgsParser := sepBy1 (categoryParser `tff_atomic_type 0) "*"
syntax tff_xprod_args := tffXProdArgsParser

syntax tff_atomic_type ">" tff_atomic_type : tff_type
syntax "(" tff_xprod_args ")" ">" tff_atomic_type : tff_type

syntax fof_quantifier := "!" <|> "?"
syntax tff_variable := ident (":" tff_atomic_type) ?
syntax fof_quantifier "[" tff_variable,* "]" ":" tff_term : tff_term

syntax TPTP_input := 
  "tff" "(" ident "," (ident <|> "axiom") "," tff_formula tff_annotation ? ")" "."


syntax TPTP_input* : TPTP_file

def explicitBinder : Parser := Term.explicitBinder false

constant iota : Type

def processTffAtomicType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_atomic_type| $ty:ident) => pure ty
  | `(tff_atomic_type| $ty:defined_type) =>
    match ty[1].getId with
    | `i => return ← `(TPTP.iota)
    | `o => return ← `(Prop)
    | `tType => return ← `(Type)
    | _ => Macro.throwError s!"Unsupported tff_atomic_type: {ty}"
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
    match conn[0].getKind with
    | `«&» => `($t₁ ∧ $t₂)
    | `«=>» => `($t₁ → $t₂)
    | `«|» => `($t₁ ∨ $t₂)
    | _ => Macro.throwError s!"Unsupported binary_connective: {conn[0].getKind}"
  | `(tff_term| $f:ident $args:tff_arguments ?) => do
    let ts : Array Syntax ← match args with
    | some args =>
      pure $ ← ((@Syntax.SepArray.mk "," args[1].getArgs) : Array Syntax).mapM 
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
          pure (v, ← `(_))
        | `(tff_variable| $v:ident : $ty:tff_atomic_type) => 
          pure (v, ← processTffAtomicType ty)
        | _ => Macro.throwError s!"Unsupported tff_variable: {v}"
        match q[0].getKind with
        | `«!» => `(∀ ($v : $ty), $acc)
        | `«?» => `(Exists fun ($v : $ty) => $acc)
        | _ => Macro.throwError s!"Unsupported fof_quantifier: {q.getKind}"
      body
  | _ => Macro.throwError s!"Unsupported tff_term: {stx}"

partial def processTffType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_type| $ty:tff_atomic_type) =>
    processTffAtomicType ty
  | `(tff_type| $arg:tff_atomic_type > $ret:tff_atomic_type) =>
    let ret ← processTffAtomicType ret
    let arg ← processTffAtomicType arg
    return ← `($arg → $ret)
  | `(tff_type| ( $args:tff_xprod_args ) > $ret:tff_atomic_type) =>
    let ret ← processTffAtomicType ret
    let args : Array Syntax := @Syntax.SepArray.mk "*" args[0].getArgs
    let stx ← args.foldrM (fun (a acc : Syntax) => do
      let a ← processTffAtomicType a
      `($a → $acc)) ret
    return stx
  | _ => Macro.throwError s!"Unsupported tff_type: {stx}"

macro "BEGIN_TPTP" name:ident s:TPTP_file "END_TPTP" proof:term : command => do
  let hyps ← s[0].getArgs.mapM fun input => do
    match input with
    | `(TPTP_input| tff($name:ident,$role,$formula:tff_formula $annotation:tff_annotation ?).) =>
      match formula with
      | `(tff_formula| $term:tff_term) =>
        let term ← processTffTerm term
        return ← `(explicitBinder| ($name : $term))
      | `(tff_formula| $name:ident : $ty:tff_type) =>
        let ty ← processTffType ty
        return ← `(explicitBinder| ($name : $ty))
      | _ => Macro.throwError s!"Unsupported tff_formula: {formula}"
    | _ => Macro.throwError s!"Unsupported TPTP_input: {input}"
  let hyps := mkNode ``many hyps
  let spec ← `(Term.typeSpec| : False)
  let sig := mkNode ``Command.declSig #[hyps,spec]
  return ← `(theorem $name $sig := $proof)

BEGIN_TPTP my_problem
tff(wolf_type, type, c: $i ).
tff(wolf_type, type, f: ($i * $i) > $i ).
tff(wolf_type, type, p: $i > $o ).
-- tff(wolf_type, ax, p(f(x,f(x),f(c)))).
tff(hp, axiom, ! [X : $i] : p(f(f(f(f(c,c),c),c),X)) ).
tff(hp, axiom, ? [X : $i] : p(f(f(f(f(c,c),c),c),X)) ).
tff(hp, axiom, ! [X] : p(f(f(f(f(c,c),c),c),X)) ).
tff(hp, axiom, ? [X] : p(f(f(f(f(c,c),c),c),X)) ).

-- tff(wolf_type, ax, q ).
END_TPTP
by sorry


BEGIN_TPTP my_problem2
tff(box_type,type,
    box: $tType ).

tff(fruit_type,type,
    fruit: $tType ).

tff(boxa_type,type,
    boxa: box ).

tff(boxb_type,type,
    boxb: box ).

tff(boxc_type,type,
    boxc: box ).

tff(apples_type,type,
    apples: fruit ).

tff(bananas_type,type,
    bananas: fruit ).

tff(oranges_type,type,
    oranges: fruit ).

tff(equal_fruits_type,type,
    equal_fruits: ( fruit * fruit ) > $o ).

tff(equal_boxes_type,type,
    equal_boxes: ( box * box ) > $o ).

tff(contains_type,type,
    contains: ( box * fruit ) > $o ).

tff(label_type,type,
    label: ( box * fruit ) > $o ).

tff(reflexivity_for_fruits,axiom,
    ! [X: fruit] : equal_fruits(X,X) ).

tff(reflexivity_for_boxes,axiom,
    ! [X: box] : equal_boxes(X,X) ).

tff(label_is_wrong,axiom,
    ! [X: box,Y: fruit] :
      ~ ( label(X,Y)
        & contains(X,Y) ) ).

tff(each_thing_is_in_a_box,axiom,
    ! [X: fruit] :
      ( contains(boxa,X)
      | contains(boxb,X)
      | contains(boxc,X) ) ).

tff(each_box_contains_something,axiom,
    ! [X: box] :
      ( contains(X,apples)
      | contains(X,bananas)
      | contains(X,oranges) ) ).

tff(contains_is_well_defined1,axiom,
    ! [X: box,Y: fruit,Z: fruit] :
      ( ( contains(X,Y)
        & contains(X,Z) )
     => equal_fruits(Y,Z) ) ).

tff(contains_is_well_defined2,axiom,
    ! [X: box,Y: fruit,Z: box] :
      ( ( contains(X,Y)
        & contains(Z,Y) )
     => equal_boxes(X,Z) ) ).

tff(boxa_not_boxb,axiom,
    ~ equal_boxes(boxa,boxb) ).

tff(boxb_not_boxc,axiom,
    ~ equal_boxes(boxb,boxc) ).

tff(boxa_not_boxc,axiom,
    ~ equal_boxes(boxa,boxc) ).

tff(apples_not_bananas,axiom,
    ~ equal_fruits(apples,bananas) ).

tff(bananas_not_oranges,axiom,
    ~ equal_fruits(bananas,oranges) ).

tff(apples_not_oranges,axiom,
    ~ equal_fruits(apples,oranges) ).

tff(boxa_labelled_apples,hypothesis,
    label(boxa,apples) ).

tff(boxb_labelled_oranges,hypothesis,
    label(boxb,oranges) ).

tff(boxc_labelled_bananas,hypothesis,
    label(boxc,bananas) ).

tff(boxb_contains_apples,hypothesis,
    contains(boxb,apples) ).

tff(prove_boxa_contains_bananas_and_boxc_oranges,conjecture,
    ( contains(boxa,bananas)
    & contains(boxc,oranges) ) ).

END_TPTP
sorry
