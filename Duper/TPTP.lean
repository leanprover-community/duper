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

syntax tff_annotation := "," ident

syntax tff_term : tff_formula
syntax ident ":" tff_type : tff_formula


syntax defined_type := "$" noWs ident
syntax defined_type : tff_atomic_type
syntax tff_atomic_type : tff_type

def tffXProdArgsParser := sepBy1 (categoryParser `tff_atomic_type 0) "*"
syntax tff_xprod_args := tffXProdArgsParser

syntax tff_atomic_type ">" tff_atomic_type : tff_type
syntax "(" tff_xprod_args ")" ">" tff_atomic_type : tff_type


syntax TPTP_input := 
  "tff" "(" ident "," ident "," tff_formula tff_annotation ? ")" "."


syntax TPTP_input* : TPTP_file

def explicitBinder : Parser := Term.explicitBinder false

constant iota : Type

partial def processTffTerm (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_term| $f:ident $args:tff_arguments ?) => do
    let ts : Array Syntax ← match args with
    | some args =>
      pure $ ← ((@Syntax.SepArray.mk "," args[1].getArgs) : Array Syntax).mapM 
                fun arg => processTffTerm arg
    | none => pure #[]
    let ts := mkNode ``many ts
    let ts := mkNode ``Term.app #[f, ts]
    return ← `($ts)
  | _ => Macro.throwError s!"Unsupported tff_term: {stx}"

def processTffAtomicType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(tff_atomic_type| $ty:defined_type) =>
    match ty[1].getId with
    | `i => return ← `(TPTP.iota)
    | `o => return ← `(Prop)
    | `tType => return ← `(Type)
    | _ => Macro.throwError s!"Unsupported tff_atomic_type: {ty}"
  | _ => Macro.throwError s!"Unsupported tff_atomic_type: {stx}"

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
    | `(TPTP_input| tff($name:ident,$role:ident,$formula:tff_formula $annotation:tff_annotation ?).) =>
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
tff(hp, ax, p(f(f(f(f(c,c),c),c),c)) ).

-- tff(wolf_type, ax, q ).
END_TPTP
by sorry

#check my_problem


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


 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 

 