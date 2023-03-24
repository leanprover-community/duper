import Lean
import Duper.TPTPParser.SyntaxDecl

open Lean
open Lean.Parser
open TSyntax.Compat

namespace TPTP

def explicitBinder : Parser := Term.explicitBinder false

axiom iota : Type
private axiom iotaInhabited : iota
noncomputable instance : Inhabited iota := ⟨iotaInhabited⟩

def processThfDefinedType (ty : Syntax) : MacroM Syntax := do
  match ty with
  | `(defined_type|🍉$id) =>
    match id.getId with
    | `i => `(TPTP.iota)
    | `o => `(Prop)
    | `tType => `(Type)
    | _ => Macro.throwError s!"Unsupported thf_defined_type: {ty}"
  | _ => Macro.throwError s!"{ty} is not a defined type"

def processThfDefinedTerm (term : Syntax) : MacroM Syntax := do
  match term with
  | `(defined_term|🍉$id) =>
    match id.getId with
    | `true => `(True)
    | `false => `(False)
    | _ => Macro.throwError s!"Unsupported thf_defined_term: {term}"
  | _ => Macro.throwError s!"{term} is not a defined term" 

partial def processThfAtomicType (stx : Syntax) : MacroM Syntax := do
  match stx with
  | `(thf_type| $ty:thf_atomic_type) => processThfAtomicType ty
  | `(thf_atomic_type| $ty:ident) => pure ty
  | `(thf_atomic_type| $ty:defined_type) => processThfDefinedType ty
  | `(thf_atomic_type| $f:ident $args:thf_type_arguments) => do
    let ts ←
      pure $ ← ((@Syntax.SepArray.mk "," args.raw[1].getArgs) : Array Syntax).mapM
                fun arg => processThfAtomicType arg
    let ts := mkNode ``many ts
    let ts := mkNode ``Term.app #[f, ts]
    `($ts)
  | _ => Macro.throwError s!"Unsupported thf_atomic_type: {stx}"

/-- In addition to returning the syntax that corresponds to the type of `stx`, if the
    type of `stx` is `Type` or has the form `A → B → ... → Type`, then we also return
    an Array containing the stx for `A`, `B`, etc. (in reverse order. So `A → B → Type` would
    have the stx array #[B, A]) This is so that we can add the appropriate `Inhabited` constraints
    to the newly declared type. -/
partial def processThfType (stx : Syntax) : MacroM (Syntax × Option (Array Syntax)) := do
  match stx with
  | `(thf_type| ( $t:thf_type ) ) => processThfType t
  | `(thf_type| $ty:thf_atomic_type) =>
    let res ← processThfAtomicType ty
    let typeStx ← `(Type)
    if res == typeStx then return (res, some #[])
    else return (res, none)
  | `(thf_type| $arg:thf_type > $ret:thf_type) =>
    -- Although the current parser syntax has thf_type > thf_type, this pattern should
    -- only appear in TPTP files when both arg and ret are of the category thf_atomic_type
    let (ret, stxListOpt) ← processThfType ret
    let (arg, _) ← processThfType arg
    let res ← `($arg → $ret)
    match stxListOpt with
    | none => return (res, none)
    | some stxList => return (res, some (stxList.push arg))
  | `(thf_type| ( $args:thf_xprod_args ) > $ret:thf_atomic_type) =>
    let ret ← processThfAtomicType ret
    let args : Array Syntax := @Syntax.SepArray.mk "*" args.raw[0].getArgs
    let args ← args.mapM (fun a => processThfAtomicType a)
    let res ← args.foldrM (fun (a acc : Syntax) => `($a → $acc)) ret
    let typeStx ← `(Type)
    if ret == typeStx then return (res, some args.reverse)
    else return (res, none)
  | `(thf_type| $q:th1_quantifier [ $vs,* ] : $ty) =>
    let (ty, _) ← processThfType ty
    let vs : Array Syntax := vs
    let res ← vs.foldrM
      fun v acc => do
        let (v, v_ty) ← match v with
        | `(thf_variable| $v:ident) =>
          -- throw Error?
          pure (v, (← `(_) : Syntax))
        | `(thf_variable| $v:ident : $v_ty:thf_type) =>
          pure (v, (← processThfType v_ty).1)
        | _ => Macro.throwError s!"Unsupported thf_variable: {v} when trying to process a tf1_quantified_type"
        match q.raw[0].getKind with
        | Name.str _ "!>" => `(∀ ($v : $v_ty), $acc)
        | _ => Macro.throwError s!"Unsupported th1_quantifier: {q.raw[0].getKind}"
      ty
    return (res, none)
  | _ => Macro.throwError s!"Unsupported thf_type: {stx}"

partial def processThfTerm (stx : Syntax) (is_untyped : Bool) : MacroM Syntax := do
  match stx with
  | `(thf_term| $d:defined_term) => processThfDefinedTerm d
  | `(thf_term| ( $t:thf_term ) ) => processThfTerm t is_untyped
  | `(thf_term| ~ $t:thf_term ) =>
    let t ← processThfTerm t is_untyped
    `(¬ $t)
  | `(thf_term| $t₁:thf_term @ $t₂:thf_term) => do
    let t₁ ← processThfTerm t₁ is_untyped
    let t₂ ← processThfTerm t₂ is_untyped
    `(($t₁ $t₂))
  | `(thf_term| $t₁:thf_term $conn:bexpOp $t₂:thf_term ) => do
    let t₁ ← processThfTerm t₁ is_untyped
    let t₂ ← processThfTerm t₂ is_untyped
    match conn.raw[0].getKind with
    | Name.str _ "&" => `($t₁ ∧ $t₂)
    | Name.str _ "=>" => `($t₁ → $t₂)
    | Name.str _ "|"=> `($t₁ ∨ $t₂)
    | Name.str _ "<=>" => `($t₁ ↔ $t₂)
    | Name.str _ "<~>" => `(¬ ($t₁ ↔ $t₂))
    | Name.str _ "~|" => `(¬ ($t₁ ∨ $t₂))
    | Name.str _ "~&" => `(¬ ($t₁ ∧ $t₂))
    | _ => Macro.throwError s!"Unsupported bexpOp: {conn.raw[0].getKind}"
  | `(thf_term| $t₁:thf_term $conn:eqOp $t₂:thf_term ) => do
    let t₁ ← processThfTerm t₁ is_untyped
    let t₂ ← processThfTerm t₂ is_untyped
    match conn.raw[0].getKind with
    | Name.str _ "=" => `($t₁ = $t₂)
    | Name.str _ "!=" => `($t₁ ≠ $t₂)
    | _ => Macro.throwError s!"Unsupported eqOp: {conn.raw[0].getKind}"
  | `(thf_term| $f:ident $args:thf_arguments ?) => do
    let ts : Array Syntax ← match args with
    | some args =>
      ((@Syntax.SepArray.mk "," args.raw[1].getArgs) : Array Syntax).mapM
          fun arg => processThfTerm arg is_untyped
    | none => pure #[]
    let ts := mkNode ``many ts
    let ts := mkNode ``Term.app #[f, ts]
    `($ts)
  | `(thf_term| $q:quantifier [ $vs,* ] : $body) => do
    let body ← processThfTerm body is_untyped
    let vs : Array Syntax := vs
    vs.foldrM
      fun v acc => do
        let (v, ty) ← match v with
        | `(thf_variable| $v:ident) =>
          if is_untyped then
            let iotaTypeSyntax ← `(TPTP.iota)
            pure (v, iotaTypeSyntax.raw)
          else
            -- throw Error?
            pure (v, (← `(_) : Syntax))
        | `(thf_variable| $v:ident : $ty:thf_type) =>
          pure (v, (← processThfType ty).1)
        | _ => Macro.throwError s!"Unsupported thf_variable: {v}"
        match q.raw[0].getKind with
        | Name.str _ "!" => `(∀ ($v : $ty), $acc)
        | Name.str _ "?" => `(Exists fun ($v : $ty) => $acc)
        | Name.str _ "^" => `(fun ($v : $ty) => $acc)
        | _ => Macro.throwError s!"Unsupported quantifier: {q.raw[0].getKind}"
      body
  | _ => Macro.throwError s!"Unsupported thf_term: {stx}"

/-- Determines whether an identifier is a variable by checking whether the first character is capital -/
def isVar (stx : TSyntax `ident) : MacroM Bool := do
  match stx with
  | Syntax.ident _ rawVal _ _ => return (rawVal.get 0).isUpper
  | _ => Macro.throwError "Non-ident passed into isVar"

/-- Given a piece of syntax, returns the list of variables that appear in said syntax. This function
    may return lists in which the same variable appears multiple times. -/
partial def getVarsHelper (stx : Syntax) : MacroM (List (TSyntax `ident)) := do
  match stx with
  | `(thf_term| ( $t:thf_term )) => getVarsHelper t
  | `(thf_term| ~ $t:thf_term ) => getVarsHelper t
  | `(thf_term| $t1:thf_term $conn:bexpOp $t2:thf_term ) =>
    return (← getVarsHelper t1).append (← getVarsHelper t2)
  | `(thf_term| $t1:thf_term $conn:eqOp $t2:thf_term ) =>
    return (← getVarsHelper t1).append (← getVarsHelper t2)
  | `(thf_term| $f:ident $args:thf_arguments ?) =>
    match args with
    | none =>
      if (← isVar f) then return [f]
      else return []
    | some args =>
      let args := ((@Syntax.SepArray.mk "," args.raw[1].getArgs) : Array Syntax)
      let argsVars ← args.mapM (fun arg => getVarsHelper arg)
      let argsVars := argsVars.foldl
        (fun acc varList => varList.append acc) []
      if (← isVar f) then return f :: argsVars
      else return argsVars
  | _ => Macro.throwError s!"Unsupported cnf term: {stx}"

/-- Given a piece of syntax, returns the list of variables that appear in said syntax. This function is needed
    because cnf clauses are implicitly universally quantified (but Lean requires that we explicitly universally
    quantify the variables). This function is only intended to be called on cnf clauses. -/
def getVars (stx : Syntax) : MacroM (List (TSyntax `ident)) := do
  let varsWithDuplicates ← getVarsHelper stx
  let vars := varsWithDuplicates.foldl
    (fun acc var => if acc.contains var then acc else var :: acc) []
  return vars

partial def processCnfTerm (stx : Syntax) : MacroM Syntax := do
  let vars ← getVars stx
  let iotaTypeSyntax ← `(TPTP.iota)
  let unquantifiedRes ← processThfTerm stx true
  let quantifiedRes ← vars.foldlM
    (fun acc (var : TSyntax `ident) => `(∀ ($var : $iotaTypeSyntax), $acc)) unquantifiedRes
  return quantifiedRes

/-- Note: This function is only meant to be used for fof/cnf formats (tff files declare their own symbols).

    Returns a list in which each element is `(explicitBinder| ($name : $ty)) where $name is a symbol that
    appears in stx (and isn't a variable) and $ty is the type of said symbol.

    In fof/cnf formats, the only base types are Prop and `iota. All symbols therefore must be of type Prop, type
    `iota, or functions that output Prop or iota. Which of these is the case can be determined by the position
    of the symbol in the overall formula.

    The topType argument is used to keep track of what the overall type of stx is supposed to be. -/
partial def getNonVarSymbols (acc : HashMap String (TSyntax `TPTP.explicitBinder)) (topType : TSyntax `thf_type)
  (stx : Syntax) : MacroM (HashMap String (TSyntax `TPTP.explicitBinder)) := do
  match stx with
  | `(thf_term|🍉$id:ident) => return acc
  | `(thf_term| ( $t:thf_term )) => getNonVarSymbols acc topType t
  | `(thf_term| ~ $t:thf_term ) =>
    if topType != (← `(Prop)) then Macro.throwError s!"Error: cnf/fof term: {stx} is supposed to have type {topType}"
    else getNonVarSymbols acc (← `(Prop)) t
  | `(thf_term| $t1:thf_term $conn:bexpOp $t2:thf_term ) =>
    if topType != (← `(Prop)) then Macro.throwError s!"Error: cnf/fof term: {stx} is supposed to have type {topType}"
    else
      match conn.raw[0].getKind with
      | Name.str _ "&" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | Name.str _ "=>" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | Name.str _ "|" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | Name.str _ "<=>" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | Name.str _ "<~>" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | Name.str _ "~|" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | Name.str _ "~&" => getNonVarSymbols (← getNonVarSymbols acc (← `(Prop)) t1) (← `(Prop)) t2
      | _ => Macro.throwError s!"Unsupported bexpOp: {conn.raw[0].getKind}"
  | `(thf_term| $t1:thf_term $conn:eqOp $t2:thf_term ) =>
    if topType != (← `(Prop)) then Macro.throwError s!"Error: cnf/fof term: {stx} is supposed to have type {topType}"
    else
      match conn.raw[0].getKind with
      | Name.str _ "=" => getNonVarSymbols (← getNonVarSymbols acc (← `(TPTP.iota)) t1) (← `(TPTP.iota)) t2
      | Name.str _ "!=" => getNonVarSymbols (← getNonVarSymbols acc (← `(TPTP.iota)) t1) (← `(TPTP.iota)) t2
      | _ => Macro.throwError s!"Unsupported eqOp: {conn.raw[0].getKind}"
  | `(thf_term| $f:ident $args:thf_arguments ?) =>
    if (← isVar f) then
      if let some _ := args then
        Macro.throwError s!"Variable used as function in cnf/fof term: {stx}"
      else
        return acc
    match args with
    | none =>
      let s := f.getId.getString!
      let binder ← `(explicitBinder| ($f : $topType))
      return acc.insert s binder
    | some args =>
      let args := ((@Syntax.SepArray.mk "," args.raw[1].getArgs) : Array Syntax)
      let iotaTypeSyntax ← `(TPTP.iota)
      let fType ← args.foldlM (fun (acc _ : Syntax) => do
        `($iotaTypeSyntax → $acc)) topType
      let acc ← args.foldlM (fun acc arg => do
        getNonVarSymbols acc (← `(TPTP.iota)) arg) acc
      let s := f.getId.getString!
      let binder ← `(explicitBinder| ($f : $fType))
      return acc.insert s binder
  | `(thf_term| $q:quantifier [ $vs,* ] : $body) =>
    if topType != (← `(Prop)) then Macro.throwError s!"Error: cnf/fof term: {stx} is supposed to have type {topType}"
    else getNonVarSymbols acc (← `(Prop)) body
  | _ => Macro.throwError s!"Unsupported cnf/fof term: {stx}"

macro "BEGIN_TPTP" name:ident s:TPTP_file "END_TPTP" proof:term : command => do
  let mut symtab : HashMap String (TSyntax `TPTP.explicitBinder) := HashMap.empty
  let sargs := s.raw[0].getArgs
  for input in sargs do
    match input with
    | `(TPTP_input| tff($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      pure () -- Only need to retrieve symbols from cnf and fof files
    | `(TPTP_input| tff($n:ident,type,$name:ident : $ty:thf_type $annotation:annotation ?).) =>
      pure () -- Only need to retrieve symbols from cnf and fof files
    | `(TPTP_input| thf($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      pure ()
    | `(TPTP_input| thf($n:ident,type,$name:ident : $ty:thf_type $annotation:annotation ?).) =>
      pure () -- Only need to retrieve symbols from cnf and fof files
    | `(TPTP_input| cnf($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      symtab ← getNonVarSymbols symtab (← `(Prop)) term
    | `(TPTP_input| fof($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      symtab ← getNonVarSymbols symtab (← `(Prop)) term
    | _ => Macro.throwError s!"Unsupported TPTP_input: {input}"
  -- Perform a foldl so that we only have one binder for each symbol
  let nonVarSymbols := (symtab.toList).foldl
    (fun acc (_, binder) =>
      if List.contains acc binder then acc
      else binder :: acc) []
  let mut hyps : Array (TSyntax `TPTP.explicitBinder) := #[]
  for input in sargs do
    match input with
    | `(TPTP_input| tff($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      let term ← processThfTerm term false
      let name := (mkIdent $ name.getId.appendBefore "h")
      if role.getId == `conjecture then
        hyps := hyps.push (← `(explicitBinder| ($name : ¬ $term)))
      else
        hyps := hyps.push (← `(explicitBinder| ($name : $term)))
    | `(TPTP_input| tff($n:ident,type,$name:ident : $ty:thf_type $annotation:annotation ?).) =>
      let (ty, stxArrOpt) ← processThfType ty
      hyps := hyps.push (← `(explicitBinder| ($name : $ty)))
      match stxArrOpt with
      | none => continue
      | some stxArr =>
        let typeArgName := `typeArg
        let mut counter := 0
        let mut nameApp ← `($name)
        let mut typeArgs : Array Ident := #[]
        for _ in stxArr do
          let typeArg := mkIdent $ typeArgName.appendAfter (toString counter)
          nameApp ← `($nameApp $typeArg)
          counter := counter + 1
          typeArgs := typeArgs.push typeArg
        let mut quantifiedNameApp ← `(Inhabited $nameApp)
        for (stx, typeArg) in stxArr.zip typeArgs.reverse do
          quantifiedNameApp ← `(∀ $typeArg : $stx, $quantifiedNameApp)
        hyps := hyps.push (← `(explicitBinder| (_ : $quantifiedNameApp)))
    | `(TPTP_input| thf($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      let term ← processThfTerm term false
      let name := (mkIdent $ name.getId.appendBefore "h")
      if role.getId == `conjecture then
        hyps := hyps.push (← `(explicitBinder| ($name : ¬ $term)))
      else
        hyps := hyps.push (← `(explicitBinder| ($name : $term)))
    | `(TPTP_input| thf($n:ident,type,$name:ident : $ty:thf_type $annotation:annotation ?).) =>
      let (ty, stxArrOpt) ← processThfType ty
      hyps := hyps.push (← `(explicitBinder| ($name : $ty)))
      match stxArrOpt with
      | none => continue
      | some stxArr =>
        let typeArgName := `typeArg
        let mut counter := 0
        let mut nameApp ← `($name)
        let mut typeArgs : Array Ident := #[]
        for _ in stxArr do
          let typeArg := mkIdent $ typeArgName.appendAfter (toString counter)
          nameApp ← `($nameApp $typeArg)
          counter := counter + 1
          typeArgs := typeArgs.push typeArg
        let mut quantifiedNameApp ← `(Inhabited $nameApp)
        for (stx, typeArg) in stxArr.zip typeArgs.reverse do
          quantifiedNameApp ← `(∀ $typeArg : $stx, $quantifiedNameApp)
        hyps := hyps.push (← `(explicitBinder| (_ : $quantifiedNameApp)))
    | `(TPTP_input| cnf($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      let term ← processCnfTerm term
      let name := (mkIdent $ name.getId.appendBefore "h")
      if role.getId == `conjecture then
        hyps := hyps.push (← `(explicitBinder| ($name : ¬ $term)))
      else
        hyps := hyps.push (← `(explicitBinder| ($name : $term)))
    | `(TPTP_input| fof($name:ident,$role,$term:thf_term $annotation:annotation ?).) =>
      -- Although tff differs from fof, I think that processThfTerm will do what we want for fof terms
      let term ← processThfTerm term true
      let name := (mkIdent $ name.getId.appendBefore "h")
      if role.getId == `conjecture then
        hyps := hyps.push (← `(explicitBinder| ($name : ¬ $term)))
      else
        hyps := hyps.push (← `(explicitBinder| ($name : $term)))
    | _ => Macro.throwError s!"Unsupported TPTP_input: {input}"
  let hypall := mkNode ``many (nonVarSymbols.toArray.append hyps)
  let spec ← `(Term.typeSpec| : False)
  let sig := mkNode ``Command.declSig #[hypall,spec]
  `(theorem $name $sig := $proof)