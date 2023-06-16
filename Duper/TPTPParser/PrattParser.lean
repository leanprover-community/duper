import Lean

axiom Iota : Type

namespace TPTP

namespace Tokenizer
open Lean

inductive Status :=
| default
| ident
deriving Repr

inductive Token :=
| op (op : String)
| ident (ident : String)
deriving Repr, Inhabited, BEq

def Token.toString : Token → String
| .op a => a
| .ident a => a

structure State where
(status : Status := .default)
(currToken : String := "")
(res : Array Token := #[])
deriving Repr

def tokens := [
  "@", "|", "&", "<=>", "=>", "<=", "<~>", "~|", "~&", ">", "=", "!=",
  "~", ",", "(", ")", "*", "!", "?", "^", ":", "[", "]", "!>", ".", "*"
]

def tokenHashMap : HashSet String := 
  HashSet.empty.insertMany tokens

def tokenPrefixes : HashSet String := 
  HashSet.empty.insertMany $ tokens.bind (fun t => Id.run do
    let mut res := []
    let mut pref := ""
    for c in t.data do
      pref := pref.push c
      res := pref :: res
    return res
)

abbrev TokenizerM := StateRefT State IO

def setStatus (status : Status) : TokenizerM Unit := do
  modify (fun (s : State) => {s with status := status})

def getStatus : TokenizerM Status := do
  return (← get).status

def addToCurrToken (char : Char) : TokenizerM Unit := do
  modify (fun (s : State) => {s with currToken := s.currToken.push char})

def getCurrToken : TokenizerM String := do
  return (← get).currToken
  
def addCurrToken : TokenizerM Unit := do
  modify fun (s : State) => 
    {s with 
      res := s.res.push $ match s.status with | .default => .op s.currToken | .ident => .ident s.currToken, 
      currToken := ""
    }

def finalizeToken : TokenizerM Unit := do
  if (← getCurrToken) != "" then
    match ← getStatus with
    | .default => 
      if tokenHashMap.contains (← getCurrToken)
      then addCurrToken
      else throw $ IO.userError s!"Invalid token: {(← getCurrToken)}"
    | .ident => addCurrToken
    setStatus .default

def tokenizeAux (str : String) : TokenizerM Unit := do
  for char in str.data do
    if char.isWhitespace then
        finalizeToken
    else
      match ← getStatus with
      | .default =>
        if char.isAlpha || char == '$' then
          finalizeToken
          setStatus .ident
          addToCurrToken char
        else if tokenPrefixes.contains ((← getCurrToken).push char) then
          addToCurrToken char
        else if tokenPrefixes.contains (⟨[char]⟩) then
          finalizeToken
          addToCurrToken char
        else throw $ IO.userError s!"Invalid token: {char}"
      | .ident => 
        if char.isAlphanum || char == '_'
        then addToCurrToken char
        else
          finalizeToken
          addToCurrToken char
          setStatus .default
  
  finalizeToken

  def tokenize (s : String) : IO (Array Token) := do
    return (← (tokenizeAux s).run {}).2.res

end Tokenizer

namespace Parser
open Tokenizer
/- Pratt parser following `https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html`-/

structure State where
(tokens : Array Token)
(curr : Nat := 0)
deriving Repr


abbrev ParserM := StateRefT State IO

def isEOF : ParserM Bool := do return (← get).curr ==  (← get).tokens.size

def peek : ParserM Token := do
  let i := (← get).curr
  let ts := (← get).tokens
  if i >= ts.size then throw $ IO.userError "Unexpected end of file"
  return ts[i]!

def peek? : ParserM (Option Token) := do
  if ← isEOF then return none else return ← peek 

def next : ParserM Token := do
  let c ← peek
  modify (fun (s : State) => {s with curr := s.curr + 1})
  return c

def infixBindingPower? : String → Option (Nat × Nat)
| "|" | "&" | "<=>" | "=>" | "<=" | "<~>" | "~|" | "~&" => (60,61)
| "=" | "!=" => (90, 90)
| "*" => (111, 110)
| ">" => (121, 120)
| "@" => (130, 131)
| _ => none

def prefixBindingPower? : String → Option Nat
| "~" => some 70
| _ => none

def BinderBindingPower? : String → Option Nat
| "!" | "!>" | "?" | "^" => some 70
| _ => none

inductive Term where
| mk : Token → List Term → Term
deriving Inhabited, Repr

def Term.func : Term → Token := fun ⟨n, _⟩ => n
def Term.args : Term → List Term := fun ⟨_, as⟩ => as

def parseToken (t : Token) : ParserM Unit := do
  let nextToken ← next
  if nextToken != t then throw $ IO.userError s!"Expected '{t.toString}', got '{repr nextToken}'"

def parseIdent : ParserM String := do
  let nextToken ← next
  let .ident id := nextToken
    | throw $ IO.userError s!"Expected identifier, got '{repr nextToken}'"
  return id

partial def parseSep (sep : Token) (p : ParserM α) : ParserM (List α) := do
  let t ← p
  if (← peek?) == some sep then
    parseToken sep
    let l ← parseSep sep p
    return t :: l
  else
    return [t]

mutual
partial def parseTerm (minbp : Nat := 0) : ParserM Term := do        
  let lhs ← parseLhs 
  let res ← addOpAndRhs lhs minbp
  return res

partial def parseLhs : ParserM Term := do
  let nextToken ← next
  if let .ident _ := nextToken then
    if (← peek?) == some (.op "(") then
      parseToken (.op "(")
      let args ← parseSep (.op ",") (parseTerm 0)
      parseToken (.op ")")
      return Term.mk nextToken args
    else
      return Term.mk nextToken []
  else if nextToken == .op "(" then
    let lhs ← parseTerm 0
    parseToken (.op ")")
    return lhs
  else if let some rbp := BinderBindingPower? nextToken.toString then
    parseToken (.op "[")
    let vars ← parseSep (.op ",") parseTypeDecl
    parseToken (.op "]")
    parseToken (.op ":")
    let rhs ← parseTerm rbp
    return Term.mk nextToken (rhs :: vars)
  else if let some rbp := prefixBindingPower? nextToken.toString then
    let rhs ← parseTerm rbp
    return Term.mk nextToken [rhs]
  else
    throw $ IO.userError s!"Expected term, got '{repr nextToken}'"

partial def addOpAndRhs (lhs : Term) (minbp : Nat) : ParserM Term := do
  if ← isEOF then
    return lhs
  else
    let op ← peek
    let some (lbp, rbp) := infixBindingPower? op.toString
      | return lhs
    if lbp < minbp then
      return lhs
    else
      let op ← next
      let rhs ← parseTerm rbp
      return ← addOpAndRhs (Term.mk op [lhs, rhs]) minbp

partial def parseTypeDecl : ParserM Term := do
  let ident ← parseIdent
  if (← peek?) == some (.op ":") then
    parseToken (.op ":")
    let ty ← parseTerm
    return Term.mk (.ident ident) [ty]
  else
    return Term.mk (.ident ident) []
end

structure Command where
(cmd : String)
(args : List Term)
deriving Repr

def parseCommand : ParserM Command := do
  let cmd ← parseIdent
  match cmd with
  | "thf" | "tff" | "cnf" | "fof" =>
    parseToken (.op "(")
    let name ← parseIdent
    parseToken (.op ",")
    let kind ← parseIdent
    parseToken (.op ",")
    let val ← match kind with
    | "axiom" | "conjecture" | "hypothesis" => parseTerm
    | "type" => parseTypeDecl
    | _ => throw $ IO.userError s!"unknown declaration kind: {kind}"
    parseToken (.op ")")
    parseToken (.op ".")
    return ⟨cmd, [Term.mk (.ident name) [], Term.mk (.ident kind) [], val]⟩
  | "include" => throw $ IO.userError "includes are not yet implemented"
  | _ => throw $ IO.userError "Command '{cmd}' not supported"


partial def parseFile : ParserM (List Command) := do
  if ← isEOF 
  then return []
  else
    let c ← parseCommand
    return c :: (← parseFile)

def parse (s : String) : IO (List Command) := do
  let tokens ← Tokenizer.tokenize s
  let res ← parseFile.run {tokens}
  return res.1

open Tokenizer
#eval tokenize "(a)"


namespace Term

open Parser
open Lean
open Meta

#check MetavarContext.mkLambda

partial def toLeanExpr (t : Parser.Term) : MetaM Expr := do
  match t with
  | ⟨.ident "$i", []⟩ => return mkConst `Iota
  | ⟨.ident "$tType", []⟩ => return mkSort levelOne
  | ⟨.ident "$o", []⟩ => return mkSort levelZero
  | ⟨.ident "$true", []⟩ => return mkConst `True
  | ⟨.ident "$false", []⟩ => return mkConst `False
  | ⟨.ident n, as⟩ => do
    let some decl := (← getLCtx).findFromUserName? n
      | throwError "Unknown variable name {n}"
    return mkAppN (mkFVar decl.fvarId) (← as.mapM toLeanExpr).toArray
  | ⟨.op "!", body :: vars⟩ | ⟨.op "!>", body :: vars⟩ => 
    withLocalDeclsD (← makeLocalDecls body vars) fun vs => do
      mkForallFVars vs (← body.toLeanExpr)
  | ⟨.op "^", body :: vars⟩ =>
    withLocalDeclsD (← makeLocalDecls body vars) fun vs => do
      mkLambdaFVars vs (← body.toLeanExpr)
  | ⟨.op "?", body :: vars⟩ =>
    withLocalDeclsD (← makeLocalDecls body vars) fun vs => do
      let mut res ← body.toLeanExpr
      for v in vs.reverse do
        res ← mkAppM `Exists #[← mkLambdaFVars #[v] res]
      return res
  | ⟨.op "~", [a]⟩   => mkAppM `Not #[← a.toLeanExpr]
  | ⟨.op "|", as⟩   => mkAppM `Or (← as.mapM toLeanExpr).toArray
  | ⟨.op "&", as⟩   => mkAppM `And (← as.mapM toLeanExpr).toArray
  | ⟨.op "<=>", as⟩ => mkAppM `Iff (← as.mapM toLeanExpr).toArray
  | ⟨.op "!=", as⟩  => mkAppM `Ne (← as.mapM toLeanExpr).toArray
  | ⟨.op "=", as⟩   => mkAppM `Eq (← as.mapM toLeanExpr).toArray
  | ⟨.op "~|", as⟩  => mkAppM ``Not #[← mkAppM `Or (← as.mapM toLeanExpr).toArray]
  | ⟨.op "~&", as⟩  => mkAppM ``Not #[← mkAppM `And (← as.mapM toLeanExpr).toArray]
  | ⟨.op "<~>", as⟩ => mkAppM ``Not #[← mkAppM `Iff (← as.mapM toLeanExpr).toArray]
  | ⟨.op "@", [a,b]⟩ => return mkApp (← a.toLeanExpr) (← b.toLeanExpr)
  | ⟨.op "=>", [a,b]⟩ | ⟨.op "<=", [b,a]⟩ => mkArrow (← a.toLeanExpr) (← b.toLeanExpr)
  | ⟨.op ">", [⟨.op "*", [a, b]⟩, c]⟩   => toLeanExpr ⟨.op ">", [a, ⟨.op ">", [b, c]⟩]⟩
  | ⟨.op ">", [a, b]⟩ => mkArrow (← a.toLeanExpr) (← b.toLeanExpr)
  | _ => throwError "Could not translate to Lean Expr: {repr t}"
where
  makeLocalDecls (body : Term) (vars : List Term): MetaM (Array (Name × (Array Expr → MetaM Expr))) := do
    let decls : List (Name × (Array Expr → MetaM Expr)) ← vars.mapM fun var => do
      match var with
      | ⟨.ident v, ty⟩ =>
        let ty ← match ty with
        | [ty] => ty.toLeanExpr
        | [] => pure $ mkConst `Iota
        | _ => throwError "invalid bound var: {repr var}"
        return (v, fun (_ : Array Expr) => pure ty)
      | _ => throwError "invalid bound var: {repr var}"
    return decls.toArray

end Term

end Parser

open Parser
open Lean
open Meta

abbrev Formulas := Array (Expr × Expr × Array Name)

def compileCmds (cmds : List Parser.Command) (acc : Formulas) (k : Formulas → MetaM α): MetaM α := do
  match cmds with
  | ⟨cmd, args⟩ :: cs =>
    match cmd with
    | "thf" | "tff" | "cnf" | "fof" => 
      match args with
      | [_, ⟨.ident "type", _⟩, ⟨.ident id, [ty]⟩]  =>
        withLocalDeclD id (← ty.toLeanExpr) fun _ => do
          compileCmds cs acc k
      | [⟨.ident name, []⟩, ⟨.ident kind@"axiom", _⟩, val] 
      | [⟨.ident name, []⟩, ⟨.ident kind@"hypothesis", _⟩, val]
      | [⟨.ident name, []⟩, ⟨.ident kind@"conjecture", _⟩, val] =>
        let val ← val.toLeanExpr
        let val := if kind == "conjecture" then ← mkAppM ``Not #[val] else val
        withLocalDeclD ("H_" ++ name) val fun x => do
          let acc := acc.push (val, x, #[])
          compileCmds cs acc k
      | _ => throwError "Unknown declaration kind: {args.map repr}"
    | "include" => throwError "includes should have been unfolded first"
    | cmd => throwError "Unknown command: {cmd}"
  | [] => k acc

/-- Collect all constants (lower case variables) since these are not explicitly declared in FOF and CNF format. -/
partial def collectConstantsOfCmd (topLevel : Bool) (acc : HashMap String Expr) (t : Parser.Term): MetaM (HashMap String Expr) := do
  match t with
  | ⟨.ident n, as⟩ => do
    let acc ← as.foldlM (collectConstantsOfCmd false) acc
    if n.data[0]!.isLower && n.data[0]! != '$' && !acc.contains n
    then 
      let ty ← as.foldlM 
        (fun acc _ => mkArrow (mkConst `Iota) acc)
        (if topLevel then mkSort levelZero else mkConst `Iota)
      let acc := acc.insert n ty
      return acc
    else 
      return acc
  | ⟨.op "!", body :: _⟩ | ⟨.op "?", body :: _⟩ =>
    collectConstantsOfCmd topLevel acc body
  | ⟨.op "~", as⟩
  | ⟨.op "|", as⟩
  | ⟨.op "&", as⟩
  | ⟨.op "<=>", as⟩ 
  | ⟨.op "=>", as⟩ | ⟨.op "<=", as⟩ 
  | ⟨.op "~|", as⟩ 
  | ⟨.op "~&", as⟩  
  | ⟨.op "<~>", as⟩ => 
    as.foldlM (collectConstantsOfCmd topLevel) acc
  | ⟨.op "!=", as⟩ 
  | ⟨.op "=", as⟩ =>
    as.foldlM (collectConstantsOfCmd false) acc
  | _ => throwError "Failed to collect constants: {repr t}"

def collectCnfFofConstants (cmds : List Parser.Command) : MetaM (HashMap String Expr) := do
  let mut acc := HashMap.empty
  for cmd in cmds do
    match cmd with
    | ⟨"cnf", [_, _, val]⟩ | ⟨"fof", [_, _, val]⟩ =>
      acc ← collectConstantsOfCmd true acc val
    | _ => pure ()
  return acc


def compile [Inhabited α] (s : String) (k : Formulas → MetaM α) : MetaM α := do
  let cmds ← Parser.parse s
  let constants ← collectCnfFofConstants cmds
  withLocalDeclsD (constants.toArray.map fun (n, ty) => (n, fun _ => pure ty)) fun _ => do
    compileCmds cmds #[] k


elab "hello" : tactic => 
  compile "fof(goal_ax,axiom,
    ! [A] :
      ( ( reflexive_rewrite(b,A)
        & reflexive_rewrite(c,A) )
     => goal ) )."
    fun formulas => do
      for (x, _ , _) in formulas do
        logInfo m!"{x}"

example : False := by
  hello
  sorry


def toLeanExpr (s : String) : MetaM Expr := do
  let tokens ← Tokenizer.tokenize s
  let (t, _) ← parseTerm.run {tokens}
  let r ← t.toLeanExpr
  trace[Meta.debug] "{r}"
  return r

set_option trace.Meta.debug true
#eval toLeanExpr "?[a : $tType, b : $tType]: a = b"
#eval toLeanExpr "![x : $tType]: ![a : x]: a != a"
#eval toLeanExpr "$true != $true"
#eval toLeanExpr "$true & $true"

end TPTP