

namespace TPTP

structure Context where
(input : String)

inductive DeclType where
| typeDecl
| axiomDecl
| conjectureDecl
deriving Repr

inductive TPTPType where
| type
| i
| o
| ident (s : String)
deriving Repr

inductive TPTPParse where
| ident : String → TPTPParse
| decl : DeclType → TPTPParse
| declType : DeclType → TPTPParse
| type : TPTPType → TPTPParse
deriving Repr

def TPTPParse.ident! : TPTPParse → String
| .ident str => str
| e => panic! s!"TPTPParse.ident! failed: {repr e}"

structure State where
(pos : String.Pos := 0)
(stack : List TPTPParse := [])
(error : Option String := none)
deriving Repr, Inhabited

def ParserM := ExceptT String id

partial def parseWhitespace (c : Context) (s : State) : State :=
  let rec go i :=
    if c.input.atEnd i then
      i
    else
      let char := c.input.get! i
      if char.isWhitespace then
        go (c.input.next i)
      else
        i
  let i := go s.pos
  ⟨i, s.stack, s.error⟩

partial def parseIdent (c : Context) (s : State) : State :=
  let rec go i acc :=
    if c.input.atEnd i then
      (i, acc)
    else
      let char := c.input.get! i
      if char.isAlpha then
        go (c.input.next i) (acc.push char)
      else
        (i, acc)
  let (i, name) := go s.pos ""
  if i > s.pos then
    parseWhitespace c ⟨i, .ident name :: s.stack, s.error⟩ 
  else 
    {s with error := "expected identifier"}

partial def seq (f1 f2 : Context → State → State) (c : Context) (s : State) : State :=
  let s := f1 c s
  if s.error.isSome then s else
  f2 c s

notation a ">>" b => seq a b

partial def parseToken (str : String) (c : Context) (s : State) : State :=
  if c.input.atEnd s.pos then
    {s with error := s!"expected '{str}', got end of string"}
  else Id.run do
    let mut s0 := s
    let mut read := ""
    for char in str.data do
      let curr := c.input.get! s0.pos
      read := read.push curr
      if curr == char then
        s0 := {s0 with pos := c.input.next s0.pos}
      else
        return {s0 with error := s!"expected '{str}', got '{read}'"}
    s0 := parseWhitespace c s0
    return s0

partial def sepBy (str : String) (f : Context → State → State) (c : Context) (s : State) : State :=
  let s1 := f c s
  if s1.error.isSome
  then s
  else
    let rec go s1 :=
      let s2 := (parseToken str >> f) c s1
      if s2.error.isSome then s1 else
      go s2
    go s1

partial def parseEOF (c : Context) (s : State) : State :=
  if c.input.atEnd s.pos then s
  else {s with error := s!"expected end of file, got {c.input.get! s.pos}"}

partial def alternatives (alts : Array (Context → State → State)) (c : Context) (s : State) : State := Id.run do
  let mut errors := #[]
  for alt in alts do
    let s := alt c s
    match s.error with
    | some err => errors := errors.push err
    | none => return s
  return {s with error := "No valid parse found:" ++ "\\n·".intercalate errors.toList}

partial def pushStack (elem : TPTPParse) (c : Context) (s : State) : State :=
  {s with stack := elem :: s.stack}

partial def parseThfDeclKind (c : Context) (s : State) : State :=
  alternatives #[
    parseToken "type" >> pushStack (.declType .typeDecl),
    parseToken "axiom" >> pushStack (.declType .axiomDecl),
    parseToken "conjecture" >> pushStack (.declType .conjectureDecl)
  ] c s

partial def popStack (f : TPTPParse → Context → State → State) (c : Context) (s : State) : State :=
  match s.stack with
  | a :: as => f a c {s with stack := as}
  | [] => panic! "popStack requires nonempty stack"

partial def modifyLatestStack (f : TPTPParse → TPTPParse) (c : Context) (s : State) : State :=
  popStack (fun e => pushStack (f e)) c s

partial def parseType (c : Context) (s : State) : State :=
  alternatives #[
    parseIdent >> modifyLatestStack fun e => (.type (.ident e.ident!)), -- TODO: modifyLatestStack
    parseToken "$type" >> pushStack (.type .type),
    parseToken "$i" >> pushStack (.type .i),
    parseToken "$o" >> pushStack (.type .o)
  ] c s

partial def parseTypeDecl (c : Context) (s : State) : State :=
  let s := (parseIdent >> parseToken ":" >> parseType) c s
  -- {s with stack := s.stack}
  s

partial def parseThfDecl (c : Context) (s : State) : State :=
  let s := (parseToken "thf" >> parseToken "(" >> parseIdent >> parseToken ","
    >> parseToken "type" >> parseToken "," >> parseTypeDecl >> parseToken ")") c s
  -- let s := (parseToken "thf" >> parseToken "(" >> parseIdent >> parseToken "," >> parseThfDeclKind >> parseToken "," >> parseToken ")") c s
  -- {s with stack := s.stack}
  s


#eval parseThfDeclKind ⟨"axiom"⟩ {} 
#eval parseThfDecl ⟨"thf(atype,type,a:t)"⟩ {} 

#eval sepBy ',' parseIdent ⟨""⟩ {} 

#eval parseIdent ⟨"saassss"⟩ {} 
#eval (parseChar '(' >> parseIdent >> parseChar ')') ⟨"(s)"⟩ {} 

end TPTP