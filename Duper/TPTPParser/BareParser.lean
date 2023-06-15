
namespace TPTP

structure Context where
(input : String)

inductive TPTPType where
| type
| i
| o
| ident (s : String)
deriving Repr, Inhabited

inductive DeclKind where
| typeDecl
| axiomDecl
| conjectureDecl
deriving Repr, Inhabited

inductive TPTPParse where
| typeDecl (id : String) (type : TPTPParse)
| term (id : String) (type : TPTPType)
| ident : String → TPTPParse
| decl : String → DeclKind → TPTPParse → TPTPParse
| declKind : DeclKind → TPTPParse
| type : TPTPType → TPTPParse
| token : String → TPTPParse
| eqOp : TPTPParse → TPTPParse → TPTPParse → TPTPParse
deriving Repr, Inhabited

def TPTPParse.ident! : TPTPParse → String
| .ident str => str
| e => panic! s!"TPTPParse.ident! failed: {repr e}"

def TPTPParse.declKind! : TPTPParse → DeclKind
| .declKind ty => ty
| e => panic! s!"TPTPParse.declKind! failed: {repr e}"

structure State where
(pos : String.Pos := 0)
(stack : Array TPTPParse := #[])
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
    parseWhitespace c ⟨i, s.stack.push $ .ident name, s.error⟩ 
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
  {s with stack := s.stack.push elem}

partial def popStack (f : TPTPParse → Context → State → State) (c : Context) (s : State) : State :=
  f s.stack.back c {s with stack := s.stack.pop}

partial def shrinkStack (iniStackSz : Nat) (c : Context) (s : State) : State :=
  {s with stack := s.stack.shrink iniStackSz}

partial def modifyLatestStack (f : TPTPParse → TPTPParse) (c : Context) (s : State) : State :=
  popStack (fun e => pushStack (f e)) c s

partial def parseTokenAndPush (str : String) (c : Context) (s : State) : State :=
  let s := parseToken str c s
  if s.error.isNone then pushStack (.token str) c s else s

partial def parseDeclKind (c : Context) (s : State) : State :=
  alternatives #[
    parseToken "type" >> pushStack (.declKind .typeDecl),
    parseToken "axiom" >> pushStack (.declKind .axiomDecl),
    parseToken "conjecture" >> pushStack (.declKind .conjectureDecl)
  ] c s

partial def parseType (c : Context) (s : State) : State :=
  alternatives #[
    parseIdent >> modifyLatestStack fun e => (.type (.ident e.ident!)), -- TODO: modifyLatestStack
    parseToken "$type" >> pushStack (.type .type),
    parseToken "$i" >> pushStack (.type .i),
    parseToken "$o" >> pushStack (.type .o)
  ] c s

partial def parseTypeDecl (c : Context) (s : State) : State :=
  let iniStackSz := s.stack.size
  let s := (parseIdent >> parseToken ":" >> parseType) c s
  if s.error.isSome then s else
  let id :=  s.stack[iniStackSz + 0]!
  let type :=  s.stack[iniStackSz + 1]!
  let s := shrinkStack iniStackSz c s
  let s := pushStack (.typeDecl id.ident! type) c s
  s

def parseTerm (c : Context) (s : State) : State :=
  parseIdent c s

partial def parseThfDecl (c : Context) (s : State) : State :=
  let iniStackSz := s.stack.size
  let s := (parseToken "thf" >> parseToken "("
    >> parseIdent >> parseToken ","
    >> parseDeclKind >> parseToken ","
    >> alternatives #[parseTypeDecl, parseTerm] >> parseToken ")" >> parseToken ".") c s
  if s.error.isSome then s else
  let declName :=  s.stack[iniStackSz + 0]!
  let declKind :=  s.stack[iniStackSz + 1]!
  let declValue := s.stack[iniStackSz + 2]!
  let s := shrinkStack iniStackSz c s
  let s := pushStack (.decl declName.ident! declKind.declKind! declValue) c s
  s

def parseEqOp (c : Context) (s : State) : State :=
  let iniStackSz := s.stack.size
  let s := (
    parseTerm >>
    alternatives #[
      parseTokenAndPush "=",
      parseTokenAndPush "!="
    ] >>
    parseTerm
  ) c s
  if s.error.isSome then s else
  let term₁ :=  s.stack[iniStackSz + 0]!
  let op :=  s.stack[iniStackSz + 1]!
  let term₂ := s.stack[iniStackSz + 2]!
  let s := shrinkStack iniStackSz c s
  let s := pushStack (.eqOp op term₁ term₂) c s
  s


#eval parseEqOp ⟨"a != a"⟩ {} 
#eval parseThfDecl ⟨"thf(atype,type,a:$type)."⟩ {} 
#eval parseThfDecl ⟨"thf(atype,conjecture,a != a)."⟩ {} 

#eval sepBy "," parseIdent ⟨""⟩ {} 

#eval parseIdent ⟨"saassss"⟩ {} 
-- #eval (parseChar '(' >> parseIdent >> parseToken "s") ⟨"(s)"⟩ {} 

end TPTP