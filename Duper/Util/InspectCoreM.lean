import Lean

open Lean

namespace Duper

def antiquotedTokens (s : String) : Array String := Id.run <| do
  let mut ret := #[]
  let mut last : String.Pos := ⟨0⟩
  let mut curr : String.Pos := ⟨0⟩
  let mut last_antiquot : Bool := false
  while true do
    match s.get? curr with
    | some ch =>
      let curr' := curr
      curr := curr + ch
      if ¬ ch.isAlphanum ∧ ch != '_' then
        if curr != last + ch ∧ last_antiquot then
          ret := ret.push (s.extract last curr')
        last := curr
        last_antiquot := (ch == '`')
    | none => break
  return ret

def collectTokenFromLeanFile (path : String) : IO (Array String) := do
  let components := (⟨path⟩ : System.FilePath).components
  let syspath := System.mkFilePath components
  let file ← IO.FS.lines syspath
  let file := String.intercalate " " file.toList
  return antiquotedTokens file

def collectTokenFromLeanFolder (path : String) : IO (HashSet String) := do
  let entries ← System.FilePath.walkDir path
  let mut ret : HashSet String := HashSet.empty
  for entry in entries do
    if ← entry.isDir then
      continue
    if entry.extension != "lean" then
      continue
    let file ← IO.FS.lines entry
    let file := String.intercalate " " file.toList
    let arr := antiquotedTokens file
    for el in arr do
      ret := ret.insert el
  let list := ret.toList
  ret := HashSet.empty
  let mut exclude := HashSet.empty
  for entry in ["Lean", "Meta", "Array", "Option", "List", "Expr",
                "Match", "Bool", "Nat", "0", ""] do
    exclude := exclude.insert entry
  for entry in list do
    if ¬ exclude.contains entry then
      ret := ret.insert entry
  return ret

#eval HashSet.toList <$> collectTokenFromLeanFolder "Duper"

def Expr.findall (p : Expr → Bool) (e : Expr) : Array Expr :=
  /- This is a reference implementation for the unsafe one above -/
  if p e then
    #[e]
  else match e with
    | Expr.forallE _ d b _   => findall p d ++ findall p b
    | Expr.lam _ d b _       => findall p d ++ findall p b
    | Expr.mdata _ b         => findall p b
    | Expr.letE _ t v b _    => findall p t ++ findall p v ++ findall p b
    | Expr.app f a           => findall p f ++ findall p a
    | Expr.proj _ _ b        => findall p b
    | _                      => #[]

#check Expr.forallE `_ (Expr.const `Nat []) (.sort .zero) BinderInfo.default

-- Lean's "repr" does not deal with LevelMVarId correctly
partial def levelToMeta (l : Level) : String :=
  match l with
  | .zero => "Level.zero"
  | .succ l' => "Level.succ (" ++ levelToMeta l' ++ ")"
  | .max l1 l2 => "Level.max (" ++ levelToMeta l1 ++ ") (" ++ levelToMeta l2 ++ ")"
  | .imax l1 l2 => "Level.imax (" ++ levelToMeta l1 ++ ") (" ++ levelToMeta l2 ++ ")"
  | .param n => "Level.param `" ++ n.toString
  | .mvar id => "Level.mvar (LevelMVarId.mk `" ++ id.name.toString ++ ")"

-- Lean's "repr" does not deal with LevelMVarId correctly
partial def exprToMeta (e : Expr) : String :=
  match e with
  | Expr.forallE _ d b _ => "Expr.forallE `_ (" ++ exprToMeta d ++ ") (" ++ exprToMeta b ++ ") BinderInfo.default"
  | Expr.lam _ d b _ => "Expr.lam `_ (" ++ exprToMeta d ++ ") (" ++ exprToMeta b ++ ") BinderInfo.default"
  | Expr.mdata _ b => exprToMeta b
  | Expr.letE _ t v b _ => "Expr.letE `_ (" ++ exprToMeta t ++ ") (" ++ exprToMeta v ++ ") ("  ++ exprToMeta b ++ ") BinderInfo.default"
  | Expr.app f a => "Expr.app (" ++ exprToMeta f ++ ") (" ++ exprToMeta a ++ ")"
  | Expr.proj name idx b => "Expr.proj `" ++ name.toString ++ " " ++ idx.repr ++ " (" ++ exprToMeta b ++ ")"
  | Expr.const name us => "Expr.const `" ++ name.toString ++ " [" ++ String.intercalate ", " (us.map levelToMeta) ++ "]"
  | Expr.lit l =>
    match l with
    | .natVal l => "Expr.lit (Literal.natVal " ++ l.repr ++ ")"
    | .strVal s => "Expr.lit (Literal.strVal " ++ "\"" ++ s ++ "\"" ++ ")"
  | Expr.sort l => "Expr.sort (" ++ levelToMeta l ++ ")"
  | Expr.mvar id => "Expr.mvar (Lean.MVarId.mk " ++ id.name.toString ++ ")"
  | Expr.fvar id => "Expr.fvar (Lean.FVarId.mk " ++ id.name.toString ++ ")"
  | Expr.bvar n => "Expr.bvar " ++ n.repr

partial def add_name_to_closure (name : Name) (closure : HashSet Name) : CoreM (HashSet Name) := do
  if closure.contains name then
    return closure
  let mut ret := closure.insert name
  let decls := (← get).env.constants
  let ty := (decls.find! name).type
  let names := (Expr.findall (fun e => e.isConst) ty).map Expr.constName!
  for name in names do
    ret ← add_name_to_closure name ret
  return ret

#eval (do
  let res ← add_name_to_closure ``Nat.add_assoc HashSet.empty
  let res := res.toList
  IO.println res : CoreM _)

def inspectCoreM (filterpath : String) : CoreM (Array Name) := do
  let s ← get
  let constList := s.env.constants.toList
  let tokenset ← collectTokenFromLeanFolder filterpath
  let mut nameset : HashSet Name := HashSet.empty
  for (name, ci) in constList do
    let subs := Array.mk (name.toString.split (fun x => x == '.'))
    if subs.size == 0 then
      continue
    if subs.size >= 4 then
      continue
    if !tokenset.contains subs[subs.size - 1]! then
      continue
    let mut interesting := false
    if let .axiomInfo _ := ci then
      interesting := true
    if let .thmInfo _ := ci then
      interesting := true
    if ¬ interesting then
      continue
    nameset := nameset.insert name
  let mut nameset_closure : HashSet Name := HashSet.empty
  for name in nameset do
    nameset_closure ← add_name_to_closure name nameset_closure
  return nameset_closure.toArray

-- Lean's "repr" does not deal with LevelMVarId correctly
def constInfoToMeta (ci : ConstantInfo) : String :=
  let cv := ci.toConstantVal
  let name := cv.name.toString
  let levelParams := "[" ++ String.intercalate ", " (cv.levelParams.map (fun n => "`" ++ n.toString)) ++ "]"
  let ty := exprToMeta cv.type
  "Declaration.axiomDecl {name := `" ++ name ++ ", levelParams := " ++ levelParams ++ ", type := " ++ ty ++ ", isUnsafe := false}"
  
def addNamesToCoreM (funcname : String) (names : Array Name) : CoreM String := do
  let signature := "def " ++ funcname ++ " : CoreM Unit := do"
  let mut lines := #[]
  lines := lines.push "let mut env ← getEnv"
  let constmap := (← get).env.constants
  for name in names do
    let ci := constmap.find! name
    let line := "if let none := env.find? `" ++ name.toString ++ " then"
    lines := lines.push line
    let line := "  env ← ofExceptKernelException $ env.addDecl (" ++ constInfoToMeta ci ++ ")"
    lines := lines.push line
  lines := lines.push "setEnv env"
  let body := String.intercalate "\n  " lines.toList
  return signature ++ "\n  " ++ body

#eval do
  let str ← addNamesToCoreM "restoreCoreM" #[`Nat, `Nat.add_assoc, `Nat.brecOn]
  IO.println str