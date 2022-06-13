import Lean
import Duper.RuleM

/- This code is copied from Lean's Discrimination Trees, but the support for
definitional equality has been removed. -/

namespace Duper

open Lean
open RuleM

inductive Key where
  | const : Name → Nat → Key
  | fvar  : FVarId → Nat → Key
  | lit   : Literal → Key
  | star  : Key
  | other : Key
  | arrow : Key
  | proj  : Name → Nat → Key
  deriving Inhabited, BEq, Repr

protected def Key.hash : Key → UInt64
  | Key.const n a => mixHash 5237 $ mixHash (hash n) (hash a)
  | Key.fvar n a  => mixHash 3541 $ mixHash (hash n) (hash a)
  | Key.lit v     => mixHash 1879 $ hash v
  | Key.star      => 7883
  | Key.other     => 2411
  | Key.arrow     => 17
  | Key.proj s i  => mixHash 11 $ mixHash (hash s) (hash i)

instance : Hashable Key := ⟨Key.hash⟩

inductive Trie (α : Type) where
  | node (vs : Array α) (children : Array (Key × Trie α)) : Trie α

structure DiscrTree (α : Type) where
  root : Std.PersistentHashMap Key (Trie α) := {}

def Key.ctorIdx : Key → Nat
  | Key.star     => 0
  | Key.other    => 1
  | Key.lit ..   => 2
  | Key.fvar ..  => 3
  | Key.const .. => 4
  | Key.arrow    => 5
  | Key.proj ..  => 6

def Key.lt : Key → Key → Bool
  | Key.lit v₁,      Key.lit v₂      => v₁ < v₂
  | Key.fvar n₁ a₁,  Key.fvar n₂ a₂  => Name.quickLt n₁.name n₂.name || (n₁ == n₂ && a₁ < a₂)
  | Key.const n₁ a₁, Key.const n₂ a₂ => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | Key.proj s₁ i₁,  Key.proj s₂ i₂  => Name.quickLt s₁ s₂ || (s₁ == s₂ && i₁ < i₂)
  | k₁,              k₂              => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

def Key.format : Key → Format
  | Key.star                   => "*"
  | Key.other                  => "◾"
  | Key.lit (Literal.natVal v) => Std.format v
  | Key.lit (Literal.strVal v) => repr v
  | Key.const k _              => Std.format k
  | Key.proj s i               => Std.format s ++ "." ++ Std.format i
  | Key.fvar k _               => Std.format k.name
  | Key.arrow                  => "→"

instance : ToFormat Key := ⟨Key.format⟩

def Key.arity : Key → Nat
  | Key.const _ a => a
  | Key.fvar _ a  => a
  | Key.arrow     => 2
  | Key.proj ..   => 1
  | _             => 0

instance : Inhabited (Trie α) := ⟨Trie.node #[] #[]⟩


namespace DiscrTree

def empty : DiscrTree α := { root := {} }

partial def Trie.format [ToMessageData α] : Trie α → MessageData
  | Trie.node vs cs => MessageData.group $ MessageData.paren $
    "node" ++ (if vs.isEmpty then MessageData.nil else " " ++ toMessageData vs)
    ++ MessageData.joinSep (cs.toList.map $ fun ⟨k, c⟩ => MessageData.paren (toMessageData k ++ " => " ++ format c)) ","

instance [ToMessageData α] : ToMessageData (Trie α) := ⟨Trie.format⟩

partial def format [ToMessageData α] (d : DiscrTree α) : MessageData :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × MessageData) k c =>
      (false, p.2 ++ MessageData.paren (toMessageData k ++ " => " ++ toMessageData c)))
    (true, Format.nil)
  MessageData.group r

instance [ToMessageData α] : ToMessageData (DiscrTree α) := ⟨fun dt => format dt⟩

/- The discrimination tree ignores some implicit arguments and proofs.
   We use the following auxiliary id as a "mark". -/
private def tmpMVarId : MVarId := { name := `_discr_tree_tmp }
private def tmpStar := mkMVar tmpMVarId

instance : Inhabited (DiscrTree α) where
  default := {}

/--
  Return true iff the argument should be treated as a "wildcard" by the discrimination tree.

  - We ignore proofs because of proof irrelevance. It doesn't make sense to try to
    index their structure.

  - We ignore instance implicit arguments (e.g., `[Add α]`) because they are "morally" canonical.
    Moreover, we may have many definitionally equal terms floating around.
    Example: `Ring.hasAdd Int Int.isRing` and `Int.hasAdd`.

  - We considered ignoring implicit arguments (e.g., `{α : Type}`) since users don't "see" them,
    and may not even understand why some simplification rule is not firing.
    However, in type class resolution, we have instance such as `Decidable (@Eq Nat x y)`,
    where `Nat` is an implicit argument. Thus, we would add the path
    ```
    Decidable -> Eq -> * -> * -> * -> [Nat.decEq]
    ```
    to the discrimination tree IF we ignored the implict `Nat` argument.
    This would be BAD since **ALL** decidable equality instances would be in the same path.
    So, we index implicit arguments if they are types.
    This setting seems sensible for simplification lemmas such as:
    ```
    forall (x y : Unit), (@Eq Unit x y) = true
    ```
    If we ignore the implicit argument `Unit`, the `DiscrTree` will say it is a candidate
    simplification lemma for any equality in our goal.

  Remark: if users have problems with the solution above, we may provide a `noIndexing` annotation,
  and `ignoreArg` would return true for any term of the form `noIndexing t`.
-/
private def ignoreArg (a : Expr) (i : Nat) (infos : Array Meta.ParamInfo) : RuleM Bool := do
  if h : i < infos.size then
    let info := infos.get ⟨i, h⟩
    if info.isInstImplicit then
      return true
    else if info.isImplicit || info.isStrictImplicit then
      return not (← isType a)
    else
      isProof a
  else
    isProof a

private partial def pushArgsAux (infos : Array Meta.ParamInfo) : Nat → Expr → Array Expr → RuleM (Array Expr)
  | i, Expr.app f a _, todo => do
    if (← ignoreArg a i infos) then
      pushArgsAux infos (i-1) f (todo.push tmpStar)
    else
      pushArgsAux infos (i-1) f (todo.push a)
  | _, _, todo => return todo

def mkNoindexAnnotation (e : Expr) : Expr :=
  mkAnnotation `noindex e

def hasNoindexAnnotation (e : Expr) : Bool :=
  annotation? `noindex e |>.isSome

private def pushArgs (root : Bool) (todo : Array Expr) (e : Expr) : RuleM (Key × Array Expr) := do
  if hasNoindexAnnotation e then
    return (Key.star, todo)
  else
    let fn := e.getAppFn
    let push (k : Key) (nargs : Nat) : RuleM (Key × Array Expr) := do
      let info ← getFunInfoNArgs fn nargs
      let todo ← pushArgsAux info.paramInfo (nargs-1) e todo
      return (k, todo)
    match fn with
    | Expr.lit v _       => return (Key.lit v, todo)
    | Expr.const c _ _   =>
      let nargs := e.getAppNumArgs
      push (Key.const c nargs) nargs
    | Expr.proj s i a .. =>
      return (Key.proj s i, todo.push a)
    | Expr.fvar fvarId _ =>
      let nargs := e.getAppNumArgs
      push (Key.fvar fvarId nargs) nargs
    | Expr.mvar mvarId _ =>
      if mvarId == tmpMVarId then
        -- We use `tmp to mark some implicit arguments and proofs
        return (Key.star, todo)
      else
        return (Key.star, todo)
    | Expr.forallE _ d b _ =>
      if b.hasLooseBVars then
        return (Key.other, todo)
      else
        return (Key.arrow, todo.push d |>.push b)
    | _ =>
      return (Key.other, todo)

partial def mkPathAux (root : Bool) (todo : Array Expr) (keys : Array Key) : RuleM (Array Key) := do
  if todo.isEmpty then
    return keys
  else
    let e    := todo.back
    let todo := todo.pop
    let (k, todo) ← pushArgs root todo e
    mkPathAux false todo (keys.push k)

private def initCapacity := 8

def mkPath (e : Expr) : RuleM (Array Key) := do
  let todo : Array Expr := Array.mkEmpty initCapacity
  let keys : Array Key  := Array.mkEmpty initCapacity
  mkPathAux (root := true) (todo.push e) keys

private partial def createNodes (keys : Array Key) (v : α) (i : Nat) : Trie α :=
  if h : i < keys.size then
    let k := keys.get ⟨i, h⟩
    let c := createNodes keys v (i+1)
    Trie.node #[] #[(k, c)]
  else
    Trie.node #[v] #[]

private def insertVal [BEq α] (vs : Array α) (v : α) : Array α :=
  if vs.contains v then vs else vs.push v

private partial def insertAux [BEq α] (keys : Array Key) (v : α) : Nat → Trie α → Trie α
  | i, Trie.node vs cs =>
    if h : i < keys.size then
      let k := keys.get ⟨i, h⟩
      let c := Id.run $ cs.binInsertM
          (fun a b => a.1 < b.1)
          (fun ⟨_, s⟩ => let c := insertAux keys v (i+1) s; (k, c)) -- merge with existing
          (fun _ => let c := createNodes keys v (i+1); (k, c))
          (k, default)
      Trie.node vs c
    else
      Trie.node (insertVal vs v) cs

def insertCore [BEq α] (d : DiscrTree α) (keys : Array Key) (v : α) : DiscrTree α :=
  if keys.isEmpty then panic! "invalid key sequence"
  else
    let k := keys[0]
    match d.root.find? k with
    | none =>
      let c := createNodes keys v 1
      { root := d.root.insert k c }
    | some c =>
      let c := insertAux keys v 1 c
      { root := d.root.insert k c }

def insert [BEq α] (d : DiscrTree α) (e : Expr) (v : α) : RuleM (DiscrTree α) := do
  let keys ← mkPath e
  return d.insertCore keys v

private def getKeyArgs (e : Expr) (isMatch root : Bool) : RuleM (Key × Array Expr) := do
  match e.getAppFn with
  | Expr.lit v _       => return (Key.lit v, #[])
  | Expr.const c _ _   =>
    let nargs := e.getAppNumArgs
    return (Key.const c nargs, e.getAppRevArgs)
  | Expr.fvar fvarId _ =>
    let nargs := e.getAppNumArgs
    return (Key.fvar fvarId nargs, e.getAppRevArgs)
  | Expr.mvar mvarId _ =>
    if isMatch then
      return (Key.other, #[])
    else do
      return (Key.star, #[])
  | Expr.proj s i a .. =>
    return (Key.proj s i, #[a])
  | Expr.forallE _ d b _ =>
    if b.hasLooseBVars then
      return (Key.other, #[])
    else
      return (Key.arrow, #[d, b])
  | _ =>
    return (Key.other, #[])

private abbrev getMatchKeyArgs (e : Expr) (root : Bool) : RuleM (Key × Array Expr) :=
  getKeyArgs e (isMatch := true) (root := root)

private abbrev getUnifyKeyArgs (e : Expr) (root : Bool) : RuleM (Key × Array Expr) :=
  getKeyArgs e (isMatch := false) (root := root)

private def getStarResult (d : DiscrTree α) : Array α :=
  let result : Array α := Array.mkEmpty initCapacity
  match d.root.find? Key.star with
  | none                  => result
  | some (Trie.node vs _) => result ++ vs

private abbrev findKey (cs : Array (Key × Trie α)) (k : Key) : Option (Key × Trie α) :=
  cs.binSearch (k, default) (fun a b => a.1 < b.1)

private partial def getMatchLoop (todo : Array Expr) (c : Trie α) (result : Array α) : RuleM (Array α) := do
  match c with
  | Trie.node vs cs =>
    if todo.isEmpty then
      return result ++ vs
    else if cs.isEmpty then
      return result
    else
      let e     := todo.back
      let todo  := todo.pop
      let first := cs[0] /- Recall that `Key.star` is the minimal key -/
      let (k, args) ← getMatchKeyArgs e (root := false)
      /- We must always visit `Key.star` edges since they are wildcards.
         Thus, `todo` is not used linearly when there is `Key.star` edge
         and there is an edge for `k` and `k != Key.star`. -/
      let visitStar (result : Array α) : RuleM (Array α) :=
        if first.1 == Key.star then
          getMatchLoop todo first.2 result
        else
          return result
      let visitNonStar (k : Key) (args : Array Expr) (result : Array α) : RuleM (Array α) :=
        match findKey cs k with
        | none   => return result
        | some c => getMatchLoop (todo ++ args) c.2 result
      let result ← visitStar result
      match k with
      | Key.star  => return result
      /-
        Recall that dependent arrows are `(Key.other, #[])`, and non-dependent arrows are `(Key.arrow, #[a, b])`.
        A non-dependent arrow may be an instance of a dependent arrow (stored at `DiscrTree`). Thus, we also visit the `Key.other` child.
      -/
      | Key.arrow => visitNonStar Key.other #[] (← visitNonStar k args result)
      | _         => visitNonStar k args result

private def getMatchRoot (d : DiscrTree α) (k : Key) (args : Array Expr) (result : Array α) : RuleM (Array α) :=
  match d.root.find? k with
  | none   => return result
  | some c => getMatchLoop args c result

/--
  Find values that match `e` in `d`.
-/
partial def getMatch (d : DiscrTree α) (e : Expr) : RuleM (Array α) := do
  Core.checkMaxHeartbeats "getMatch"
  let result := getStarResult d
  let (k, args) ← getMatchKeyArgs e (root := true)
  match k with
  | Key.star => return result
  | _        => getMatchRoot d k args result

partial def getUnify (d : DiscrTree α) (e : Expr) : RuleM (Array α) := do
  Core.checkMaxHeartbeats "getUnify"
  let (k, args) ← getUnifyKeyArgs e (root := true)
  match k with
  | Key.star => d.root.foldlM (init := #[]) fun result k c => process k.arity #[] c result
  | _ =>
    let result := getStarResult d
    match d.root.find? k with
    | none   => return result
    | some c => process 0 args c result
where
  process (skip : Nat) (todo : Array Expr) (c : Trie α) (result : Array α) : RuleM (Array α) := do
    match skip, c with
    | skip+1, Trie.node vs cs =>
      if cs.isEmpty then
        return result
      else
        cs.foldlM (init := result) fun result ⟨k, c⟩ => process (skip + k.arity) todo c result
    | 0, Trie.node vs cs => do
      if todo.isEmpty then
        return result ++ vs
      else if cs.isEmpty then
        return result
      else
        let e     := todo.back
        let todo  := todo.pop
        let (k, args) ← getUnifyKeyArgs e (root := false)
        let visitStar (result : Array α) : RuleM (Array α) :=
          let first := cs[0]
          if first.1 == Key.star then
            process 0 todo first.2 result
          else
            return result
        let visitNonStar (k : Key) (args : Array Expr) (result : Array α) : RuleM (Array α) :=
          match findKey cs k with
          | none   => return result
          | some c => process 0 (todo ++ args) c.2 result
        match k with
        | Key.star  => cs.foldlM (init := result) fun result ⟨k, c⟩ => process k.arity todo c result
        -- See comment a `getMatch` regarding non-dependent arrows vs dependent arrows
        | Key.arrow => visitNonStar Key.other #[] (← visitNonStar k args (← visitStar result))
        | _         => visitNonStar k args (← visitStar result)

end DiscrTree
end Duper



