import Lean
open Lean

def List.subsequences (xs : List α) :=
  match xs with
  | nil => [nil]
  | cons a as => List.subsequences as ++ map (List.cons a) (List.subsequences as)

def MVarId.modifyLCtx (mvarId : MVarId) (lctx : LocalContext) : MetaM PUnit := do
  let decl ← mvarId.getDecl
  let decl' := {decl with lctx := lctx}
  let mctx := (← get).mctx
  let mctx' := {mctx with decls := mctx.decls.insert mvarId decl'}
  modify fun s => {s with mctx := mctx'}

instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

-- The following two functions are copied from Lean's
-- standard library. The only difference is that we
-- replace `whnf e` with `e`.
private partial def instantiateForallAux (ps : Array Expr) (i : Nat) (e : Expr) : MetaM Expr := do
  if h : i < ps.size then
    let p := ps.get ⟨i, h⟩
    match e with
    | Expr.forallE _ _ b _ => instantiateForallAux ps (i+1) (b.instantiate1 p)
    | _                => throwError "invalid instantiateForallNoReducing, too many parameters"
  else
    return e

def Lean.Expr.countLambdas : Expr → Nat
| lam _ _ b _  => countLambdas b + 1
| _            => 0

def Lean.Expr.countForalls : Expr → Nat
| forallE _ _ b _ => countForalls b + 1
| _               => 0

/-- Given `e` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `B[p_1, ..., p_n]`. -/
def Lean.Expr.instantiateForallNoReducing (e : Expr) (ps : Array Expr) : MetaM Expr :=
  instantiateForallAux ps 0 e

def Lean.Meta.findInstance (ty : Expr) : MetaM Expr := do
  let ty ← instantiateMVars ty
  forallTelescope ty fun xs ty' => do
    let u ← do
      if ty' == .sort (.succ .zero) then
        pure <| mkConst ``Nat
      else if let .sort (.succ l) := ty then
        pure <| mkSort l
      else try
        Meta.mkAppOptM ``inferInstanceAs #[ty', none]
      catch _ =>
        -- Find assumption in Local Context
        let ctx ← getLCtx
        let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
          let declExpr := decl.toExpr
          let declType ← Lean.Meta.inferType declExpr
          if ← Lean.Meta.isDefEq declType ty'
          then
            return Option.some declExpr
          else
            return Option.none
        match option_matching_expr with
        | some e => pure e
        | none => Meta.mkAppOptM ``default #[ty', none]
    mkLambdaFVars xs u

/-- Returns the arity of e -/
partial def getArity (e : Expr) : Nat :=
  match e.consumeMData with
  | Expr.forallE _ _ b _ => 1 + getArity b
  | _ => 0

/-- Abstracts occurences of `p` in `e`. Previously, `Meta.kabstract` was used for this purpose, but because
    `Meta.kabstract` invokes definitional equality, there were some instances in which `Meta.kabstract` performed
    an abstraction at a position where `RuleM.replace` would not perform a replacement. This was an issue because it
    created inconsistencies between the clauses produced by superposition's main code and proof reconstruction.
    
    `abstractAtExpr` is written to follow the implementation of `Meta.kabstract` without invoking definitional equality
    (instead testing for equality after instantiating metavariables).  -/
def Lean.Meta.abstractAtExpr (e : Expr) (p : Expr) (occs : Occurrences := .all) : MetaM Expr := do
  let e ← Lean.instantiateMVars e
  let p ← Lean.instantiateMVars p
  if p.isFVar && occs == Occurrences.all then
    return e.abstract #[p] -- Easy case
  else
    let pHeadIdx := p.toHeadIndex
    let pNumArgs := p.headNumArgs
    let rec visit (e : Expr) (offset : Nat) : StateRefT Nat MetaM Expr := do
      let visitChildren : Unit → StateRefT Nat MetaM Expr := fun _ => do
        match e with
        | .app f a         => return e.updateApp! (← visit f offset) (← visit a offset)
        | .mdata _ b       => return e.updateMData! (← visit b offset)
        | .proj _ _ b      => return e.updateProj! (← visit b offset)
        | .letE _ t v b _  => return e.updateLet! (← visit t offset) (← visit v offset) (← visit b (offset+1))
        | .lam _ d b _     => return e.updateLambdaE! (← visit d offset) (← visit b (offset+1))
        | .forallE _ d b _ => return e.updateForallE! (← visit d offset) (← visit b (offset+1))
        | e                => return e
      if e.hasLooseBVars then
        visitChildren ()
      else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
        visitChildren ()
      else if e == p then -- e and p have already had their metavariables instantiated at the beginning of abstrAtExpr
        let i ← get
        set (i+1)
        if occs.contains i then
          return mkBVar offset
        else
          visitChildren ()
      else
        visitChildren ()
    visit e 0 |>.run' 1