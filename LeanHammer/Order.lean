import Lean

namespace Schroedinger
open Lean

inductive Comparison
| GreaterThan
| LessThan
| Equal
| Incomparable
deriving BEq

namespace Comparison

instance : ToMessageData Comparison := ⟨
  fun c => match c with
| GreaterThan => ">"
| LessThan => "<"
| Equal => "="
| Incomparable => "?"
⟩ 

end Comparison

namespace Order
open Lean.Meta
open Comparison

partial def weight (s : Expr) (w : Int := 0) (sign : Int) : MetaM Int := do
  trace[Meta.debug] "s: {s}" 
  s.withApp fun f ss =>
    match f with
    | Expr.fvar .. => do
      let mut w := w + sign * 1
      for u in ss do
        w ← weight u w sign
      return w
    | Expr.const .. => do
      let mut w := w + sign * 1
      for u in ss do
        w ← weight u w sign
      return w
    | Expr.mvar mVarId .. => do
      return w + sign * 1
    | _ => throwError "Not implemented"

partial def varBalance (s : Expr) (vb : Std.HashMap Expr Int := {}) (sign : Int) : MetaM (Std.HashMap Expr Int) := do
  trace[Meta.debug] "s: {s}" 
  s.withApp fun f ss =>
    match f with
    | Expr.fvar .. => do
      let mut vb := vb
      for u in ss do
        vb ← varBalance u vb sign
      return vb
    | Expr.const .. => do
      let mut vb := vb
      for u in ss do
        vb ← varBalance u vb sign
      return vb
    | Expr.mvar mVarId .. => do
      let vb := vb.insert s $ (← vb.findD s 0) + sign
      return vb
    | _ => throwError "Not implemented"

def compareVarBalance (vb : Std.HashMap Expr Int := {}) : MetaM Comparison := do
  let mut res := Equal
  for (v, b) in vb.toArray do
    if b > 0 then
      if res == LessThan then
        res := Incomparable
        break
      else
        res := GreaterThan
    else if b < 0 then
      if res == GreaterThan then
        res := Incomparable
        break
      else
        res := LessThan
  return res

-- TODO: Not quite KBO yet
def kbo (s t : Expr) : MetaM Comparison := do
  -- Core.checkMaxHeartbeats "kbo"
  if s == t then Equal
  else
    let wb : Int := 0
    let wb ← weight s wb 1
    let wb ← weight t wb (-1)
    let vb := {}
    let vb ← varBalance s vb 1
    let vb ← varBalance t vb (-1)
    trace[Meta.debug] "wb: {wb}"
    trace[Meta.debug] "vb: {vb.toArray}"
    let vbComparison ← compareVarBalance vb
    if wb > 0 ∧ (vbComparison == GreaterThan ∨ vbComparison == Equal) then
      GreaterThan
    else if wb < 0 ∧ (vbComparison == LessThan ∨ vbComparison == Equal) then
      LessThan
    else
      Incomparable


def test : MetaM Unit := do
  let ty := mkConst ``Nat
  let x ← mkFreshExprMVar ty
  let y ← mkFreshExprMVar ty
  let s := (mkConst ``Nat.zero)
  let t := mkApp (mkConst ``Nat.succ) x
  let res ← kbo s t
  trace[Meta.debug] "s: {s}"
  trace[Meta.debug] "t: {t}"
  trace[Meta.debug] "res: {res}"

set_option trace.Meta.debug true
#eval test

end Order

end Schroedinger