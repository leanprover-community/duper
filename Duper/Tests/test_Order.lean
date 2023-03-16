import Duper.Order


namespace Duper.Order.Test
open Lean

opaque a : Nat
opaque b : Nat
opaque c : Nat
opaque f : Nat → Nat
opaque g : Nat → Nat → Nat

def consts := #[mkConst ``a, mkConst ``b, mkConst ``c]

partial def constructRandomExpr (fuel : Nat) : MetaM (Expr × Nat) := do
  let fuel := fuel - 1
  let i := if fuel == 0 then 0 else ← IO.rand 0 2
  if i == 0 then
    return (consts[← IO.rand 0 (consts.size - 1)]!, fuel)
  else if i == 1 then
    let (a, fuel) ← constructRandomExpr fuel
    return (mkApp (mkConst ``f) a, fuel)
  else
    let (a, fuel) ← constructRandomExpr fuel
    let (b, fuel) ← constructRandomExpr fuel
    return (mkApp2 (mkConst ``g) a b, fuel)
  

#eval show Elab.TermElabM _ from do
  for _ in [:10] do
    let (a, _) ← constructRandomExpr (fuel := 20)
    let (b, _) ← constructRandomExpr (fuel := 20)
    let cab ← kbo a b {} false
    let cba ← kbo b a {} false
    logInfo m!"{a}\n{cab}\n{b}"

    -- Check symmetry
    guard $ cab == cba.flip

end Duper.Order.Test