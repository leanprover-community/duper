import Lean

namespace Duper
open Std
open Lean
open Meta
open Core

/-- Applies beta and eta reduction exhaustively. -/
def betaEtaReduce (e : Expr) : MetaM Expr := do
  let e ← Core.betaReduce e
  match e.etaExpanded? with
  | some e => return e
  | none => return e

/-- Applies beta, eta, and zeta reduction exhaustively. I believe that by applying zeta reduction
    first, then beta reduction, and finally eta reduction, it is not necessary to iterate this
    function until a fixed point is reached (the output should always be a fixed point) -/
def betaEtaZetaReduce (e : Expr) : MetaM Expr := do
  let e ← Meta.zetaReduce e
  let e ← betaReduce e
  match e.etaExpanded? with
  | some e => return e
  | none => return e