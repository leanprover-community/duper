import Lean

namespace Duper
open Std
open Lean
open Meta
open Core

/-- Applies beta and eta reduction exhaustively -/
partial def betaEtaReduce (e : Expr) : MetaM Expr := do
  let e' ← Core.betaReduce e
  match e'.etaExpanded? with
  | some e' =>
    if e' == e then return e
    else betaEtaReduce e'
  | none =>
    if e' == e then return e
    else betaEtaReduce e'

/-- This is the same as Core.betaReduce except that we set useZeta to true since we intend to zetaReduce as well -/
def betaReduce (e : Expr) : CoreM Expr :=
  transform e (pre := fun e => return if e.isHeadBetaTarget (useZeta := true) then .visit e.headBeta else .continue)

/-- Applies beta, eta, and zeta reduction exhaustively -/
partial def betaEtaZetaReduce (e : Expr) : MetaM Expr := do
  let e' ← betaReduce e
  let e' ← Meta.zetaReduce e'
  match e'.etaExpanded? with
  | some e' =>
    if e' == e then return e
    else betaEtaZetaReduce e'
  | none =>
    if e' == e then return e
    else betaEtaZetaReduce e'