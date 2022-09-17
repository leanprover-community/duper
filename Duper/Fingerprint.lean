import Lean
import Duper.RuleM

namespace Duper

open Lean
open RuleM

initialize Lean.registerTraceClass `Fingerprint.debug

inductive FingerprintFeatureValue where
  | F : Expr → FingerprintFeatureValue
  | A : FingerprintFeatureValue
  | B : FingerprintFeatureValue
  | N : FingerprintFeatureValue

open FingerprintFeatureValue

/-- General fingerprint feature function (see: http://www.eprover.eu/EXPDATA/FP_INDEX/schulz_fp-index_ext.pdf) 
    Note that this function assumes that e already has had its metavariables instantiated -/
def gfpf (e : Expr) (pos : ExprPos) : FingerprintFeatureValue :=
  match e.getAtPos? pos with
  | none =>
    if e.canInstantiateToGetAtPos pos then B
    else N
  | some e' =>
    if e'.isMVar then A
    else F e.getTopSymbol

-- Given by Fig. 1 of http://www.eprover.eu/EXPDATA/FP_INDEX/schulz_fp-index_ext.pdf
def featureValuesCompatibleForUnification (v1 : FingerprintFeatureValue) (v2 : FingerprintFeatureValue) : Bool :=
  match v1, v2 with
  | F e1, F e2 => e1 == e2
  | F _, A => true
  | F _, B => true
  | F _, N => false
  | A, F _ => true
  | A, A => true
  | A, B => true
  | A, N => false
  | B, F _ => true
  | B, A => true
  | B, B => true
  | B, N => true
  | N, F _ => false
  | N, A => false
  | N, B => true
  | N, N => true

/-- Returns false if an expression with fingerprint feature value v1 cannot be matched onto to any expression with
    fingerprint feature value v2 (i.e. there is no substitution σ such that σ(e1) = e2) -/
def featureValuesCompatibleForMatching (v1 : FingerprintFeatureValue) (v2 : FingerprintFeatureValue) : Bool :=
  match v1, v2 with
  | F e1, F e2 => e1 == e2
  | F _, _ => false
  | A, F _ => true
  | A, A => true
  | A, B => false
  | A, N => false
  | B, _ => true
  | N, N => true
  | N, _ => false