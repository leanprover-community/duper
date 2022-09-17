import Lean
import Duper.RuleM

namespace Duper

open Lean
open RuleM
open Std

initialize Lean.registerTraceClass `Fingerprint.debug

inductive FingerprintFeatureValue where
  | F : Expr → FingerprintFeatureValue
  | A : FingerprintFeatureValue
  | B : FingerprintFeatureValue
  | N : FingerprintFeatureValue

def FingerprintFeatureValue.format : FingerprintFeatureValue → MessageData
  | A => "A"
  | B => "B"
  | N => "N"
  | F e => m!"F({e})"

instance : ToMessageData (FingerprintFeatureValue) := ⟨FingerprintFeatureValue.format⟩

abbrev Fingerprint := List FingerprintFeatureValue

inductive FingerprintTrie (α : Type) [BEq α] [Hashable α] where
  | node
      (childA : FingerprintTrie α) (childB : FingerprintTrie α)
      (childN : FingerprintTrie α) (childF : Array (Expr × FingerprintTrie α)) : FingerprintTrie α
  | leaf (vals : HashSet α)
deriving Inhabited

def FingerprintTrie.format [ToMessageData α] [BEq α] [Hashable α] : FingerprintTrie α → MessageData
  | _ => sorry

def FingerprintTrie.formatClause [BEq α] [Hashable α] :
  FingerprintTrie (Clause × α) → MessageData
  | _ => sorry

instance [ToMessageData α] [BEq α] [Hashable α] : ToMessageData (FingerprintTrie α) := ⟨FingerprintTrie.format⟩
instance [BEq α] [Hashable α] : ToMessageData (FingerprintTrie (Clause × α)) := ⟨FingerprintTrie.formatClause⟩

abbrev ClauseFingerprintTrie := FingerprintTrie (Clause × ClausePos)

/- The filterSet argument is a hack to simulate deletions from the FingerprintTrie. I currently think that this might
   be not only easier, but also more efficient than actually deleting all entries relating to a particular clause, but
   I could be quite off-base on that. -/
structure RootCFPTrie where
  root : ClauseFingerprintTrie := FingerprintTrie.leaf {}
  filterSet : Std.HashSet Clause := {} -- Keeps track of the set of clauses that should be filtered out (i.e. "removed" clauses)

open FingerprintTrie
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

/-- Fingerprint features that will define levels of the fingerprint trie. The current value is just what is described
    in (http://www.eprover.eu/EXPDATA/FP_INDEX/schulz_fp-index_ext.pdf). Finding an actually good fingerprint function
    is an item in TODO.md -/
def fingerprintFeatures : List ExprPos := [
  #[],
  #[0],
  #[1]
]

/-- Every ClauseFingerprintTrie (that isn't a subtrie of a different ClauseFingerprintTrie) must have a depth equal
    to numFingerprintFeatures -/
def numFingerprintFeatures : Nat := fingerprintFeatures.length

def getFingerprint (e : Expr) : Fingerprint :=
  fingerprintFeatures.map (fun pos => gfpf e pos)

/-- Yields an empty ClauseFingerprintTrie with the given depth d -/
def mkEmptyWithDepth (d : Nat) : ClauseFingerprintTrie :=
  match d with
  | 0 => leaf {}
  | d' + 1 =>
    let t := mkEmptyWithDepth d'
    node t t t #[]

/-- Yields an empty ClauseFingerprintTrie with the correct depth -/
def empty : ClauseFingerprintTrie := mkEmptyWithDepth numFingerprintFeatures

/-- Given a fingerprint f, yields a ClauseFingerprintTrie whose depth equals the length of f and whose
    only value is v (located at the position indicated by f) -/
def mkSingleton (f : Fingerprint) (v : (Clause × ClausePos)) : ClauseFingerprintTrie :=
  let childDepth := f.length - 1
  let emptyChild := mkEmptyWithDepth childDepth
  match f with
  | [] => leaf (HashSet.empty.insert v)
  | A :: restFeatures => node (mkSingleton restFeatures v) emptyChild emptyChild #[]
  | B :: restFeatures => node emptyChild (mkSingleton restFeatures v) emptyChild #[]
  | N :: restFeatures => node emptyChild emptyChild (mkSingleton restFeatures v) #[]
  | F e :: restFeatures => node emptyChild emptyChild emptyChild #[(e, mkSingleton restFeatures v)]

/-- Inserts v into t at the position indicated by fingerprint f.
    Throws an error if the length of f does not equal the depth of t -/
def insertHelper (t : ClauseFingerprintTrie) (f : Fingerprint)
  (v : (Clause × ClausePos)) : RuleM ClauseFingerprintTrie := do
  match f, t with
  | [], leaf vals => return leaf (vals.insert v)
  | [], _ => throwError "Depth of {t} incompatible with length of {f}"
  | A :: restFeatures, node childA childB childN childF =>
    let childA' ← insertHelper childA restFeatures v
    return node childA' childB childN childF
  | B :: restFeatures, node childA childB childN childF =>
    let childB' ← insertHelper childB restFeatures v
    return node childA childB' childN childF
  | N :: restFeatures, node childA childB childN childF =>
    let childN' ← insertHelper childN restFeatures v
    return node childA childB childN' childF
  | F e :: restFeatures, node childA childB childN childF =>
    match childF.findIdx? (fun (exp, _) => e == exp) with
    | none =>
      let childF' := childF.push (e, mkSingleton restFeatures v)
      return node childA childB childN childF'
    | some idx =>
      let (_, eChild) := childF[idx]!
      let eChild' ← insertHelper eChild restFeatures v
      let childF' := childF.set! idx (e, eChild')
      return node childA childB childN childF'
  | _, _ => throwError "Depth of {t} incompatible with length of {f}"

def insert (t : RootCFPTrie) (e : Expr) (v : (Clause × ClausePos)) : RuleM RootCFPTrie :=
  return ⟨← insertHelper t.root (getFingerprint e) v, t.filterSet⟩

def delete (t : RootCFPTrie) (c : Clause) : RuleM RootCFPTrie :=
  return ⟨t.root, t.filterSet.insert c⟩

/-- Returns all clause and position pairs that indicate subexpressions that may be unifiable with e -/
def getUnificationPartners (t : RootCFPTrie) (e : Expr) : RuleM (HashSet (Clause × ClausePos)) :=
  sorry

/-- Returns all clause and position pairs that indicate subexpressions that e can match onto
    (i.e. assigning metavariables in e) -/
def getMatchOntoPartners (t : RootCFPTrie) (e : Expr) : RuleM (HashSet (Clause × ClausePos)) :=
  sorry

/-- Returns all clause and position pairs that indicate subexpressions that can be matched onto e
    (i.e. not assigning metavariables in e) -/
def getMatchFromPartners (t : RootCFPTrie) (e : Expr) : RuleM (HashSet (Clause × ClausePos)) :=
  sorry