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
  | leaf (vals : Array α)
deriving Inhabited

abbrev ClauseFingerprintTrie := FingerprintTrie (Clause × ClausePos)

open FingerprintTrie
open FingerprintFeatureValue

-- Print functions ----------------------------------------------------------------------------------------
partial def FingerprintTrie.format [ToMessageData α] [BEq α] [Hashable α] : FingerprintTrie α → MessageData
  | leaf vals => m!"leaf({vals})"
  | node childA childB childN childF =>
    let childFMsg := childF.foldl (fun acc (e, t) => acc ++ m!"({e}, {t.format}), ") m!""
    let childFMsg := m!"childF: {childFMsg}"
    m!"node with:\nchildA:{childA.format}\nchildB:{childB.format}\nchildN:{childN.format}\n" ++ childFMsg

partial def countElems [BEq α] [Hashable α] : FingerprintTrie α → Nat
  | leaf vals => vals.size
  | node childA childB childN childF =>
    let childFElems := childF.foldl (fun acc (_, t) => acc + countElems t) 0
    countElems childA + countElems childB + countElems childN + childFElems

def foldMsgs (arr : Array MessageData) : MessageData := arr.foldl (fun acc m => acc ++ m!"\n" ++ m) m!""

private partial def printElemsHelper [ToMessageData α] [BEq α] [Hashable α] : FingerprintTrie α → Array MessageData
  | leaf vals => vals.map (fun x => m!": {x}")
  | node childA childB childN childF =>
    let childAMsgs := (printElemsHelper childA).map (fun m => m!"A" ++ m)
    let childBMsgs := (printElemsHelper childB).map (fun m => m!"B" ++ m)
    let childNMsgs := (printElemsHelper childN).map (fun m => m!"N" ++ m)
    let childFMsgs := childF.map (fun (e, t) => (printElemsHelper t).map (fun m => m!"F({e})" ++ m))
    let childFMsgs := childFMsgs.map foldMsgs
    ((childAMsgs.append childBMsgs).append childNMsgs).append childFMsgs

def FingerprintTrie.printElems [ToMessageData α] [BEq α] [Hashable α] (t : FingerprintTrie α) : MessageData :=
  foldMsgs $ printElemsHelper t

instance [ToMessageData α] [BEq α] [Hashable α] : ToMessageData (FingerprintTrie α) :=
  ⟨FingerprintTrie.printElems⟩
-----------------------------------------------------------------------------------------------------------

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

/-- Yields an empty ClauseFingerprintTrie with the given depth d -/
def mkEmptyWithDepth (d : Nat) : ClauseFingerprintTrie :=
  match d with
  | 0 => leaf {}
  | d' + 1 =>
    let t := mkEmptyWithDepth d'
    node t t t #[]

/-- Yields an empty ClauseFingerprintTrie with the correct depth -/
def empty : ClauseFingerprintTrie := mkEmptyWithDepth numFingerprintFeatures

/- The filterSet argument is a hack to simulate deletions from the FingerprintTrie. I currently think that this might
   be not only easier, but also more efficient than actually deleting all entries relating to a particular clause, but
   I could be quite off-base on that. -/
structure RootCFPTrie where
  root : ClauseFingerprintTrie := empty
  filterSet : HashSet Clause := {} -- Keeps track of the set of clauses that should be filtered out (i.e. "removed" clauses)
deriving Inhabited

namespace RootCFPTrie

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

def getFingerprint (e : Expr) : Fingerprint :=
  fingerprintFeatures.map (fun pos => gfpf e pos)

/-- Given a fingerprint f, yields a ClauseFingerprintTrie whose depth equals the length of f and whose
    only value is v (located at the position indiced by f) -/
def mkSingleton (f : Fingerprint) (v : (Clause × ClausePos)) : ClauseFingerprintTrie :=
  let childDepth := f.length - 1
  let emptyChild := mkEmptyWithDepth childDepth
  match f with
  | [] => leaf #[v]
  | A :: restFeatures => node (mkSingleton restFeatures v) emptyChild emptyChild #[]
  | B :: restFeatures => node emptyChild (mkSingleton restFeatures v) emptyChild #[]
  | N :: restFeatures => node emptyChild emptyChild (mkSingleton restFeatures v) #[]
  | F e :: restFeatures => node emptyChild emptyChild emptyChild #[(e, mkSingleton restFeatures v)]

/-- Inserts v into t at the position indiced by fingerprint f.
    Throws an error if the length of f does not equal the depth of t -/
def insertHelper (t : ClauseFingerprintTrie) (f : Fingerprint)
  (v : (Clause × ClausePos)) : RuleM ClauseFingerprintTrie := do
  match f, t with
  | [], leaf vals => return leaf (vals.push v)
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

/-- Adds v to t.root at the location indiced by e and removes v.1 from t.filterSet so that previously
    deleted clauses can be readded -/
def insert (t : RootCFPTrie) (e : Expr) (v : (Clause × ClausePos)) : RuleM RootCFPTrie :=
  return ⟨← insertHelper t.root (getFingerprint e) v, t.filterSet.erase v.1⟩

/-- Adds c to t.filterSet so that Clause × ClausePos pairs with c as the clause are ignored going forward -/
def delete (t : RootCFPTrie) (c : Clause) : RuleM RootCFPTrie :=
  return ⟨t.root, t.filterSet.insert c⟩

/-- Obtains all values in t that are unification-compatible with f. Throws an error if the depth of t is not
    equal to the length of f -/
private def getUnificationPartnersHelper (t : ClauseFingerprintTrie) (f : Fingerprint) :
  RuleM (Array (Clause × ClausePos)) := do
  match f, t with
  | [], leaf vals => return vals
  | A :: restFeatures, node childA childB childN childF =>
    let arrA ← getUnificationPartnersHelper childA restFeatures
    let arrB ← getUnificationPartnersHelper childB restFeatures
    let arrF ← childF.foldlM
      (fun acc (_, child) => return acc.append $ ← getUnificationPartnersHelper child restFeatures) #[]
    return (arrF.append arrA).append arrB
  | B :: restFeatures, node childA childB childN childF =>
    let arrA ← getUnificationPartnersHelper childA restFeatures
    let arrB ← getUnificationPartnersHelper childB restFeatures
    let arrN ← getUnificationPartnersHelper childN restFeatures
    let arrF ← childF.foldlM
      (fun acc (_, child) => return acc.append $ ← getUnificationPartnersHelper child restFeatures) #[]
    return ((arrF.append arrA).append arrB).append arrN
  | N :: restFeatures, node childA childB childN childF =>
    let arrB ← getUnificationPartnersHelper childB restFeatures
    let arrN ← getUnificationPartnersHelper childN restFeatures
    return arrB.append arrN
  | F e :: restFeatures, node childA childB childN childF =>
    let arrA ← getUnificationPartnersHelper childA restFeatures
    let arrB ← getUnificationPartnersHelper childB restFeatures
    match childF.find? (fun (exp, _) => e == exp) with
    | none => return arrA.append arrB
    | some (_, eChild) =>
      let arrF ← getUnificationPartnersHelper eChild restFeatures
      return (arrF.append arrA).append arrB
  | _, _ => throwError "Depth of {t} incompatible with length of {f}"

/-- Returns all clause and position pairs that indicate subexpressions that may be unifiable with e -/
def getUnificationPartners (t : RootCFPTrie) (e : Expr) : RuleM (Array (Clause × ClausePos)) := do
  trace[Fingerprint.debug] "About to call getUnificationPartnersHelper with {t.root} and {getFingerprint e}"
  let unfilteredRes ← getUnificationPartnersHelper t.root (getFingerprint e)
  trace[Fingerprint.debug] "Unfiltered result from getUnificationPartners {e}: {unfilteredRes}"
  trace[Fingerprint.debug] "{e} fingerprint: {getFingerprint e}"
  trace[Fingerprint.debug] "Current RootCFPTrie: {t.root}"
  return Array.filter (fun c => not (t.filterSet.contains c.1)) unfilteredRes

private def getMatchOntoPartnersHelper (t : ClauseFingerprintTrie) (f : Fingerprint) :
  RuleM (Array (Clause × ClausePos)) := do
  match f, t with
  | [], leaf vals => return vals
  | A :: restFeatures, node childA childB childN childF =>
    let arrA ← getMatchOntoPartnersHelper childA restFeatures
    let arrF ← childF.foldlM
      (fun acc (_, child) => return acc.append $ ← getMatchOntoPartnersHelper child restFeatures) #[]
    return arrF.append arrA
  | B :: restFeatures, node childA childB childN childF =>
    let arrA ← getMatchOntoPartnersHelper childA restFeatures
    let arrB ← getMatchOntoPartnersHelper childB restFeatures
    let arrN ← getMatchOntoPartnersHelper childN restFeatures
    let arrF ← childF.foldlM
      (fun acc (_, child) => return acc.append $ ← getMatchOntoPartnersHelper child restFeatures) #[]
    return ((arrF.append arrA).append arrB).append arrN
  | N :: restFeatures, node childA childB childN childF =>
    let arrN ← getMatchOntoPartnersHelper childN restFeatures
    return arrN
  | F e :: restFeatures, node childA childB childN childF =>
    match childF.find? (fun (exp, _) => e == exp) with
    | none => return #[]
    | some (_, eChild) => getMatchOntoPartnersHelper eChild restFeatures
  | _, _ => throwError "Depth of {t} incompatible with length of {f}"

/-- Returns all clause and position pairs that indicate subexpressions that e can match onto
    (i.e. assigning metavariables in e) -/
def getMatchOntoPartners (t : RootCFPTrie) (e : Expr) : RuleM (Array (Clause × ClausePos)) := do
  let unfilteredRes ← getMatchOntoPartnersHelper t.root (getFingerprint e)
  return Array.filter (fun c => not (t.filterSet.contains c.1)) unfilteredRes

private def getMatchFromPartnersHelper (t : ClauseFingerprintTrie) (f : Fingerprint) :
  RuleM (Array (Clause × ClausePos)) := do
  match f, t with
  | [], leaf vals => return vals
  | A :: restFeatures, node childA childB childN childF =>
    let arrA ← getMatchFromPartnersHelper childA restFeatures
    let arrB ← getMatchFromPartnersHelper childB restFeatures
    return arrA.append arrB
  | B :: restFeatures, node childA childB childN childF =>
    let arrB ← getMatchFromPartnersHelper childB restFeatures
    return arrB
  | N :: restFeatures, node childA childB childN childF =>
    let arrB ← getMatchFromPartnersHelper childB restFeatures
    let arrN ← getMatchOntoPartnersHelper childN restFeatures
    return arrB.append arrN
  | F e :: restFeatures, node childA childB childN childF =>
    let arrA ← getMatchFromPartnersHelper childA restFeatures
    let arrB ← getMatchFromPartnersHelper childB restFeatures
    match childF.find? (fun (exp, _) => e == exp) with
    | none => return arrA.append arrB
    | some (_, eChild) =>
      let arrF ← getMatchFromPartnersHelper eChild restFeatures
      return (arrF.append arrA).append arrB
  | _, _ => throwError "Depth of {t} incompatible with length of {f}"

/-- Returns all clause and position pairs that indicate subexpressions that can be matched onto e
    (i.e. not assigning metavariables in e) -/
def getMatchFromPartners (t : RootCFPTrie) (e : Expr) : RuleM (Array (Clause × ClausePos)) := do
  let unfilteredRes ← getMatchFromPartnersHelper t.root (getFingerprint e)
  return Array.filter (fun c => not (t.filterSet.contains c.1)) unfilteredRes