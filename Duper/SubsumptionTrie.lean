import Lean
import Std
import Duper.RuleM

namespace Duper

open Lean
open RuleM
open Std
open List
open Expr

initialize Lean.registerTraceClass `SubsumptionTrie.debug

abbrev Feature := Nat

def featureLt (f1 : Feature) (f2 : Feature) : Bool := f1 < f2
def featureEq (f1 : Feature) (f2 : Feature) : Bool := f1 = f2

/-
  Data structure for feature vector indexing:
  https://www.researchgate.net/publication/228724593_Simple_and_Efficient_Clause_Subsumption_with_Feature_Vector_Indexing
-/
inductive SubsumptionTrie where
  | node (children : Array (Feature × SubsumptionTrie)) : SubsumptionTrie
  | leaf (vals : HashSet Clause) : SubsumptionTrie
deriving Inhabited

namespace SubsumptionTrie

-- Print functions -----------------------------------------------------------------------------------------------------------------
partial def format : SubsumptionTrie → MessageData
  | node children =>
    MessageData.group $ MessageData.paren $
      "node" ++ MessageData.joinSep (children.toList.map $ fun ⟨k, c⟩ => MessageData.paren (toMessageData k ++ " => " ++ format c)) ","
  | leaf vals =>
    MessageData.group $ MessageData.paren $
      "leaf" ++ (if vals.isEmpty then MessageData.nil else " " ++ toMessageData vals.toArray)

instance : ToMessageData SubsumptionTrie := ⟨format⟩
------------------------------------------------------------------------------------------------------------------------------------

/-
  Features Zipperposition has (in order) (https://github.com/sneeuwballen/zipperposition/blob/master/src/core/FV_tree.ml#L311):
  1. Number of positive literals
  2. Number of negative literals
  3. Number of symbols and variables in positive literals (ho_weight of positive literals)
  4. Number of symbols and variables in negative literals (ho_weight of negative literals)
  5. The set of symbols occurring in positive literals
  6. The set of symbols occurring in negative literals
  7. Maximal depth of each symbol in positive literals (map from symbol name to number, -1 if symbol does not occur)
  8. Maximal depth of each symbol in negative literals (map from symbol name to number, -1 if symbol does not occur)
  9. Number of occurrences of each symbol in positive literals (map from symbol name to number)
  10. Number of occurrences of each symbol in negative literals (map from symbol name to number)

  For now, I intend to just implement the first four, but it may be worthwhile to implement the rest later
-/
def getFeatureVector (c : Clause) : List Feature := Id.run $ do
  let mut posLits := 0
  let mut negLits := 0
  let mut posWeight := 0
  let mut negWeight := 0
  for l in c.lits do
    if l.sign then
      posLits := posLits + 1
      posWeight := posWeight + l.lhs.weight + l.rhs.weight
    else
      negLits := negLits + 1
      negWeight := negWeight + l.lhs.weight + l.rhs.weight
  return [posLits, negLits, posWeight, negWeight]

def emptyLeaf : SubsumptionTrie := leaf {}
def emptyNode : SubsumptionTrie := node #[]

def singleton (c : Clause) (features : List Feature) : SubsumptionTrie :=
  match features with
  | nil => leaf (HashSet.empty.insert c)
  | fstFeature :: restFeatures => node #[(fstFeature, singleton c restFeatures)]

private def insertHelper (t : SubsumptionTrie) (c : Clause) (features : List Feature) : RuleM SubsumptionTrie :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let children ←
      children.binInsertM
        (fun a b => featureLt a.1 b.1)
        (fun (_, t) => do let t' ← insertHelper t c restFeatures; return (fstFeature, t'))
        (fun _ => return (fstFeature, singleton c restFeatures))
        (fstFeature, default)
    return node children
  | leaf vals, nil => return leaf (vals.insert c)
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def insert (t : SubsumptionTrie) (c : Clause) : RuleM SubsumptionTrie :=
  insertHelper t c (getFeatureVector c)

private def deleteHelper (t : SubsumptionTrie) (c : Clause) (features : List Feature) : RuleM SubsumptionTrie :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut curIdx := 0
    for (childFeature, childTrie) in children do
      if childFeature == fstFeature then
        let childTrie' ← deleteHelper childTrie c restFeatures
        let children' := children.set! curIdx (childFeature, childTrie')
        return node children'
      curIdx := curIdx + 1
    return node children -- c not found in t, so just return original t
  | leaf vals, nil => return leaf (vals.erase c)
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def delete (t : SubsumptionTrie) (c : Clause) : RuleM SubsumptionTrie :=
  deleteHelper t c (getFeatureVector c)

private def getPotentialSubsumingClausesHelper (t : SubsumptionTrie) (features : List Feature) : RuleM (Array Clause) :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut potentialSubsumingClauses := #[]
    for (childFeature, childTrie) in children do
      if featureLt childFeature fstFeature || featureEq childFeature fstFeature then
        potentialSubsumingClauses := potentialSubsumingClauses.append (← getPotentialSubsumingClausesHelper childTrie restFeatures)
    return potentialSubsumingClauses
  | leaf vals, nil => return vals.toArray
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def getPotentialSubsumingClauses (t : SubsumptionTrie) (c : Clause) : RuleM (Array Clause) :=
  getPotentialSubsumingClausesHelper t (getFeatureVector c)

private def getPotentialSubsumedClausesHelper (t : SubsumptionTrie) (features : List Feature) : RuleM (Array Clause) :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut potentialSubsumingClauses := #[]
    for (childFeature, childTrie) in children do
      if featureLt fstFeature childFeature || featureEq fstFeature childFeature then
        potentialSubsumingClauses := potentialSubsumingClauses.append (← getPotentialSubsumedClausesHelper childTrie restFeatures)
    return potentialSubsumingClauses
  | leaf vals, nil => return vals.toArray
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def getPotentialSubsumedClauses (t : SubsumptionTrie) (c : Clause) : RuleM (Array Clause) :=
  getPotentialSubsumedClausesHelper t (getFeatureVector c)