import Lean
import Std
import Duper.RuleM

namespace Duper

open Lean
open RuleM
open Std
open List

initialize Lean.registerTraceClass `SubsumptionTrie.debug

abbrev Feature := Nat

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
  TODO: Need to figure out how to define a subsumption feature (fn). It can't just be a symbol/expr because some features might be more
  complicated than just |C|_f for some f. For instance, one feature might be Σ_f |C|_f which is the total number of function symbols.
  The paper says that in practice, this feature decides ~half of all subsumption attempts, so we definitely want to be able to support it
-/

def getFeatureVector (c : Clause) : List Feature := sorry

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
        (fun a b => a.1 < b.1)
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