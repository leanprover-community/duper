import Lean
import Duper.RuleM

namespace Duper

open Lean
open RuleM
open List
open Expr

initialize Lean.registerTraceClass `duper.subsumptionTrie.debug

inductive SubsumptionTrieFeatureValue where
  | N : Nat → SubsumptionTrieFeatureValue -- Feature is a number
  | S : HashSet Expr → SubsumptionTrieFeatureValue -- Feature is a set
  | M : HashMap Expr Nat → SubsumptionTrieFeatureValue -- Feature is a map
deriving Inhabited

open SubsumptionTrieFeatureValue

def SubsumptionTrieFeatureValueLe (f1 : SubsumptionTrieFeatureValue) (f2 : SubsumptionTrieFeatureValue) : Bool :=
  match f1, f2 with
  | N n1, N n2 => n1 ≤ n2
  | S s1, S s2 => -- Return true iff s1 is a subset of s2
    Id.run $ do
    for e in s1.toArray do
      if s2.contains e then continue
      else return false
    return true
  | M m1, M m2 => -- Return true iff for every (e, n1) pair in m1 there is an (e, n2) pair in m2 with n1 ≤ n2
    Id.run $ do
    for (e, n1) in m1.toArray do
      match m2.find? e with
      | none => return false
      | some n2 =>
        if n1 ≤ n2 then continue
        else return false
    return true
  | _, _ => false -- In practice, this case should never be reached if comparing features at the same depth

def SubsumptionTrieFeatureValueEq (f1 : SubsumptionTrieFeatureValue) (f2 : SubsumptionTrieFeatureValue) : Bool :=
  match f1, f2 with
  | N n1, N n2 => n1 == n2
  | S s1, S s2 => s1.toArray == s2.toArray
  | M m1, M m2 => m1.toArray == m2.toArray
  | _, _ => false -- In practice, this case should never be reached if comparing features at the same depth

abbrev FeatureVector := List SubsumptionTrieFeatureValue

/-
  Data structure for feature vector indexing:
  https://www.researchgate.net/publication/228724593_Simple_and_Efficient_Clause_Subsumption_with_Feature_Vector_Indexing
-/
inductive SubsumptionTrie where
  | node (children : Array (SubsumptionTrieFeatureValue × SubsumptionTrie)) : SubsumptionTrie
  | leaf (vals : HashSet Clause) : SubsumptionTrie
deriving Inhabited

namespace SubsumptionTrie

-- Print functions -----------------------------------------------------------------------------------------------------------------
def SubsumptionTrieFeatureValue.format : SubsumptionTrieFeatureValue → MessageData
  | N n => m!"{n}"
  | S s => m!"{s.toArray}"
  | M m => m!"{m.toArray}"

instance : ToMessageData SubsumptionTrieFeatureValue := ⟨SubsumptionTrieFeatureValue.format⟩

partial def format : SubsumptionTrie → MessageData
  | node children =>
    MessageData.group $ MessageData.paren $
      "node" ++ MessageData.joinSep (children.toList.map $ fun ⟨k, c⟩ => MessageData.paren (toMessageData k ++ " => " ++ format c)) ","
  | leaf vals =>
    MessageData.group $ MessageData.paren $
      "leaf" ++ (if vals.isEmpty then MessageData.nil else " " ++ toMessageData vals.toArray)

instance : ToMessageData SubsumptionTrie := ⟨format⟩
------------------------------------------------------------------------------------------------------------------------------------

/-- Inserts every variable and constant that appears in e into acc. Note that as with Expr.weight, this function may require
    revision to be more similar to Zipperposition's implementation once we actually start working on higher order things -/
partial def collectSymbolsInExpr (acc : HashSet Expr) (e : Expr) : HashSet Expr :=
  match e.consumeMData with
  | fvar _ => acc.insert e.consumeMData
  | const _ _ => acc.insert e.consumeMData
  | app e1 e2 => collectSymbolsInExpr (collectSymbolsInExpr acc e1) e2
  | lam _ _ body _ => collectSymbolsInExpr acc body
  | forallE _ _ body _ => collectSymbolsInExpr acc body
  | letE _ _ val body _ => collectSymbolsInExpr (collectSymbolsInExpr acc val) body
  | proj _ _ struct => collectSymbolsInExpr acc struct
  | _ => acc

/-- Inserts every variable and constant that appears in l into acc. -/
def collectSymbolsInLit (acc : HashSet Expr) (l : Lit) : HashSet Expr :=
  collectSymbolsInExpr (collectSymbolsInExpr acc l.lhs) l.rhs

/-- Updates acc with maps each symbol to its maximal depth in a clause. Note that as with Expr.weight, this function may
    require revision to be more similar to Zipperposition's implementation once we actually start working on higher order things.
    See https://github.com/sneeuwballen/zipperposition/blob/master/src/core/FV_tree.ml#L182 -/
partial def updateDepthMapWithExpr (acc : HashMap Expr Nat) (e : Expr) (curDepth := 0) : HashMap Expr Nat :=
  match e.consumeMData with
  | fvar fVarId =>
    match acc.find? (fvar fVarId) with
    | none => acc.insert (fvar fVarId) curDepth
    | some maxDepth =>
      if curDepth > maxDepth then acc.insert (fvar fVarId) curDepth
      else acc
  | const declName us =>
    match acc.find? (const declName us) with
    | none => acc.insert (const declName us) curDepth
    | some maxDepth =>
      if curDepth > maxDepth then acc.insert (const declName us) curDepth
      else acc
  | app e1 e2 => -- We recurse along e1 with curDepth and e2 with curDepth + 1 following Zipperposition's symbols_depth_ function
    updateDepthMapWithExpr (updateDepthMapWithExpr acc e1 curDepth) e2 (curDepth + 1)
  | lam _ _ body _ => -- As with Zipperposition's implementation, we do not increase depth when going under lambdas
    updateDepthMapWithExpr acc body curDepth
  | forallE _ _ body _ => -- We stay at curDepth to be consistent with the above case
    updateDepthMapWithExpr acc body curDepth
  | letE _ _ val body _ => -- We stay at curDepth to be consistent with the above cases (though I'm less sure that this is correct)
    updateDepthMapWithExpr (updateDepthMapWithExpr acc val curDepth) body curDepth
  | proj _ _ struct => updateDepthMapWithExpr acc struct (curDepth + 1)
  | _ => acc

/-- Updates acc which maps each symbol to its maximal depth in a clause. -/
def updateDepthMapWithLit (acc : HashMap Expr Nat) (l : Lit) : HashMap Expr Nat :=
  updateDepthMapWithExpr (updateDepthMapWithExpr acc l.lhs) l.rhs

/-- Updates acc which maps each symbol to the number of times it occurs in a clause. Note that as with Expr.weight, this function may
    require revision to be more similar to Zipperposition's implementation once we actually start working on higher order things. -/
partial def updateOccurrenceMapWithExpr (acc : HashMap Expr Nat) (e : Expr) : HashMap Expr Nat :=
  match e.consumeMData with
  | fvar fVarId =>
    match acc.find? (fvar fVarId) with
    | none => acc.insert (fvar fVarId) 1
    | some numOccurrences => acc.insert (fvar fVarId) (numOccurrences + 1)
  | const declName us =>
    match acc.find? (const declName us) with
    | none => acc.insert (const declName us) 1
    | some numOccurrences => acc.insert (const declName us) (numOccurrences + 1)
  | app e1 e2 => updateOccurrenceMapWithExpr (updateOccurrenceMapWithExpr acc e1) e2
  | lam _ _ body _ => updateOccurrenceMapWithExpr acc body
  | forallE _ _ body _ => updateOccurrenceMapWithExpr acc body
  | letE _ _ val body _ => updateOccurrenceMapWithExpr (updateOccurrenceMapWithExpr acc val) body
  | proj _ _ struct => updateOccurrenceMapWithExpr acc struct
  | _ => acc

/-- Updates acc which maps each symbol to the number of times it occurs in a clause. -/
def updateOccurrenceMapWithLit (acc : HashMap Expr Nat) (l : Lit) : HashMap Expr Nat :=
  updateOccurrenceMapWithExpr (updateOccurrenceMapWithExpr acc l.lhs) l.rhs

/-
  Features (in order) (based on Zipperposition: https://github.com/sneeuwballen/zipperposition/blob/master/src/core/FV_tree.ml#L311):
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
-/
def getFeatureVector (c : Clause) : FeatureVector := Id.run $ do
  let mut posLits := 0
  let mut negLits := 0
  let mut posWeight := 0
  let mut negWeight := 0
  let mut posSymbols := {}
  let mut negSymbols := {}
  let mut posDepthMap := {}
  let mut negDepthMap := {}
  let mut posOccurrenceMap := {}
  let mut negOccurrenceMap := {}
  for l in c.lits do
    if l.sign then
      posLits := posLits + 1
      posWeight := posWeight + l.lhs.weight + l.rhs.weight
      posSymbols := collectSymbolsInLit posSymbols l
      posDepthMap := updateDepthMapWithLit posDepthMap l
      posOccurrenceMap := updateOccurrenceMapWithLit posOccurrenceMap l
    else
      negLits := negLits + 1
      negWeight := negWeight + l.lhs.weight + l.rhs.weight
      negSymbols := collectSymbolsInLit negSymbols l
      negDepthMap := updateDepthMapWithLit negDepthMap l
      negOccurrenceMap := updateOccurrenceMapWithLit negOccurrenceMap l
  return [
    N posLits, N negLits, N posWeight, N negWeight,
    S posSymbols, S negSymbols,
    M posDepthMap, M negDepthMap, M posOccurrenceMap, M negOccurrenceMap
  ]

/-- Identical to getFeatureVector except it is written to taken an MClause rather than a Clause -/
def getFeatureVector' (c : MClause) : FeatureVector := Id.run $ do
  let mut posLits := 0
  let mut negLits := 0
  let mut posWeight := 0
  let mut negWeight := 0
  let mut posSymbols := {}
  let mut negSymbols := {}
  let mut posDepthMap := {}
  let mut negDepthMap := {}
  let mut posOccurrenceMap := {}
  let mut negOccurrenceMap := {}
  for l in c.lits do
    if l.sign then
      posLits := posLits + 1
      posWeight := posWeight + l.lhs.weight + l.rhs.weight
      posSymbols := collectSymbolsInLit posSymbols l
      posDepthMap := updateDepthMapWithLit posDepthMap l
      posOccurrenceMap := updateOccurrenceMapWithLit posOccurrenceMap l
    else
      negLits := negLits + 1
      negWeight := negWeight + l.lhs.weight + l.rhs.weight
      negSymbols := collectSymbolsInLit negSymbols l
      negDepthMap := updateDepthMapWithLit negDepthMap l
      negOccurrenceMap := updateOccurrenceMapWithLit negOccurrenceMap l
  return [
    N posLits, N negLits, N posWeight, N negWeight,
    S posSymbols, S negSymbols,
    M posDepthMap, M negDepthMap, M posOccurrenceMap, M negOccurrenceMap
  ]

def emptyLeaf : SubsumptionTrie := leaf {}
def emptyNode : SubsumptionTrie := node #[]

def singleton (c : Clause) (features : FeatureVector) : SubsumptionTrie :=
  match features with
  | [] => leaf (HashSet.empty.insert c)
  | fstFeature :: restFeatures => node #[(fstFeature, singleton c restFeatures)]

private def insertHelper (t : SubsumptionTrie) (c : Clause) (features : FeatureVector) : RuleM SubsumptionTrie :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut curIdx := 0
    for (childFeature, childTrie) in children do
      if SubsumptionTrieFeatureValueEq childFeature fstFeature then
        let childTrie' ← insertHelper childTrie c restFeatures
        let children' := children.set! curIdx (childFeature, childTrie')
        return node children'
      curIdx := curIdx + 1
    return node (children.push (fstFeature, singleton c restFeatures))
  | leaf vals, [] => return leaf (vals.insert c)
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def insert (t : SubsumptionTrie) (c : Clause) : RuleM SubsumptionTrie :=
  insertHelper t c (getFeatureVector c)

private def deleteHelper (t : SubsumptionTrie) (c : Clause) (features : FeatureVector) : RuleM SubsumptionTrie :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut curIdx := 0
    for (childFeature, childTrie) in children do
      if SubsumptionTrieFeatureValueEq childFeature fstFeature then
        let childTrie' ← deleteHelper childTrie c restFeatures
        let children' := children.set! curIdx (childFeature, childTrie')
        return node children'
      curIdx := curIdx + 1
    return node children -- c not found in t, so just return original t
  | leaf vals, [] => return leaf (vals.erase c)
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def delete (t : SubsumptionTrie) (c : Clause) : RuleM SubsumptionTrie :=
  deleteHelper t c (getFeatureVector c)

private def getPotentialSubsumingClausesHelper (t : SubsumptionTrie) (features : FeatureVector) : RuleM (Array Clause) :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut potentialSubsumingClauses := #[]
    for (childFeature, childTrie) in children do
      if SubsumptionTrieFeatureValueLe childFeature fstFeature then
        potentialSubsumingClauses := potentialSubsumingClauses.append (← getPotentialSubsumingClausesHelper childTrie restFeatures)
    return potentialSubsumingClauses
  | leaf vals, [] => return vals.toArray
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def getPotentialSubsumingClauses (t : SubsumptionTrie) (c : Clause) : RuleM (Array Clause) :=
  getPotentialSubsumingClausesHelper t (getFeatureVector c)

/-- Identical to `getPotentialSubsumingClauses` except it takes an MClause rather than a Clause -/
def getPotentialSubsumingClauses' (t : SubsumptionTrie) (c : MClause) : RuleM (Array Clause) :=
  getPotentialSubsumingClausesHelper t (getFeatureVector' c)

private def getPotentialSubsumedClausesHelper (t : SubsumptionTrie) (features : FeatureVector) : RuleM (Array Clause) :=
  match t, features with
  | node children, (fstFeature :: restFeatures) => do
    let mut potentialSubsumingClauses := #[]
    for (childFeature, childTrie) in children do
      if SubsumptionTrieFeatureValueLe fstFeature childFeature then
        potentialSubsumingClauses := potentialSubsumingClauses.append (← getPotentialSubsumedClausesHelper childTrie restFeatures)
    return potentialSubsumingClauses
  | leaf vals, [] => return vals.toArray
  | _, _ => throwError "Features: {features} length does not match depth of trie {t}"

def getPotentialSubsumedClauses (t : SubsumptionTrie) (c : Clause) : RuleM (Array Clause) :=
  getPotentialSubsumedClausesHelper t (getFeatureVector c)

/-- Identical to `getPotentialSubsumedClauses` except that it takes an MClause rather than a Clause -/
def getPotentialSubsumedClauses' (t : SubsumptionTrie) (c : MClause) : RuleM (Array Clause) :=
  getPotentialSubsumedClausesHelper t (getFeatureVector' c)
