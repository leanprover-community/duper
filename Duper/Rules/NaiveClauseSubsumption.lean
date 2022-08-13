import Duper.Simp
import Duper.Selection
import Duper.Util.ProofReconstruction
import Duper.ProverM

namespace Duper

open Lean
open RuleM
open SimpResult
open ProverM
open Std
initialize Lean.registerTraceClass `Rule.subsumption

/-- Determines whether there is any σ such that σ(l1.lhs) = l2.lhs and σ(l1.rhs) = l2.rhs. Returns true and applies σ if so,
    returns false (without applying any substitution) otherwise -/
def checkDirectMatch (l1 : Lit) (l2 : Lit) : RuleM Bool := do
  conditionallyModifyingMCtx do -- Only modify the MCtx if both lhsCheck and rhsCheck are successful
    let lhsCheck ← performMatch #[(l2.lhs, l1.lhs)] -- Note: It is important that l2 is first argument since l2 is match_target
    let rhsCheck ← performMatch #[(l2.rhs, l1.rhs)]
    if lhsCheck && rhsCheck then return (true, true)
    else return (false, false)

/-- Determines whether there is any σ such that σ(l1.rhs) = l2.lhs and σ(l1.lhs) = l2.rhs. Returns true and applies σ if so,
    returns false (without applying any substitution) otherwise -/
def checkCrossMatch (l1 : Lit) (l2 : Lit) : RuleM Bool := do
  conditionallyModifyingMCtx do -- Only modify the MCtx if both lhsCheck and rhsCheck are successful
    let lhsCheck ← performMatch #[(l2.lhs, l1.rhs)] -- Note: It is important that l2 is first argument since l2 is match_target
    let rhsCheck ← performMatch #[(l2.rhs, l1.lhs)]
    if lhsCheck && rhsCheck then return (true, true)
    else return (false, false)

/-- Determines whether σ(l1) = l2 for any substitution σ. Importantly, litsMatch can return true if l1.sign = l2.sign and either:
    - σ(l1.lhs) = l2.lhs and σ(l1.rhs) = l2.rhs
    - σ(l1.rhs) = l2.lhs and σ(l1.lhs) = l2.rhs -/
def litsMatch (l1 : Lit) (l2 : Lit) : RuleM Bool := do
  if l1.sign != l2.sign then return false
  else if ← checkDirectMatch l1 l2 then return true
  else if ← checkCrossMatch l1 l2 then return true
  else return false

/-- Determines whether, for any substitution σ, σ(l) is in c at startIdx or after startIdx. If it is, then metavariables are assigned so that σ is
    applied and the index of σ(l) in c is returned. If there are multiple indices in c that l can match, then litInClause returns the first one.
    If there is no substitution σ such that σ(l) is in c at or after startIdx, the MetavarContext is left unchanged and none is returned.

    Additionally, litInClause is not allowed to return any Nat that is part of the exclude set. This is to prevent instances in which multiple
    literals in the subsumingClause all map onto the same literal in the subsumedClause. -/
def litInClause (l : Lit) (c : MClause) (exclude : HashSet Nat) (startIdx : Nat) : RuleM (Option Nat) := do
  for i in [startIdx:c.lits.size] do
    if exclude.contains i then
      continue
    else
      let cLit := c.lits[i]
      if ← litsMatch l cLit then return some i
      else continue
  return none

/-- Attempts to find an injective mapping f from subsumingClauseLits to subsumedClauseLits and a substitution σ such that
    for every literal l ∈ subsumingClauseLits, σ(l) = f(l). If subsumptionCheckHelper fails to find such a mapping and substitution,
    then subsumptionCheckHelper returns none without modifying the state's MetavarContext.

    If subsumptionCheckHelper succeeds, then it assigns MVars to apply σ and returns a list of nats res such that:
    ∀ i ∈ [0, subsumingClauseLits.length], σ(subsumingClauseLits.get! i) = subsumedClauseLits[res.get! i]

    The argument exclude contains a set of Nats that cannot be mapped to (so that injectivity is preserved). The argument fstStart is provided
    to facilitate backtracking.
    
    subsumptionCheckHelper is defined as a partialDef, but should always terminate because every recursive call either makes subsumingClauseLits
    smaller or makes fstStart bigger (and once fstStart exceeds the size of subsumedClauseLits.lits, litInClause is certain to fail) -/
partial def subsumptionCheckHelper (subsumingClauseLits : List Lit) (subsumedClauseLits : MClause) (exclude : HashSet Nat) (fstStart := 0) :
  RuleM Bool := do
  match subsumingClauseLits with
  | List.nil => return true
  | l :: restSubsumingClauseLits =>
    match ← litInClause l subsumedClauseLits exclude fstStart with
    | none => return false
    | some idx =>
      let tryWithIdx ←
        conditionallyModifyingMCtx do -- Only modify the MCtx if the recursive call succeeds
          let exclude := exclude.insert idx
          if ← subsumptionCheckHelper restSubsumingClauseLits subsumedClauseLits exclude then return (true, true)
          else return (false, false)
      /- tryWithIdx indicates whether it is possible to find an injective mapping from subsumingClauseLits to subsumedClauseLits that satisfies
         the constraints of subsumption where the first literal in subsumingClauseLits is mapped to the first possible literal in subsumingClauseLits
         after fstStart. If tryWithIdx succeeded, then we can simply return that success and have no need to backtrack. But if tryWithIdx failed,
         then matching l with the first lit possible after fstStart in subsumedClauseLits doesn't work. Therefore, we should simulate backtracking
         to that decision by recursing with fstStart one above idx -/
      if tryWithIdx then return true
      else subsumptionCheckHelper subsumingClauseLits subsumedClauseLits exclude (idx + 1)

def subsumptionCheck (subsumingClause : MClause) (subsumedClause : MClause) : RuleM Bool :=
  withoutModifyingMCtx do -- Avoid modifying mctx so that mvar assignments from failed subsumption checks don't impact future subsumption checks
    if subsumingClause.lits.size > subsumedClause.lits.size then return false
    subsumptionCheckHelper (subsumingClause.lits).toList subsumedClause {}

/-- naiveForwardClauseSubsumption implements forward clause subsumption without the feature vector indexing described
    in "Simple and Efficient Clause Subsumption with Feature Vector Indexing" -/
def naiveForwardClauseSubsumption (activeClauses : ClauseSet) : MSimpRule := fun c => do
  let fold_fn := fun acc nextClause => do
    match acc with
    | Unapplicable =>
      withoutModifyingLoadedClauses do
        let nextClause ← loadClause nextClause
        if ← subsumptionCheck nextClause c then 
          trace[Rule.subsumption] "Forward subsumption: removed {c.lits} because it was subsumed by {nextClause.lits}"
          return Removed 
        else return Unapplicable
    | Removed => return Removed
    | Applied _ => throwError "Invalid clause subsumption result"
  activeClauses.foldM fold_fn Unapplicable

open BackwardSimpResult

def naiveBackwardClauseSubsumption (activeClauses : ClauseSet) : BackwardMSimpRule := fun givenSubsumingClause => do
  let fold_fn := fun acc nextClause =>
    withoutModifyingLoadedClauses do
      let nextClause ← loadClause nextClause
      if ← subsumptionCheck givenSubsumingClause nextClause then
        trace[Rule.subsumption] "Backward subsumption: removed {nextClause.lits} because it was subsumed by {givenSubsumingClause.lits}"
        return (nextClause :: acc)
      else return acc
  return Removed (← activeClauses.foldM fold_fn [])