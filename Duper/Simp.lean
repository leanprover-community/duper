import LeanHammer.ProverM
import LeanHammer.RuleM
import LeanHammer.MClause
import LeanHammer.Util.Iterate

namespace Duper
open RuleM
open ProverM

inductive SimpResult (α : Type)
| Applied (c : α) : SimpResult α
| Unapplicable : SimpResult α
| Removed : SimpResult α

namespace SimpResult

def mapM [Monad m] (f : α → m β): SimpResult α → m (SimpResult β)
| Applied c    => do Applied (← f c)
| Unapplicable => Unapplicable
| Removed      => Removed

def forM {m : Type u → Type v} [Monad m] {α : Type} (r : SimpResult α) (f : α → m PUnit) : m PUnit :=
match r with
| Applied c    => f c
| Unapplicable => PUnit.unit
| Removed      => PUnit.unit

end SimpResult

open SimpResult

abbrev MSimpRule := MClause → RuleM (SimpResult (List (MClause × Option ProofReconstructor)))
abbrev SimpRule := Clause → ProverM (SimpResult Clause)
    

def MSimpRule.toSimpRule (rule : MSimpRule) (ruleName : String)
    : SimpRule := fun givenClause => do
  -- Run the rule
  let (res, cs) ← runSimpRule do
    let mclause ← loadClause givenClause
    let cs? ← rule mclause
    cs?.forM fun cs => do
      for (c, mkProof) in cs do yieldClause c ruleName mkProof
    return cs?
  match res with
  | Removed           => Removed
  | Unapplicable      => Unapplicable
  | Applied []        => Removed
  | Applied _ => do
    -- Return first clause, add others to passive set
    for i in [:cs.size] do
      let (c, proof) := cs[i]
      if i == 0 then
        let _ ← addNewClause c proof
      else
        addNewToPassive c proof
    Applied cs[0].1


end Duper