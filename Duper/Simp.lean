import Duper.ProverM
import Duper.RuleM
import Duper.MClause
import Duper.Util.Iterate

namespace Duper
open RuleM
open ProverM

inductive SimpResult (α : Type)
| Applied (c : α) : SimpResult α
| Unapplicable : SimpResult α
| Removed : SimpResult α

namespace SimpResult

def mapM [Monad m] (f : α → m β): SimpResult α → m (SimpResult β)
| Applied c    => return Applied (← f c)
| Unapplicable => return Unapplicable
| Removed      => return Removed

def forM {m : Type u → Type v} [Monad m] {α : Type} (r : SimpResult α) (f : α → m PUnit) : m PUnit :=
match r with
| Applied c    => f c
| Unapplicable => return PUnit.unit
| Removed      => return PUnit.unit

end SimpResult

open SimpResult

abbrev MSimpRule := MClause → RuleM (SimpResult (List (MClause × Option ProofReconstructor)))
abbrev SimpRule := Clause → ProverM (SimpResult Clause)

def MSimpRule.toSimpRule (rule : MSimpRule) (ruleName : String) : SimpRule := fun givenClause => do
  -- Run the rule
  let (res, cs) ← runSimpRule do
    let mclause ← loadClause givenClause
    let cs? ← rule mclause
    cs?.forM fun cs => do
      for (c, mkProof) in cs do yieldClause c ruleName mkProof
    return cs?
  match res with
  | Removed           => return Removed
  | Unapplicable      => return Unapplicable
  | Applied []        => return Removed
  | Applied _ => do
    -- Return first clause, add others to passive set
    for i in [:cs.size] do
      let (c, proof) := cs[i]
      if i == 0 then
        let _ ← addNewClause c proof
      else
        addNewToPassive c proof
    return Applied cs[0].1

end Duper
