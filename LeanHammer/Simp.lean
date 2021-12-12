import LeanHammer.ProverM
import LeanHammer.MClause
import LeanHammer.Iterate

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

end SimpResult

open SimpResult

abbrev MSimpRule := MClause → RuleM (SimpResult (List MClause))
abbrev SimpRule := Clause → ProverM (SimpResult Clause)

def MSimpRule.toSimpRuleAux (rule : MSimpRule) : 
    Clause → ProverM (SimpResult (List Clause)) := 
  fun givenClause => do
    runRuleM do
      let mclause ← loadClause givenClause
      let cs? ← rule mclause
      let cs? ← cs?.mapM fun cs => cs.mapM fun c => neutralizeMClause c
      cs?

def MSimpRule.toSimpRule (rule : MSimpRule) : SimpRule := do
  fun givenClause => do
    match ← toSimpRuleAux rule givenClause with
    | Removed           => Removed
    | Unapplicable      => Unapplicable
    | Applied []        => Removed
    | Applied (c :: cs) => do
      for c' in cs do addNewToPassive c'
      Applied c
