import LeanHammer.ProverM
import LeanHammer.MClause

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

abbrev SimpRule := MClause → RuleM (SimpResult (List MClause))

def applySimpRuleAux (rule : SimpRule) (givenClause : Clause) : 
    ProverM (SimpResult (List Clause)) := do
  RuleM.runAsProverM do
    let mclause ← MClause.fromClause givenClause
    let cs? ← rule mclause
    let cs? ← cs?.mapM fun cs => cs.mapM fun c => c.toClause
    cs?

def applySimpRule (rule : SimpRule) (givenClause : Clause) :
    ProverM (SimpResult Clause) := do
  match ← applySimpRuleAux rule givenClause with
  | Removed           => Removed
  | Unapplicable      => Unapplicable
  | Applied []        => Removed
  | Applied (c :: cs) => do
    for c' in cs do addToPassive c'
    Applied c

