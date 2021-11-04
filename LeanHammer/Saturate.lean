import LeanHammer.Clause
import LeanHammer.Loop
open Lean


structure ProofState :=
(activeSet : Array Clause)
(passiveSet : Array Clause)

namespace ProofState

def empty : ProofState := ⟨#[],#[]⟩ 

end ProofState

partial def saturate : IO Unit := do
  let ps ← IO.timedLoop 5 ProofState.empty fun proofState => do
    IO.println "now"
    IO.sleep 1
    return LoopCtrl.next proofState

set_option trace.Meta.debug true


#eval saturate