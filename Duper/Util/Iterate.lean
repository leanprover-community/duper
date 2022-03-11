import Duper.ProverM


inductive LoopCtrl
| next : LoopCtrl
| abort : LoopCtrl

@[specialize] -- TODO: What does "specialize do?"
partial def iterate [Monad m] (f : m LoopCtrl) : m Unit := do
  match ← f with
  | LoopCtrl.next => iterate f
  | LoopCtrl.abort => pure ()
