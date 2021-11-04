
inductive LoopCtrl (α β : Type)
| next (a : α) : LoopCtrl α β
| abort (a : β) : LoopCtrl α β

namespace IO

def loop (init : α) (l : α → IO (LoopCtrl α β)) : IO β :=
IO.iterate init fun a => do 
  match ← l a with
  | LoopCtrl.next a => Sum.inl a
  | LoopCtrl.abort b => Sum.inr b 

def timedLoop (maxtime : Nat) (init : α) (l : α → IO (LoopCtrl α α)) : IO α := do
  let startTime ← IO.monoMsNow
  return ← IO.loop init fun a => do
    match ← l a with
    | LoopCtrl.next a => 
      let now ← IO.monoMsNow
      if now - startTime > maxtime 
      then LoopCtrl.abort a 
      else LoopCtrl.next a
    | LoopCtrl.abort a => LoopCtrl.abort a

end IO