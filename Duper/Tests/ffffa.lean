import Duper.Tactic
import Duper.Tests.Testduper

axiom f : Nat → Nat
axiom a : Nat

example (h : f a = a) : 
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
a
))))))))))
))))))))))
))))))))))
))))))))))
)))))))))) = a
 := by duper

 example (h : f a = a) : 
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
f (f (f (f (f (f (f (f (f (f (
a
))))))))))
))))))))))
))))))))))
))))))))))
)))))))))) = a
 := by testduper