import Duper.Tactic
import Duper.TPTP
import Duper.DUnif.DApply

-- Examples taken from https://matryoshka-project.github.io/pubs/lamsup_article.pdf pages 9 and 10

set_option trace.Saturate.debug true in
-- set_option trace.Rule.fluidSup true in
theorem supWithLambdasEx13 (a b c : t) (f g : t → t) (h : t → t → t)
  (eq1 : f a = c) (eq2 : ∀ y : t → t, h (y b) (y a) ≠ h (g (f b)) (g c)) : False :=
  by duper

-- This example works when demod, CLC, and simplify-reflect are disabled but fluidSup is enabled
-- This example fails when demod, CLC, and simplify-reflect are disabled and fluidSup is also disabled
-- TODO: Check whether demod, CLC, and simplify-reflect can solve this example even with fluidSup disabled
set_option trace.Print_Proof true in
theorem supWithLambdasEx14 (a b c d : t) (f g : t → t)
  (eq1 : f a = c) (eq2 : f b = d) (eq3 : ∀ y : t → t, g c ≠ y a ∨ g d ≠ y b) : False :=
  by duper

set_option trace.Saturate.debug true in
theorem supWithLambdaEx15 (a c : t) (f g : t → t) (h : t → ((t → t) → t → t) → t)
  (eq1 : f a = c) (eq2 : ∀ y : (t → t) → t → t, ∀ z : t → t, h (y (fun x => g (f x)) a) y ≠ h (g c) (fun w x => w x)) :
  False := by duper
  -- For this, I'm not seeing the unifier y ↦ (fun w x => w x) anywhere (but ex15unifier shows that the unifier can handle it)

set_option trace.DUnif.debug true in
def ex15unifier 
  (f : ((t → t) → t → t) → Type)
  (h : ∀ y : (t → t) → t → t, f y) : f (fun w x => w x) :=
  by dapply h attempt 30 unifier 0 contains 0

-- Todo: Write down and test examples 16 and 17
