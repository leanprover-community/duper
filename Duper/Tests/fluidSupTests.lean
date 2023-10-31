import Duper.Tactic
import Duper.TPTP

set_option trace.Saturate.debug true
set_option trace.Rule.fluidSup true

-- Examples taken from https://matryoshka-project.github.io/pubs/lamsup_article.pdf pages 9 and 10

theorem supWithLambdasEx13 (a b c : t) (f g : t → t) (h : t → t → t)
  (eq1 : f a = c) (eq2 : ∀ y : t → t, h (y b) (y a) ≠ h (g (f b)) (g c)) : False :=
  by duper [*] {portfolioInstance := 0}

theorem supWithLambdasEx14 (a b c d : t) (f g : t → t)
  (eq1 : f a = c) (eq2 : f b = d) (eq3 : ∀ y : t → t, g c ≠ y a ∨ g d ≠ y b) : False :=
  by duper [*]

-- Note: Since the original example was untyped, it's possible that the types I chose for this don't work. So I don't
-- put too much stock in it if this continues to fail. But I do think that supWithLambda13 should be solvable
theorem supWithLambdaEx15 (a c : t) (f g : t → t) (h : t → ((t → t) → t → t) → t)
  (eq1 : f a = c) (eq2 : ∀ y : (t → t) → t → t, h (y (fun x => g (f x)) a) y ≠ h (g c) (fun w x => w x)) :
  False := by duper [*]