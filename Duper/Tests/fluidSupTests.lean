import Duper.Tactic
import Duper.TPTP
import Duper.DUnif.DApply

set_option trace.Saturate.debug true
set_option trace.Rule.fluidSup true

-- Examples taken from https://matryoshka-project.github.io/pubs/lamsup_article.pdf pages 9 and 10

theorem supWithLambdasEx13 (a b c : t) (f g : t → t) (h : t → t → t)
  (eq1 : f a = c) (eq2 : ∀ y : t → t, h (y b) (y a) ≠ h (g (f b)) (g c)) : False :=
  by duper
/-
What we want for supWithLambdasEx13:
  mainPremise preunification: [h (?m.457 b) (?m.457 a) ≠ h (g (f b)) (g c)]
  sidePremise preunification: [f a = c]
  mainPremiseSubterm preunification: ?m.457 a (pos is #[0] of main premise)
  freshFunction preunification: fun _ => ?m.460 _
  freshFunctionWithLhs preunification: ?m.460 (f a)

  mainPremiseSubterm postunification: ?m.460 (f a)
  freshFunction postunification: fun _ => ?m.460 _
  freshFunctionWithLhs postunification: ?m.460 (f a)
  freshFunctionWithRhs postunification: ?m.460 c

  In short: We want the metavariable `?m.457` that appears in the main premise to be unified
  in such a way that it applies `f` and then the fresh function `?m.460`. And we want this
  assignment to occur without making any assumptions about the fresh function `?m.460` (so
  that later, this fresh function can be unified with `g` by equality resolution)

  Currently none of the unifiers that are returned appear to do this. The closest we have
  are unifiers that make the freshFunction equal to `fun _ => ?m.XXX` after the unification.
  But this is not quite what we want because this unifier requires that freshFunction is a
  constant function when we want it to still be dependent on the input
-/

set_option trace.Print_Proof true in
theorem supWithLambdasEx14 (a b c d : t) (f g : t → t)
  (eq1 : f a = c) (eq2 : f b = d) (eq3 : ∀ y : t → t, g c ≠ y a ∨ g d ≠ y b) : False :=
  by duper

-- Note: Since the original example was untyped, it's possible that the types I chose for this don't work. So I don't
-- put too much stock in it if this continues to fail. But I do think that supWithLambda13 should be solvable
theorem supWithLambdaEx15 (a c : t) (f g : t → t) (h : t → ((t → t) → t → t) → t)
  (eq1 : f a = c) (eq2 : ∀ y : (t → t) → t → t, h (y (fun x => g (f x)) a) y ≠ h (g c) (fun w x => w x)) :
  False := by duper