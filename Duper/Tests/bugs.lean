import Duper.TPTP
import Duper.Tactic

-- Bug 1
namespace Color2

inductive Color :=
| red : Color
| green : Color

example : @Color.rec (fun _ => Nat) a b .red = a := by duper [Color.rec]

def test : Color → Color
| .red => .green
| .green => .red

set_option pp.match false
#print test
#print test.match_1
#print Color.casesOn

set_option inhabitationReasoning false in
set_option trace.Saturate.debug true in
set_option trace.Timeout.debug true in
example : ∃ c : Color, test c = .green := by
  duper [test, test.match_1, Color.rec, Color.casesOn]

-- This bug demonstrates the difficulty Duper has dealing with inductive arguments and facts such as Color.rec

end Color2

-- Bug 3
-- This example is the same as the below example except it was manually skolemized
set_option trace.Print_Proof true in
example (p : α → β → Prop) (g : _ → _) (h : ∀ (x : α), p x (g x)) : ∃ (f : α → β), ∀ x, p x (f x) :=
  by duper

-- This should work as evidenced by the example above
set_option inhabitationReasoning false in
set_option trace.Saturate.debug true in
set_option trace.Timeout.debug true in
example (p : α → β → Prop) (h : ∀ (x : α), ∃ y, p x y) : ∃ (f : α → β), ∀ x, p x (f x) :=
  by duper

-- Diagnosis of the above test
/-
- ∀ (a : α) (a_1 : β), p a (skS.0 0 a a_1) = True
- ∀ (a : α → β) (a_1 : α), p (skS.0 1 a a_1) (a (skS.0 1 a a_1)) = False

Both of the above clauses are in the active set at timeout. I believe it should be possible to unify the two left hand
sides via the following substitution:
- The first clause's `a_1` maps to some `b : β`
- The second clause's `a` and `a_1` maps to `f : α → β` and `y : α` such that `f (skS.0 1 f y) = skS.0 0 (skS.0 1 f y) b`.
  Note that this is only a constraint on `f` and makes no assumptions about `skS.0 1` or `skS.0 0`.
- The first clause's `a` maps to `(skS.0 1 f y)`

With the above unification, I believe both left hand sides should become `p (skS.0 1 f y) (skS.0 0 (skS.0 1 f y) b)`. This
would enable superposition to infer that `False = True`, which would directly yield a contradiction.

The fact that both of the listed clauses are in the active set at timeout most likely indicates that Duper was unable
to achieve this particular unification (if Duper were able to achieve this unification, the clause `False = True` would
be produced and I would expect this to immediately be the smallest clause in the passive set. The fact that this clause is
not immediately pulled from the passive set almost certainly indicates that it was not produced).

To further diagnose this bug, the thing to do would be to attempt to trace what duper is doing when superposition is called
with the above two clauses.
-/

-- Bug 4
set_option inhabitationReasoning true in
set_option trace.Saturate.debug true in
example (p : α → β → Prop) (h : ∀ (x : α), ∃ y, p x y) : ∃ (f : α → β), ∀ x, p x (f x) :=
  by duper

-- Diagnosis of the above test
/-
This is the same example used in bug 3, but with inhabitation reasoning enabled, duper results in premature saturation
rather than a deterministic timeout. The reason for this is duper is not able to determine that `α` or `α → β` are Inhabited.
Because of this, duper is unable to move forward, even though in principle, it could.

If Duper recognized `α` as nonempty, then Duper would be able to make more forward progress. When provided with `[Inhabited α]`,
the duper is able to derive that `β` is also nonempty in the above example (from `∃ y : β, ...` in `h`), though Duper will
still get stuck, not recognizing that `α → β` must be Nonempty if `α` and `β` are both Nonempty. Still, it would be more progress
than is currently achieved, and could be transformed into more progress yet if the Nonempty status of `α → β` were derived
from the Nonempty status of `α` and `β`.

Of course, Duper cannot know that `α` is nonempty, as this isn't actually entailed by the example. However, what Duper could
do in principle, rather than give up on any reasoning whatsoever, is recognize that if `α` is Empty, then regardless of what
`β` is, `α → β` must be Nonempty. This would allow Duper to proceed reasoning about the goal `∃ (f : α → β), ∀ x, p x (f x)`
which is negated to `(∃ (f : α → β), ∀ x, p x (f x)) = False` and clausified into
`∀ (a : α → β), ((∀ (x : α), p x (a x)) = False)`. With `α` recognized as Empty, `(∀ (x : α), p x (a x))` could be recognized
as vacuously true, which would transform the clause into `∀ (a : α → β), (True = False)`, and from there a contradiction could
easily be derived.

The point of this is that currently, inhabitation reasoning prevents any forward progress in the presence of potentially
uninhabited types even though there may be instances when casing on whether a type is inhabited could yield forward progress.
-/

-- Bug 5
set_option inhabitationReasoning true in
set_option trace.typeInhabitationReasoning.debug true in
tptp ITP023_3 "../TPTP-v8.0.0/Problems/ITP/ITP023_3.p"
  by duper -- Fails due to error: unknown free variable '_uniq.6173142'

set_option inhabitationReasoning false in
tptp ITP023_3' "../TPTP-v8.0.0/Problems/ITP/ITP023_3.p"
  by duper -- Det timeout

-- Diagnosis of the above test
/-
The error appears to occur during removeVanishedVarsHelper (which is only called when inhabitationReasoning is enabled).
Specifically, when the clause `∀ (a : Type) (a_1 a_2 : a), _uniq.6179254 → p c_2Ebool_2ET_2E0 = True ∨ a_1 = a_2` is
processed, an mvar `?m.6184382` is given the type `_uniq.6179254`. When `Meta.findInstance` is called on `?m.6184382`'s
type (`_uniq.6179254`), the error "unknown free variable '_uniq.6173142'" is produced.

To further diagnose this bug, the thing to do would be to attempt to trace how the above clause was produced (and therefore,
where the `_uniq.6179254` constraint was imposed).
-/

-- Bug 6
set_option inhabitationReasoning true in
example : ((∃ (A B : Type) (f : B → A) (x : B), f x = f x) = True) :=
  by duper -- Fails because we currently do not infer that A is nonempty from the fact that B and B → A are nonempty

set_option inhabitationReasoning true in
example : ∃ (A : Type) (B : A → Type) (f : ∀ (a : A), B a) (x : A), (f x = f x) = True :=
  by duper

-- Diagnosis of the above two examples
/-
This isn't so much a bug as it is a limitation in the current approach to inhabitation reasoning. The extent of reasoning Duper
currently performs in attempting to determine whether a type is inhabited is limited. The two above examples provide somewhat
more complicated cases in which Duper is not able to infer that a particular type is inhabited
-/

-- Bug 7
example (a : α) (as : List α) : [] ≠ a :: as :=
  by duper [List.rec] -- Error: AppBuilder for 'mkAppOptM', result contains metavariables @List.nil

-- Diagnosis of the above example
/-
This error arises during `addRecAsFact` in Tactic.lean on the line that calls `let ctor ← mkAppOptM ctorName #[]`.
Fundamentally, the issue is that `List` is polymorphic and the current `addRecAsFact` doesn't support that.
-/