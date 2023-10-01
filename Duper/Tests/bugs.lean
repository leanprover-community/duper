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

set_option trace.Saturate.debug true in
set_option trace.Timeout.debug true in
example : test .red = .green := by
  duper [test, test.match_1, Color.rec, Color.casesOn]

-- Diagnosis of the above test:
/-
When inhabitationReasoning is enabled, test.match_1, Color.rec, and Color.casesOn are all potentially
vacuous. This is caused by several issues in the current inhabitationReasoning. One issue is that Color2.Color
itself is not recognized as Inhabited, though there appear to be other issues as well that I haven't fully
figured out. In any case, the end result is premature saturation.

When inhabitationReasoning is disabled, duper spends plenty of time reasoning, but the reasoning
generates a ton of clauses, most of which aren't even unit clauses. I'm not 100% clear on whether
duper is currently capable of solving the goal (and just needs to wade through a ton of unneeded
clauses before it finds the one it actually needs), or whether the fact that duper has stuff to spin
its wheels on is obscuring the fact that duper can't actually solve this goal. In this latter case,
it might be due to issues actually deconstructing the arguments provided to duper (e.g. Color2.Color.rec)

It's notable that when inhabitationReasoning is disabled, both of the following are in the active set:
- `∀ (a : Color2.Color), Color2.test a = Color2.Color.rec Color2.Color.green Color2.Color.red a`
  - The full rhs is `@Color2.Color.rec (fun x => Color2.Color) Color2.Color.green Color2.Color.red a`
    which reduces to `Color.green` when a is red  (we can see that by calling #reduce)
- `Color2.test Color2.Color.red ≠ Color2.Color.green`

In the expanded form, it's unsurprising that the first premise's lhs would be smaller than the first premise's
rhs. But if we reduced the first premise's rhs, then the rhs would just be Color.green, which would be smaller.
Then, by setting a to red, we should be able to unify both premise's lhs to obtain .green ≠ .green (and from that,
we would quickly obtain our contradiction)

One question maybe worth asking is, in the current calculus, are we even instructed to compare the lhs of both
premises. Because in their current (irreducible) state, the first premise's lhs is smaller than the first premise's
rhs. This stop being true after we instantiate a and reduce the rhs, but it is true until that point.

I do think that for superposition, the lhs of the second premise should be eligible for superposition based on
(E2) of Defition 22. However, the issue for superposition is that for the first premise, by side condition 5,
we can't have the unifying side be less than or equal to the side we are substituting in. After we instantiate a,
both the lhs and rhs can be reduced to .red, but that's irrelevant because we definitely don't do substitution
midway through the superposition rule. After applying σ (which instantiates a as red), we have that the lhs of
the first premise is less than the rhs of the first premise, so we can't replace the first premise's lhs with its
rhs in the second premise.

Additional note: The above discouse concerns why I can't combine the two noted premises. And my conclusion is that
duper is being faithful to the calculus in refusing to do this. However, it occurs to me that maybe the thing
we should want of duper here isn't to use test.match_1, Color.rec, and Color.casesOn to obtain the result. Maybe
we should instead just say that `test .red` is a reducible that ought to be reduced (and if we did reduce it, our
goal would be immediately proven trivially). Having things like test.match_1, Color.rec, and Color.casesOn would
perhaps be useful if the goal were more abstract (e.g. if we were trying to prove `∃ x : Color, test x = .green`),
but as is, maybe we should want duper to just reduce `test .red` to `.green`

Final note: If `preprocessFact` in `Util.Reduction.lean` is modified at line 17 to use transparency .all rather than
.instances, the above goal is solved both with and without inhabitation reasoning. I can't recall the specific reason
we were using .instances transparency though, so I'll refrain from actually making the modification until I can check
in with Yicheng. However, even when this change is made, the example written below fails both with and without
inhabitationReasoning. An alternative way to handle this would be to improve Duper's awareness of definitions so that,
having given `test` as an explicit definition, it will know to unfold `test`. Rather than modifying the preprocessing,
this approach would instead have definitional rewriting/unfolding be an explicit simplification rule.
-/

set_option inhabitationReasoning false in
set_option trace.Saturate.debug true in
set_option trace.Timeout.debug true in
example : ∃ c : Color, test c = .green := by
  duper [test, test.match_1, Color.rec, Color.casesOn]

end Color2

-- Bug 2
instance : Neg Nat := sorry

def even_int_fun (f : Int → Int) := ∀ x, f (-x) = f x
def even_nat_fun (f : Nat → Nat) := ∀ x, f (-x) = f x

instance : Add (Int → Int) := (⟨fun f g x => f x + g x⟩ : Add (Int → Int))
instance : Add (Nat → Nat) := (⟨fun f g x => f x + g x⟩ : Add (Nat → Nat))

-- Although it takes longer than I would prefer (~2s), duper is able to solve this
set_option trace.Print_Proof true in
example (f : Int → Int) (hf : ∀ x, f (-x) = f x) : even_int_fun f := by -- The goal is the same as hf
  duper [even_int_fun]

-- Although duper can solve the above example, it appears to time out on this example. I haven't yet pinpointed
-- the reason why these two examples behave differently
set_option trace.Timeout.debug true in
set_option trace.Timeout.debug.fullActiveSet true in
example (f : Nat → Nat) (hf : ∀ x, f (-x) = f x) : even_nat_fun f := by -- The goal is the same as hf
  duper [even_nat_fun]

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