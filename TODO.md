# TODO

Inference rules:
- perform superposition only on maximal sides of main premise literal
- Unimplemented rules:
  - ArgCong
  - BoolHoist
  - FalseElim
    - I have identPropFalseElim and identBoolFalseElim as simplification rules, but I don't have the general
      propFalseElim and boolFalseElim inference rules
  - EqHoist
  - NeqHoist
  - ForallHoist
  - ExistsHoist
  - BoolRw
  - ForAllRw
  - ExistsRw

Simplification rules:
- Clause subsumption
  - Make clause subsumption more efficient by incorporating indexing structure described in
    "Simple and Efficient Clause Subsumption with Feature Vector Indexing"
- Eliminate duplicate literals
  - Right now, elimDupLit doesn't recognize symmetrical literals as duplicates. That should be an easy but useful thing to fix
- Semantic tautology deletion?
- Positive/Negative simplify-reflect
- Equality subsumption?

Refactoring to consider:
- Use mvars in Clause to avoid cost of conversion?
- Use an inductive type to store information about proof steps for reconstruction instead of using closures
  - I imagine that this wouldn't hurt, but at least right now, this isn't a priority. After commit 807a153d2d319b68e70c2dec86aeaa4da676a9ae,
    I tested to see what would happen if I disabled all proof reconstruction, and there wasn't very much sppedup. For example, asylum_nine
    became about 200 ms quicker, but took around 10000 ms in total. So it's impossible that any marginal inefficiencies in proof reconstruction
    are acting as a bottleneck.

Known bugs/issues (bugs.lean):
- Premature saturation instances:
  - PUZ137_8 achieves premature saturation because our current interpretation of $o/$oType in tff isn't correct. Currently, we interpreting $o/$oType
    as Prop, but there is an important sense in which we should at least sometimes be interpreting it as Bool. PUZ137_8 is one such instance.
    - Though at present, I don't know that fully interpreting $o/$oType as Bool would necessarily work either
  - Prior to changing superposition's side condition checks (commit 87a238ff1b76b041ef9df88557f3ceb9c4b6c89a), COM003_1 failed due to deterministic
    timeout, but did not visibly have any issue of premature saturation. After changing superposition's side condition checks, COM003_1 now results
    in premature saturation. Need to look into why this is the case.
- PUZ031_1_modified:
  - "PANIC at Lean.MetavarContext.getDecl Lean.MetavarContext:343:17: unknown metavariable" error
  - Error when reconstructing clausification
    - Determine why resRight' and the type of dproof cannot be unified
- Escaped mvar tests
  - In clausificationStepE, there are two cases that involve introducing fresh metavariables. (the (true, Expr.forallE ..) case and the case that
    calls "clausify_exists_false"). In both of these cases, fresh metavariables are introduced with the assumption that they will be assigned
    by the Meta.isDefEq call in clausificationStep. Usually, this works, however, when we have a forall or there exists statement where the variable
    being bound does not appear in the resulting expression (e.g. (forall n : Nat, true)), the clause being produced will not reference the variable
    being bound. Consequently, the unification performed by Meta.isDefEq will not need to (or be able to) assign the introduced metavariable, yielding
    a final proof that contains metavariables (which the kernel will not accept).
- COM032_5:
  - Yields: "PANIC at Lean.Meta.whnfEasyCases Lean.Meta.WHNF:262:26: unreachable code has been reached"
  - Also results in deterministic timeout, though that's not particularly surprising or necessarily indicative of a specific bug
- Unknown metavariable error in many of github's tptp tests
  - When testing on NUM931_5, the error arises due to the type of sk.145 in the expression "sk.145 ?m.187882 ?m.187884".
    The issue is NOT the arguments passed into sk.145 but rather, the type of sk.145 itself. The type is:
    "forall (_ : Type), ?_uniq.187828 -> _" which contains the unknown metavariable '?_uniq.187828'

Other:
- Modify Unif.lean and Match.lean to use Lean's built-in unifier
  - Earlier attempt to do this was (temporarily) pulled back for two reasons.
  - First: modifying Unif.lean to use isDefEq resulted in many github tests (such as COM035_5) that previously passed to fail due to unknown
    metavariable errors.
  - Second: modifying Match.lean to use Lean's built-in unifier is nontrivial. This is because in order to do matching with Lean's built-in unifier,
    we have to withNewMCtxDepth, which is a MetaM function. However, the results of the unification need to persist even after returning from
    Match.lean (and we exit the withNewMCtxDepth) scope. If we try to call withNewMCtxDepth much earlier (e.g. as part of the simplification rules
    that call performMatch), then we run into difficulties in which withNewMCtxDepth expects a MetaM function but we want to write a RuleM function.
    It may be possible to get this to work, but some significant refactoring may be required, so I'm putting this on the backburner until profiling
    determines whether this would be helpful or necessary.
  - In addition to the above two reasons, it should be noted that, at least for some of the larger tests in test.lean, duper does WORSE when Unif.lean
    calls Lean's built-in unifier (not in the sense of failing tests it would otherwise pass, but in the sense of consistently taking longer)
- Because the types of SimpRule and BackwardSimpRule were changed to take Clauses rather than MClauses as input, calling loadClause has
  been moved from Simp.lean to the beginning of each simplification rule. This isn't a problem, but there are some places where it may not
  be necessary to call loadClause. Going through the simplification rules and changing them to only call loadClause if it is actually required
  may make some of the simplification rules more efficient
    - Prior to profiling, it is unclear to me whether this improvement would be significant, because it is has the potential to remove many
      calls to loadClause, or negligible because loadClause is implemented efficiently
- Find a way to better handle fvars in DiscrTree.lean's Key.hash and Key.lt. Currently, these functions have been modified to not depend
  on fvar names, which is good in that it makes behavior more consistent, but bad in that right now, fvar keys are almost always being viewed as equal
  to each other. Ideally, we should find a function that still distinguishes different fVarIds but is less sensitive to specific names (and in particular,
  does not cause duper's behavior to depend on anything but the current test)
    - Additionally, it also seems to be important to find a better deterministic way to handle fvars in Order.lean's precCompare. In an earlier commit, making
      precCompare fvar insensitive caused PUZ012_1 (at the end of test.lean) to go from a proof with 161 clauses to a proof with 1789 clauses. This might
      just mean that duper happens to get more lucky when precCompare looks at fvars, but it would also make sense more generally that having some way of
      ordering fvars would be beneficial so that the number of necessary superposition inferences can be cut down significantly.
- Unit tests, e.g. for the ordering. (How do unit tests work in Lean 4?)
- Command line version of duper?
- Currently, we have a hacky implementation of removing clauses from indices (tacking on a filter before retrieving). If this turns out to be too inefficient,
  implement removal from discrimination trees properly.

## For later:

Clausification
- preprocessing version of clausification?
- Tseitin transformation?

Heuristics:
- LPO Ordering
- Precedence heuristics for ordering
- Literal selection heuristics
- Next given clause heuristics

Special treatment for certain types/expressions:
- Implementing rules explicitly concerning boolean reasoning to better handle Bools
- Implementing rules or integrating tactics pertaining to Nats, Ints, and/or Reals

Other:
- Duper cannot synthesize the "Inhabited" property for types it is given 
    - For example, in the barber_paradox tests (in test.lean), Duper requires either an element of type person or a proof of "Inhabited person". But having a
      hypothesis that states there exists a person with some property is insufficient. I'm not sure whether it matters to us that Duper be able to synthesize
      the "Inhabited" property for types it's given, but I note that Duper cannot give full proofs to the barber_paradox tests unless if the inhabited property
      is given.
    - Perhaps more pressingly than the above example, the fact that duper cannot synthesize the "Inhabited" attribute prevents it from proving PUZ134_2 in TPTP_test.lean.
      If this issue arises only in a small number of cases, then it might not interfere with more rigorous testing, but otherwise, it may be necessary to add this
      functionality so that we can use more TPTP files for testing.