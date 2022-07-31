# TODO

Inference rules:
- perform superposition only on maximal sides of main premise literal

Simplification rules:
- Demodulation
  - Proof reconstructions
  - Backward demodulation (using given clause as side premise to simplify pre-existing clauses in the active set)
- Semantic tautology deletion?
- Positive/Negative simplify-reflect
- Clause subsumption
- Equality subsumption?

Refactoring to consider:
- Use mvars in Clause to avoid cost of conversion?
- Use an inductive type to store information about proof steps for reconstruction instead of using closures?

Known bugs/issues (bugs.lean):
- Premature saturation instances:
  - PUZ137_8 achieves premature saturation because our current interpretation of $o/$oType in tff isn't correct. Currently, we interpreting $o/$oType
    as Prop, but there is an important sense in which we should at least sometimes be interpreting it as Bool. PUZ137_8 is one such instance.
    - Though at present, I don't know that fully interpreting $o/$oType as Bool would necessarily work either
  - Prior to changing superposition's side condition checks (commit 87a238ff1b76b041ef9df88557f3ceb9c4b6c89a), COM003_1 failed due to deterministic
    timeout, but did not visibly have any issue of premature saturation. After changing superposition's side condition checks, COM003_1 now results
    in premature saturation. Need to look into why this is the case.
- Inconsistent behavior of PUZ012_1
  - In bugs.lean, if lines 6 and 7 are commented out (the definition of PUZ082_8), then PUZ012_1 will fail to find a contradiction due to 
    deterministic timeout. However, if lines 6 and 7 are not commented out, then PUZ012_1 quickly succeeds in finding a valid contradiction
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

Other:
- Although the current setup of using 'lake build' to run PUZ_tests, LCL_tests, and COM_tests is better than nothing, at some point, I'd like to make tests
  that have more consistent output (e.g. test succeeded, test saturated, test ran out of time, or test encountered error) so that it can quickly/easily be
  determined what effects any given commit had on the outputs for PUZ_tests, LCL_tests, and COM_tests (i.e. which tests' behavior changed from the previous commit).
- Unit tests, e.g. for the ordering. (How do unit tests work in Lean 4?)
- Command line version of duper?
- Why are some clauses repeated in the proofs that duper produces (e.g. clauses 6-8 in test0011 and almost all of the early clauses in iffClausificationTest1)?
    - Do repeated clauses indicate that we're unnecessarily reproving things, and if so, how much does that impact efficiency?
- Look into whether it would be useful/more efficient to have a lhs/rhs convention so that clauses aren't duplicated up to symmetries (e.g. a = b and b = a)
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