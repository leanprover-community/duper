# TODO

Inference rules:
- check for strict maximality in superposition rule
- perform superposition only on maximal sides of main premise literal
- Add ordering checks to Equality Resolution
- Check ordering constraints before unification
- Check whether a clause is still in active set when retrieving it from an index. (Or alternatively, remove clauses from indices when they are removed from active set)

Simplification rules:
- Semantic tautology deletion?
- Rewriting of positive/negative literals (aka Demodulation)
- Positive/Negative simplify-reflect
- Clause subsumption
- Equality subsumption?

Refactoring to consider:
- Use mvars in Clause to avoid cost of conversion?
- Use an inductive type to store information about proof steps for reconstruction instead of using closures?

Other:
- Unit tests, e.g. for the ordering. (How do unit tests work in Lean 4?)
- Command line version of duper?
- Why are some clauses repeated in the proofs that duper produces (e.g. clauses 6-8 in test0011 and almost all of the early clauses in iffClausificationTest1)?
    - Do repeated clauses indicate that we're unnecessarily reproving things, and if so, how much does that impact efficiency?
- barber_paradox_inline3 appears to be show that there are some conditions in which duper can run into what's effectively an infinite loop. The fact that this
  occurs in barber_paradox_inline3 but not in barber_paradox5 (which I would expect to behave identically) potentially points to an error in how I modified duper
  to be able to function in larger tactic-style proofs.
    - COM001_1_modified in TPTP_test.lean appears to have a similar behavior
- Determine the cause of the error in PUZ134_2_modified in TPTP_test.lean
- Determine why incomparable types are being equated in PUZ135_1 in TPTP_test.lean
- Determine why several tests in TPTP_test.lean reach saturation without being solved
- Look into whether it would be useful/more efficient to have a lhs/rhs convention so that clauses aren't duplicated up to symmetries (e.g. a = b and b = a)

## For later:

Clausification
- preprocessing version of clausification?
- Tseitin transformation?

Heuristics:
- LPO Ordering
- Precedence heuristics for ordering
- Literal selection heuristics
- Next given clause heuristics

Other:
- Duper cannot synthesize the "Inhabited" property for types it is given 
    - For example, in the barber_paradox tests (in test.lean), Duper requires either an element of type person or a proof of "Inhabited person". But having a
      hypothesis that states there exists a person with some property is insufficient. I'm not sure whether it matters to us that Duper be able to synthesize
      the "Inhabited" property for types it's given, but I note that Duper cannot give full proofs to the barber_paradox tests unless if the inhabited property
      is given.
    - Perhaps more pressingly than the above example, the fact that duper cannot synthesize the "Inhabited" attribute prevents it from proving PUZ134_2 in TPTP_test.lean.
      If this issue arises only in a small number of cases, then it might not interfere with more rigorous testing, but otherwise, it may be necessary to add this
      functionality so that we can use more TPTP files for testing.