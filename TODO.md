# TODO

Inference rules:
- Equality Factoring inference rule
- check for strict maximality in superposition rule
- perform superposition only on maximal sides of main premise literal
- Check ordering constraints before unification
- Check whether a clause is still in active set when retrieving it from an index. (Or alternatively, remove clauses from indices when they are removed from active set)

Simplification rules:
- Semantic tautology deletion?
- Destructive Equality Resolution
- Rewriting of positive/negative literals (aka Demodulation)
- Positive/Negative simplify-reflect
- Clause subsumption
- Equality subsumption?
- Add proof reconstruction for inequalities of type Prop (see clausificationStepLit in Clausification.lean)
    - Once the reconstruction is added, confirm that iffClausificationTest2 (which currently depends on sorryAx because it uses an inequality of type Prop)
      no longer depends on sorryAx

Refactoring to consider:
- Use mvars in Clause to avoid cost of conversion?
- Use an inductive type to store information about proof steps for reconstruction instead of using closures?

Other:
- Unit tests, e.g. for the ordering. (How do unit tests work in Lean 4?)
- Command line version of duper?
- General issues with using duper in larger tactic-style proofs (see barber_paradox_inline tests in test.lean)
    - Right now, I believe the main issue is that mdata isn't fully handled everywhere, but there may be other issues that are obscured by the more immediate
      mdata issues.
    - I'd also like to look into/test whether any issues arise when trying to use (by duper) in the midst of a larger term
- Why are some clauses repeated in the proofs that duper produces (e.g. clauses 6-8 in test0011 and almost all of the early clauses in iffClausificationTest1)?
    - Do repeated clauses indicate that we're unnecessarily reproving things, and if so, how much does that impact efficiency?

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