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
- Semantic tautology deletion?
- Positive/Negative simplify-reflect
- Equality subsumption?

Refactoring to consider:
- Use mvars in Clause to avoid cost of conversion?

Known bugs/issues (bugs.lean):
- Premature saturation instances:
  - PUZ137_8 achieves premature saturation because our current interpretation of $o/$oType in tff isn't correct. Currently, we interpreting $o/$oType
    as Prop, but there is an important sense in which we should at least sometimes be interpreting it as Bool. PUZ137_8 is one such instance.
    - Though at present, I don't know that fully interpreting $o/$oType as Bool would necessarily work either

Other:
- Improve indexing functions for fingerprint indices
  - Current fingerprint function was arbitrarily copied from http://www.eprover.eu/EXPDATA/FP_INDEX/schulz_fp-index_ext.pdf. Explore whether other
    fingerprint functions would be better (in particular, functions that include more features)
- Look into whether superposition and demodulation are taking an excessive amount of time eliminating bad potential partners. If so, we might be
  able to save some time by checking the type of potential partners sooner (currently, we don't check until Unif.lean/Match.lean). The reason this
  might be helpful is that whenever I look for potential unification targets for a metavariable, I'm finding *everything* in the index. This is
  appropriate and necessary in FOL, but for our setting, the types should be able to rule most of these bad potential partners out.
  - Even better than checking the types earlier in superposition/demodulation would be to check them in the indexing structures. If we indexed
    expressions not just to their Clause X ClausePos pair, but to a Clause X ClausePos X Expr type (with the final Expr being the type of the
    indexed subexpression), then when we search for e's unification partners, we can easily return only those whose type is compatible with e's.
  - Alternatively, we could add a top-level component to RootCFPTrie so that rather than just having one root ClauseFingerprintTrie, we have a
    HashMap from types to ClauseFingerprintTries (where, if type tau maps to ClauseFingerprintTrie t, then t only indexes expressions of type tau).
    I don't think this would significantly increase memory, and depending on how much time is being wasted eliminating bad potential partners in
    superposition.lean and demodulation.lean, it might save a lot of time.
- Because the types of SimpRule and BackwardSimpRule were changed to take Clauses rather than MClauses as input, calling loadClause has
  been moved from Simp.lean to the beginning of each simplification rule. This isn't a problem, but there are some places where it may not
  be necessary to call loadClause. Going through the simplification rules and changing them to only call loadClause if it is actually required
  may make some of the simplification rules more efficient
  - Prior to profiling, it is unclear to me whether this improvement would be significant, because it is has the potential to remove many
    calls to loadClause, or negligible because loadClause is implemented efficiently
- Update Expr.weight function to be more similar to Zipperposition's ho_weight function
- Unit tests, e.g. for the ordering. (How do unit tests work in Lean 4?)
- Command line version of duper?
- Currently, we have a hacky implementation of removing clauses from fingerprint indexes (tacking on a filter before retrieving). If this turns out to be
  too inefficient, implement removal from fingerprint indexes properly.

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