# TODO

Inference rules:
- Unimplemented rules:
  - NeqHoist
  - ForallHoist
  - ExistsHoist
  - BoolRw
  - ForAllRw
  - ExistsRw

Bugs:
- The following problem fails
  ```
  set_option trace.Rule.boolSimp true in
  tptp ITP209_2 "../TPTP-v8.0.0/Problems/ITP/ITP209_2.p"
  by duper
  ```
  because rule 18,22,23,26,27 does not deal with ```forallE``` correctly, causing the body to contain loose bound variable, eventually leading to the failure of ```inferType```. Maybe we should use ```forallTelescope```.

Infrastructure
- precCompare: Support for higher-order problem
- TPTP higher-order problem parsing
- Performance-tuning higher-order unification procedure
- Change ```replaceAtPos!``` to ```replaceAtPosUpdateType?```
- For superposition, it might still make sense to test early whether a subterm is **depended** by another term because then we don't even need to add it to our term index. That would save us quite a bit of computation.
- Also the current implementation of ```Lit.map``` and ```Lit.mapM``` is questionable. If $t : \alpha$ (at term level) and $f : Expr \to Expr$ (at meta level) is a function, then we probably do not always have $f \ t : f \ \alpha$. Currently it doesn't cause problem, but I expect there to be problems when we add support for dependent types. I think we should probably only map to ```lhs``` and ```rhs```, and then update the type using ```Meta.inferType```.
- Make ```ClausePos``` an extension of ```LitPos```

Simplification rules:
- Semantic tautology deletion?
- Equality subsumption?

Refactoring to consider:
- Use mvars in Clause to avoid cost of conversion?

Other:
- Investigate the "nondeterminism" (behavior that changes depending on unrelated prior declarations) exhibited by ITP023_1 (duper times out on
  ITP023_1 even if given a lot of time if ITP023_1 is the only thing declared, but can solve ITP023_1 relatively quickly if SWV573_5 is declared/
  solved first)
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
- Add inter-simplification to more faithfully implement immediate simplification
- Investigate why the current implementation of orphan elimination (removeDescendants) worsens performance on average

## For later:

Clausification
- preprocessing version of clausification?
- Tseitin transformation?

Heuristics:
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