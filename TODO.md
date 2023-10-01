# TODO

I’ve listed some action items that could be taken to improve Duper. Most of these were previously
listed in the earlier version of TODO.md, though I have removed some, changed some, and added new ones.

- Better definition support (currently, we add the definition as a lemma, but we don’t enforce
  that that the definition ought to be unfolded). There are several examples in which the current
  handling of definitions appears to significantly hinder Duper’s ability to solve a problem.
- Improving Duper’s inhabitation reasoning. Several of Duper’s current known bugs and limitations
  pertain to inhabitation reasoning, so expanding and/or restructuring Duper’s inhabitation reasoning
  could enable Duper to solve a variety of problems that it currently can not
- Making curated collections of theorems tailored to particular problem domains. Examples
  include continuity lemmas, category theory lemmas, group lemmas, etc.
- Finishing implementing inference rules:
  - BoolRw
  - ForAllRw
  - ExistsRw
- Adding additional simplification rules:
  - Semantic tautology deletion?
  - Equality subsumption?
- Infrastructure changes to better handle dependent terms:
  - For superposition, it might still make sense to test early whether a subterm is **depended** by
    another term because then we don't even need to add it to our term index. That could save us quite a
    bit of computation.
  - The current implementation of ```Lit.map``` and ```Lit.mapM``` is questionable. If $t : \alpha$
    (at term level) and $f : Expr \to Expr$ (at meta level) is a function, then we probably do not always
    have $f \ t : f \ \alpha$. Currently it doesn't cause problem, but I expect there to be problems if we
    add support for dependent types. I think we should probably only map to ```lhs``` and ```rhs```, and
    then update the type using ```Meta.inferType```.
- Improve indexing functions for fingerprint indices
  - Current fingerprint function is from http://www.eprover.eu/EXPDATA/FP_INDEX/schulz_fp-index_ext.pdf.
    Explore whether other fingerprint functions would be better (especially those with more features)
- Look into whether superposition and demodulation are taking an excessive amount of time eliminating bad
  potential partners. If so, we might be able to save some time by checking the type of potential partners
  sooner (currently, we don't check until Unif.lean/Match.lean). The reason this might be helpful is that
  whenever I look for potential unification targets for a metavariable, I'm finding *everything* in the index.
  This is appropriate and necessary in FOL, but for our setting, the types should be able to rule most of these
  bad potential partners out.
  - Even better than checking the types earlier in superposition/demodulation would be to check them in the
    indexing structures. If we indexed expressions not just to their Clause X ClausePos pair, but to a
    Clause X ClausePos X Expr type (with the final Expr being the type of the indexed subexpression), then when
    we search for e's unification partners, we can easily return only those whose type is compatible with e's.
  - Alternatively, we could add a top-level component to RootCFPTrie so that rather than just having one root
    ClauseFingerprintTrie, we have a HashMap from types to ClauseFingerprintTries (where, if type tau maps to
    ClauseFingerprintTrie t, then t only indexes expressions of type tau). I don't think this would significantly
    increase memory, and depending on how much time is being wasted eliminating bad potential partners in
    superposition.lean and demodulation.lean, it might save a lot of time.
- Because the types of SimpRule and BackwardSimpRule were changed to take Clauses rather than MClauses as input,
  calling loadClause has been moved from Simp.lean to the beginning of each simplification rule. This isn't a
  problem, but there are some places where it may not be necessary to call loadClause. Going through the
  simplification rules and changing them to only call loadClause if it is actually required may make some of the
  simplification rules more efficient
  - It is presently unclear to me whether this improvement would be significant, because it is has the potential
    to remove many calls to loadClause, or negligible because loadClause is implemented efficiently
- Use mvars in Clause to avoid cost of constantly converting between the Clause and MClause representations?
- Update Expr.weight function to be more similar to Zipperposition's ho_weight function
- Currently, we have a hacky implementation of removing clauses from fingerprint indexes (tacking on a filter
  before retrieving). If this turns out to be too inefficient, implement removal from fingerprint indexes properly.
- Add inter-simplification to more faithfully implement immediate simplification
- Investigate why the current implementation of orphan elimination (removeDescendants) worsens performance on average