# TODO

Inference rules:
- Equality Factoring inference rule
- check for strict maximality in superposition rule
- perform superposition only on maximal sides of main premise literal
- Check ordering constraints before unification
- Check whether a clause is still in active set when retrieving it from an index. (Or alternatively, remove clauses from indices when they are removed from active set)

Simplification rules:
- proof reconstruction for clausifyPropEq
- Semantic tautology deletion?
- Destructive Equality Resolution
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

## For later:

Clausification
- preprocessing version of clausification?
- Tseitin transformation?

Heuristics:
- LPO Ordering
- Precedence heuristics for ordering
- Literal selection heuristics
- Next given clause heuristics