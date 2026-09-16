# Prior art and attribution

Primary problem: https://www.erdosproblems.com/602

Pinned reference statement (not an imported proof dependency):
https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/602.lean

Catalog snapshot:
https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000489

The problem is attributed to Komjáth by the problem page. Bernstein's countable-family lemma
is explicitly identified in the reference statement. Disjoint-family and very small-index
variants already have proofs there; they are not claimed as new contributions. The countable-index
variant is unfilled in that snapshot. Our implementation proves the stronger classical countable
palette version with infinite fibers. It does not solve arbitrary uncountable-index Property B.

## Search limits

Before implementation we checked the corresponding official issue/PR identifiers and the original
problem number, as well as indexed Lean code. No matching submission was found in those specific
queries. The final pre-publication query results are recorded in `evidence/prior-art-check.json`.
Code indexing is incomplete; a result count of zero does not establish absence or worldwide priority.
No first-formalization claim is made. Maintainers should review overlapping or earlier work.

Our original implementation is not copied from a third-party proof. Mathematical sources retain
their attribution, and mathlib retains its license. The contribution must still undergo official
statement, priority, eligibility and independent-checker review. No award is announced here.
