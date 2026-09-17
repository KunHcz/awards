# Sources and attribution

## Mathematical result

The negative `m^(3/4)` question and the `K(n,n^2)` obstruction are recorded on [Erdős Problem 1008](https://www.erdosproblems.com/1008). That record attributes the original question to Bollobás and Erdős and the obstruction to Folkman, with the later problem appearing in Erdős, *Some unsolved problems in graph theory and combinatorial analysis* (1971), pp. 97–109. We inspected the problem record and its formal statement, not an original copy of the 1971 proceedings.

The counting method is classical. Conlon, Fox and Sudakov, [*Large subgraphs without complete bipartite graphs*](https://arxiv.org/abs/1401.6711), arXiv:1401.6711v1 (2014), Theorem 2.3, explicitly uses the Kővári–Sós–Turán counting argument to obtain the complete-bipartite obstruction. Section 3 of their later [*Short proofs of some extremal results II*](https://arxiv.org/abs/1507.00547) discusses the original history. The present pair-counting proof, its exact attaining construction and the negative answer are not claimed as new mathematical discoveries.

## Existing formalizations

The [problem forum](https://www.erdosproblems.com/forum/thread/1008) explicitly credits Boris Alexeev and Aristotle for formalizations of the **positive** `m^(2/3)` guarantee, including Hunter's constant `1/2`. Those are genuine existing achievements, not gaps to be claimed by this submission.

We inspected this pinned source:

- Repository: `plby/lean-proofs`.
- Revision: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- Path: [`src/v4.29.1/ErdosProblems/Erdos1008.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos1008.lean).
- Final theorem: `exists_C4_free_subgraph_with_many_edges`.

Its declaration chain counts cycles and proves the positive guarantee by probabilistic deletion. We did not locate the Folkman rectangular extremum or the negative three-quarters theorem in that file. The source is not imported, redistributed or copied, and we have not audited its full dependency environment. Its attribution remains with its authors.

The [reference statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1008.lean) was used to match the original `folkman` and `three_quarters` predicates. Its unfilled proofs are not assumptions in this package. The adapted statements retain Apache-2.0 attribution in NOTICE. Only pinned mathlib modules are imported here.

## Search scope

On 17 September 2026 we checked the public problem page, its seven-comment forum and its proof-claims tab, plus targeted official issue/PR and public Lean-code queries. Query strings, returned matches, source hashes and the prior-proof Git blob comparison are recorded in [evidence/prior-art-check.json](evidence/prior-art-check.json).

These are targeted checks, not an exhaustive search for logically equivalent results. An empty keyword result does not establish worldwide priority. Existing positive proofs are explicitly distinguished rather than hidden behind an empty search result. Global first-formalization priority remains **undetermined**.

The broader `3/4`/`C4` search returned [PR #313](https://github.com/TheJustinSunPrize/awards/pull/313), its recipient issue #314, and [PR #418](https://github.com/TheJustinSunPrize/awards/pull/418). We inspected the PR descriptions at heads `e47d4733cfb1a3de9844698922d0c5157c96f2cb` and `ebe9378aa923d30c8e7eba2e124d6bfa91dd3bdb`. They address Erdős 573: respectively an all-vertex-count KST/Reiman upper bound and a finite-field lower construction. Their stated results are distinct from this exact rectangular extremum and the Folkman exponent obstruction. We did not import their code or claim to audit every internal lemma.

## Prize relationship

A matching JSP identifier has not been established. The submission requests problem correspondence or inclusion, with complete evidence for the original negative question and the exact rectangular variant. It does not alter an official solved/eligible/award status or claim someone else's positive proof. Mathematical discovery predates this work; the new work is this 2026 implementation and its verification package. Eligibility, contribution attribution, any shared priority and reward amount require organizer review.
