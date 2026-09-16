# Prior art, source rights and review status

## Mathematical sources

- Erdős Problem 751: https://www.erdosproblems.com/751
- J. A. Bondy and A. Vince, *Cycles in a graph whose lengths differ by one or two*, Journal of Graph Theory (1998), 11–15.
- N. G. de Bruijn and P. Erdős, *A colour problem for infinite graphs and a problem in the theory of relations*, Indagationes Mathematicae (1951), 369–373.

The infinite extension is the standard compactness consequence of a finite theorem. We make no claim to new mathematics.

## Existing formalization

The finite theorem is by SpringSense Innovation Institute, recorded in the statement repository as assisted by ChatGPT:

https://github.com/SpringSense-Innovation-Institute/ai-for-math-lean/blob/ae3ead960a494cf81b28541c477e50997cb03999/erdos-problems/erdos751/Erdos751/Main.lean

That snapshot contains the theorem `Erdos751.Main.erdos_751_strong` with a `Fintype` hypothesis on the vertex type. Its helper development is approximately 151 KB of Lean source. We fetched it without changes, rebuilt the relevant modules from source and audit the imported final theorem separately. No authorship of those files is claimed.

The need to finish the arbitrary-graph version is expressly documented in:

https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/751.lean

The comment says the finite-to-infinite step has not been formalized there. It also says mathlib lacks de Bruijn–Erdős; however, the sufficient compactness theorem is already present as `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` in the pinned mathlib snapshot:

https://github.com/leanprover-community/mathlib4/blob/37df177aaa770670452312393d4e84aaad56e7b6/Mathlib/Combinatorics/SimpleGraph/Finsubgraph.lean

Our use of that existing compactness theorem is explicit and not presented as a newly proved compactness result. The contribution is the integration, cycle lifting and complete quantified conclusions.

## Rights of the finite-proof source

No explicit license was located for the finite-proof snapshot: the repository license API returned 404, and the inspected Lean files did not contain license notices. Therefore **no third-party proof source is included in this submission's tracked files**. The reproduction script downloads the fixed public files from their original owner, verifies their hashes, and keeps them in the ignored `.upstream` directory. It does not change or relicense them.

Permanent redistribution or archival of those files is a separate permissions matter for the authors and reviewers. Our extension, verification scripts and documentation are licensed under the included Apache-2.0 license; that license does not apply to the fetched third-party development.

## Catalog and priority

We did not identify an exact matching numbered JSP entry in the catalog snapshot examined. The number **751 is an Erdős problem number**, not a JSP identifier. A catalog recommendation or correspondence determination is requested; no current entry's solved, claim or eligibility flag is altered.

The relevant public statement, pinned finite source, current main file, available code-search results and prize issue/PR search for the original problem number were checked on 16 September 2026. We did not locate an earlier arbitrary-vertex extension in those checks, but absence from limited searches does not establish worldwide first-formalization priority.

No prize eligibility decision, independent human review, designated verification or award has occurred. The exact additional contribution, rights, source scope and catalog relationship remain subjects for review.
