# Attribution and prior-art screening

## English

This contribution claims implementation and checking of a Lean formalization, not discovery of the underlying mathematical construction.

The [Erdős problem 1209 page](https://www.erdosproblems.com/1209), read on 2026-09-16, already gives a diagonal construction for the first prime-translate question and says that a squared-modulus version answers the squarefree question. It does not identify a first discoverer/date for that construction. We do not assign those credits to ourselves or invent them.

The page separately credits Enrique Barschkis and GPT for the fixed-sequence result about `n+2^(2^k)` never being always prime. Its linked [Lean formalization](https://github.com/ebarschkis/ErdosProblem/blob/main/Problem1209/Formalization.lean) is a distinct result, outside our claim. We do not assert that the full group of questions under 1209 has been solved.

The [reference statements](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1209.lean) distinguish the first two questions from those fixed-sequence variants. We used that exact source revision for quantifier comparison, without importing it as an assumption library.

At 2026-09-16 11:49:31 UTC, the live GitHub API returned 27 pull requests, including closed ones, in TheJustinSunPrize/awards. A search of all returned titles and bodies for the problem IDs `1014` and `1209`, and related prime-translate/squarefree-shift phrases, found no matching submission. The result fits on one page; no further page was omitted. This is a bounded intake-duplication check, not proof of world-wide novelty or a reserved priority timestamp.

GitHub code searches and inspection of known linked repositories were also performed. Search indexing was demonstrably incomplete, including omission of a known reference file, so zero results are not treated as evidence that no earlier formalization exists. First-formalization priority remains unestablished and subject to review.

The implementation was prepared with ChatGPT assistance on 2026-09-16. The submitting account has a direct interest in the outcome. Local checking is not independent human review; no curator, verifier, or recipient confirmation is claimed. Proposed formalization recipient: `RECIPIENT-jsp-001014-A`, pending authorized confirmation.
