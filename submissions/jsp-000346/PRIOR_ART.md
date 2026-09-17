# Sources, attribution and priority boundary

## Precise comparison source

Kyle Pratt, *A “digested” proof of Erdős Problem #421*, 19-page proof exposition, available from [the problem page](https://www.erdosproblems.com/421) as [this PDF](https://www.erdosproblems.com/static/421-Pratt.pdf). The public problem page identifies the exposition as last edited on 1 September 2026.

The PDF examined on 17 September 2026 has SHA-256:

```text
7d3852fd9b0eeb2ab9dbecbe9cf2a145b89c060f2e491d8064a823a49d55f8ba
```

Proposition 7.1, printed pages 17–18, states an unconditional omission bound `(1/3 - o(1)) sqrt(N)` and, separately, `(1 - o(1)) sqrt(N)` under the additional density-one hypothesis. Its proof supplies the adjacent-product obstruction used here. Those pages were rendered and visually inspected as well as text-extracted.

Our disjoint selection of obstruction triples, finite fourth-root-error bound and complete Lean implementation were independently produced in this work. The resulting coefficient `1/2` strengthens the **displayed unconditional bound in this pinned source**. It is not a correction of an invalid theorem: Pratt's weaker bound remains true. It does not improve the density-one coefficient `1`.

The exact original question appears in Erdős–Graham, *Old and new problems and results in combinatorial number theory* (1980), p. 84, as cited by Pratt and the official catalog. We checked the correspondence through those sources, not an independently inspected copy of that book.

## Other inspected public material

The current problem page and its 47-comment forum thread were retrieved during the search. The following related mathematical expositions were also checked for the claimed omission-bound comparison:

- Robby Sneiderman, [erdos-421-audit](https://github.com/Robby955/erdos-421-audit/tree/318c112c7a70879d98d86d8c3d9a280d77dadb35), `main.tex`.
- Animish Sharma, [Erdos / 421](https://github.com/Animish-Sharma/Erdos/tree/5c55362d54cf1f4af2ef2d1110a4c513cba54afd/421), `main.tex`.

These sources concern the density-one existence construction. We did not import or repackage their formal proofs, nor audit their whole dependency chains. Their mathematical contributions remain theirs. Failure to locate a matching `1/2` statement in this limited search is not evidence of worldwide first priority.

The [reference Lean statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/421.lean) supplied the exact consecutive-interval predicate. It is a statement source, not an assumption or proof imported into this package. Attribution and the Apache 2.0 notice are retained in NOTICE.

## Submission search and limitations

The accompanying `evidence/prior-art-check.json` records targeted official issue/PR and public-code searches. Such keyword and title/body searches cannot establish mathematical equivalence, global novelty, or priority. Human review of the comparison and attribution is requested.

The contribution is a new implementation and an independently derived strengthening relative to the specified source. **Global mathematical discovery priority, first-formalization priority, award eligibility and amount remain undetermined.** The broader catalog entry is not being marked solved, and no award or recipient identity is asserted.
