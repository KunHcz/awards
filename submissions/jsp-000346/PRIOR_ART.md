# Sources, attribution and priority boundary

## Precise comparison source

Kyle Pratt, *A “digested” proof of Erdős Problem #421*, a 19-page exposition linked from [the problem page](https://www.erdosproblems.com/421) as [this PDF](https://www.erdosproblems.com/static/421-Pratt.pdf). The inspected September 2026 snapshot identifies the exposition as last edited on 1 September 2026.

The comparison PDF has SHA-256:

```text
7d3852fd9b0eeb2ab9dbecbe9cf2a145b89c060f2e491d8064a823a49d55f8ba
```

Proposition 7.1, printed pages 17–18, displays an unconditional bound `(1/3-o(1))*sqrt(N)` and coefficient `1` under an additional density-one hypothesis. Its adjacent-product obstruction informed this work. The relevant pages were rendered and inspected as well as text-extracted in the initial submission.

The initial disjoint-triple argument gave coefficient `1/2`. The retained-successor argument then gave coefficient `1` without density one, with a fourth-root error. The new minimal block-crossing argument improves that finite error to `floor(log_2(floor(sqrt N)))`, with an even sharper inverse-factorial parameter choice. These arguments and the Lean implementation were developed in this work. **The comparison is to this pinned proposition**, not to every result in the literature. Pratt's weaker statements remain valid.

The original existence question is cited by Pratt and the official catalog to Erdős–Graham, *Old and new problems and results in combinatorial number theory* (1980), p.84. We checked that correspondence through those sources, not through an independently inspected copy of the book.

## Related public work

The original source search retrieved the problem page and its then 47-comment thread. These two related mathematical expositions were inspected in the initial comparison:

- Robby Sneiderman, [erdos-421-audit](https://github.com/Robby955/erdos-421-audit/tree/318c112c7a70879d98d86d8c3d9a280d77dadb35), `main.tex`.
- Animish Sharma, [Erdos / 421](https://github.com/Animish-Sharma/Erdos/tree/5c55362d54cf1f4af2ef2d1110a4c513cba54afd/421), `main.tex`.

They concern the density-one existence construction. We did not import, repackage or fully audit their proofs. Their contributions remain theirs. None of our necessary bounds is a substitute for their existence work.

The [reference Lean statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/421.lean) supplied the consecutive-interval predicate. It is not an assumed theorem or imported proof. The Apache-2.0 attribution is retained in NOTICE.

## Search and publication limits

The refreshed search found **[PR #470](https://github.com/TheJustinSunPrize/awards/pull/470)**, submitted by `green3sf` at 2026-09-17 04:38:05 UTC. Its pinned source `751ec8d4f50a620ff5eafa37033dc17bbd8882d3`, file `submissions/jsp-000346-uniform-deficit/ProductDeficit.lean`, proves the unconditional coefficient-one bound with a fourth-root error. The source was read directly; its SHA-256 is `6b111a26b75137c1e68883cfd7e487af95d28105d590f3ca849bbe15e287128b`. That submission publicly precedes this update and acknowledges our original half-root PR #457.

Accordingly, **coefficient one with a fourth-root error is not claimed here as a first public result**. The differentiating result of this update is the minimal-crossing bound with logarithmic and inverse-factorial errors. PR #470's code is not imported or copied. We read its source for comparison but did not rerun its package, and make no claim about independent official review of either submission. The recovered local implementation is retained as an intermediate argument, not evidence overriding another contributor's public priority.

`evidence/prior-art-check.json` contains the initial source-comparison record. `evidence/updated-prior-art-check.json` records the later targeted searches and any unavailable responses. An unsuccessful request is not treated as a zero-result search. Keyword and title/body matching do not establish proof equivalence, global novelty or priority. Independent expert comparison is requested.

The existing PR #457 is updated in place because these are strengthenings of the same contribution, not separate prize submissions. The unchanged larger question is not being marked solved. No confirmed recipient identity, award amount or eligibility is asserted.

**Worldwide mathematical discovery priority, first-formalization priority, official eligibility and reward remain undetermined.** No construction attaining the bound or proof of its optimality is supplied. The copied definitions, Lean and mathlib retain their original ownership; the mathematical papers are not redistributed.
