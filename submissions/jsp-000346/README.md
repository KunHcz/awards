# JSP-000346 / Erdős 421: an unconditional half-root omission bound

For an increasing sequence whose distinct nonempty consecutive blocks have different products, let `E(N)` count the positive integers at most `N` omitted by the sequence. This package proves, for every natural `N`,

\[
 E(N)\ge\frac{\sqrt N-\sqrt{\sqrt N}-3}{2}.
\]

It also proves that for every `epsilon > 0`, at **every sufficiently large** `N`,

\[
 E(N)\ge(1/2-\epsilon)\sqrt N.
\]

**No density hypothesis is imposed.** This independently derived disjoint-triple argument strengthens the coefficient `1/3` in the arbitrary-set part of Kyle Pratt's Proposition 7.1. It does not improve that proposition's separate coefficient `1` under the additional density-one hypothesis. The comparison is to the specific source version recorded in [PRIOR_ART.md](PRIOR_ART.md), not a claim of worldwide priority.

The stronger finite integer formula gives `E(100000000) >= 4949`. Its validity for all cutoffs comes from the Lean proof, not numerical sampling.

## Scope and status

This is a quantitative contribution related to **JSP-000346**, not a new proof of the catalog's density-one existence theorem. That theorem and its earlier contributors retain their attribution. This package neither establishes the best possible coefficient for product-distinct sets nor constructs a density-one set with optimal omission count.

[Source](JSP346.lean) contains 17 audited theorems. [PROOF.md](PROOF.md) gives the mathematical argument; [STATEMENT.md](STATEMENT.md) explains its exact connection to the original consecutive-block condition. [Verification](evidence/verification.json) records local checking only. Official statement review, independent verification, eligibility, priority and any reward remain undetermined. The suggested recipient is `RECIPIENT-JSP-000346-A`, pending authorized confirmation. This self-submission has an interest in the review outcome. No official records or award flags are changed.

## Reproduce

With the official Lean toolchain manager installed, run in this directory:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Data.Nat.Sqrt
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The package pins Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`; all nine Git dependencies are fixed by the manifest. The verifier checks these revisions, rebuilds this package with warnings treated as errors, audits every named theorem, and runs the complete imported-and-local `leanchecker --fresh` replay. It rejects three mathematical mutations plus false arithmetic, a placeholder and a custom assumption. Reproduction writes to `verification-output/`, preserving the submitted evidence.

The replay uses the same official Lean kernel, not an independently implemented checker or human reviewer. Cached dependencies are kernel-replayed, not all recompiled from source. Python tests include exact bounded hitting-set searches and count checks; they are not the universal mathematical proof. The prize repository's record tests do not verify the Lean mathematics.

Licensed under [Apache 2.0](LICENSE); see [NOTICE](NOTICE) for attribution.
