# JSP-000346 / Erdős 421: omission bounds from minimal block crossings

Let `d` be a strictly increasing sequence of natural numbers whose distinct nonempty consecutive blocks have different products. Let `E(N)` count the positive integers at most `N` omitted by its range, and put `M=floor(sqrt(N))`.

The strongest finite result in this package is

\[
 \boxed{M < (L+1)!\quad\Longrightarrow\quad M\le E(N)+\max(L-1,0)}
\]

for **every natural `N` and `L`**. Choosing the smallest qualifying `L` gives an explicit inverse-factorial error. A convenient consequence is

\[
 \boxed{\lfloor\sqrt N\rfloor\le E(N)+\lfloor\log_2\lfloor\sqrt N\rfloor\rfloor,}
\]

where the natural-number logarithm of zero is defined as zero. Neither result assumes density one. Two separately proved numerical corollaries give

- `E(100000000) >= 9994`, using `10000 < 8!`;
- `E(1000000000000) >= 999992`, using `1000000 < 10!`.

These statements concern every qualifying sequence, not sampled examples.

## What changed

The first version of PR #457 proved an unconditional half-root bound from an ambient adjacent-product obstruction. The retained-successor argument then gave coefficient one with a fourth-root error. **Minimal block crossings now replace that error by a logarithmic bound, and by the stronger exact factorial-parameter bound above.** All earlier results remain in the source.

The comparison source is Kyle Pratt's Proposition 7.1, which displays coefficient `1/3` without a density assumption and coefficient `1` with density one. This package strengthens that specified comparison; it neither claims worldwide priority nor asserts an optimal bound. See [PRIOR_ART.md](PRIOR_ART.md).

An earlier public submission, [PR #470](https://github.com/TheJustinSunPrize/awards/pull/470), already gives unconditional coefficient one with fourth-root error. The new differentiating contribution here is the **logarithmic and inverse-factorial error**, not a claim to be the first public coefficient-one proof.

## Proof and scope

For most retained values below `M`, multiply consecutive retained terms until the product first exceeds `M`. That product is at most `M^2`, is absent from the sequence, and differs from every other block's product. Missing inputs map to themselves below `M`. Discarding at most `L-1` terminal starts makes this an injection of at least `M-(L-1)` integers into the omissions. The factorial bound guarantees a crossing in at most `L` factors.

[PROOF.md](PROOF.md) gives the full argument. [STATEMENT.md](STATEMENT.md) maps the declarations to the literal original condition. This is a **quantitative component of JSP-000346**, not a proof of its density-one existence theorem or a construction attaining the omission bound. No official catalog, award, eligibility or recipient record is changed.

## Verification

[Source](JSP346.lean) contains 54 audited theorem declarations, including the original 17. [Verification](evidence/verification.json) records local checks, not official adjudication. Eleven negative controls cover erroneous proof assumptions, the older local/retained distinctions, nonminimal crossings and omitted terminal exceptions. Twenty-five package tests include independent exact-integer checks and exhaustive small finite sets. Test counts are not counts of solved problems.

Reproduce from this directory with the official Lean toolchain manager installed:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Data.Nat.Sqrt Mathlib.Data.Nat.Factorial.BigOperators Mathlib.Data.Nat.Log
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435` are pinned. The manifest fixes all nine Git dependencies. The verifier checks pins and cleanliness, rebuilds with warnings as errors, audits every theorem's axioms, and runs `leanchecker --fresh` over the complete imported-and-local environment. Reproduction writes to `verification-output/`, preserving submitted evidence.

The replay uses the same official Lean kernel, not an independently implemented checker or a human reviewer. Cached dependencies are replayed, not all rebuilt from source. Repository-record tests do not verify mathematics. Eligibility, priority and reward remain undetermined. Suggested recipient: `RECIPIENT-JSP-000346-A`, pending confirmation; this self-submission has an interest in the review outcome.

Licensed under [Apache 2.0](LICENSE); see [NOTICE](NOTICE).
