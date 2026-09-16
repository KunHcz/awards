# JSP-000226: the Borwein–Loring infinite family

## English

This package proves the **infinitude subproblem** of Erdős 261: infinitely many positive
integers `n` admit a decomposition of `n / 2^n` into at least two terms `a / 2^a` with distinct
positive integer `a`. It formalizes the classical Borwein–Loring family, not the full broad
JSP-000226 entry. It does **not** prove the assertion for every positive `n`, or any
continuum-cardinality claim about infinite-series representations.

For every `m >= 2`, let `n = 2^(m+1) - m - 2`. The proof establishes

```text
n / 2^n = sum from i=1 to m of (n+i) / 2^(n+i).
```

The smallest example is `4/16 = 5/32 + 6/64`; the next family members are `11, 26, 57`.
The formal proof quantifies over all natural `m`, not a finite numerical sample.
[Source](JSP226.lean) contains six audited theorems, including the exact rational identity,
the distinctness and positivity of the terms, and unboundedness of the family.

## Reproduce

The package pins Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; the manifest pins the other eight dependencies.
With the official Lean toolchain manager installed, run inside this directory:

```sh
lake exe cache get Mathlib.Tactic
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The last command writes to `verification-output/`, preserving the recorded evidence.
It checks dependency revisions and tracked source cleanliness, deletes only this package's
build outputs, rebuilds with warnings treated as errors, audits every theorem, and runs
`leanchecker --fresh` on all imported and local constants. It also executes five negative
controls. See [the script](scripts/verify.py), [configuration](verification-config.json),
and [recorded verification](evidence/verification.json).

The bundled checker uses the same Lean kernel, not a separately implemented checker.
Precompiled dependency caches were used; they were kernel-replayed, not rebuilt entirely
from source. This is local verification by the submitting project, not independent human
review or official prize verification. The original repository CI checks records, not this proof.

## Attribution and intake

This is AI-assisted formalization work, not a new mathematical discovery. See
[statement correspondence](STATEMENT.md) and [prior art](PRIOR_ART.md).
The proposed formalization recipient is `RECIPIENT-jsp-000226-A`, pending authorized confirmation.
This self-submission has a direct interest in the review outcome. No recipient identity,
curator signature, award decision, eligibility flag, payment arrangement, or private contact
is asserted or modified.

`submissions/` is a proposed intake location, not a new candidate-record schema.
Please determine whether this explicitly scoped contribution qualifies, including the
2026 completion rule for a new formalization of an older mathematical result, and arrange
any required independent checking and permanent archival. Priority is not established by
our search, a successful build, or this document. The package is licensed under
[Apache 2.0](LICENSE). Source material retains its own attribution and rights.
