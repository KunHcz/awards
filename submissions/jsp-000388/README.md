# JSP-000388: the complete quadratic obstruction

## English

This package proves the **complete quadratic case** of Erdős 477: no integer polynomial
of degree exactly two has an additive complement giving exactly one representation of
every integer as `a + f(x)`, where uniqueness is counted by the pair **`(a, f(x))`**.
It covers every `a*x^2+b*x+c` with `a != 0`, without requiring `a` to divide `b` or `b` to
be nonzero, and treats both signs of the leading coefficient.

The [source](JSP388.lean) contains thirteen audited theorems: a general non-tiling
criterion, the unrestricted coefficient argument, a bridge to actual `Polynomial Int`
values of degree two, and the positive linear boundary example.

This is a formalization of the known quadratic obstruction, not the positive existence
result for higher-degree polynomials. In particular, it does **not** solve the full
JSP-000388 existence question or the separate cubic question.

## Reproduce

The package pins Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; the manifest pins the other eight dependencies.
With the official Lean toolchain manager installed, run inside this directory:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Data.ZMod.Basic Mathlib.Data.Set.Finite.Lattice Mathlib.Algebra.Polynomial.Eval.Degree
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The last command writes to `verification-output/`, preserving the recorded evidence.
Published logs redact machine paths; trailing blank-line spaces in the negative-control log were removed.
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
The proposed formalization recipient is `RECIPIENT-jsp-000388-A`, pending authorized confirmation.
This self-submission has a direct interest in the review outcome. No recipient identity,
curator signature, award decision, eligibility flag, payment arrangement, or private contact
is asserted or modified.

`submissions/` is a proposed intake location, not a new candidate-record schema.
Please determine whether this explicitly scoped contribution qualifies, including the
2026 completion rule for a new formalization of an older mathematical result, and arrange
any required independent checking and permanent archival. Priority is not established by
our search, a successful build, or this document. The package is licensed under
[Apache 2.0](LICENSE). Source material retains its own attribution and rights.
