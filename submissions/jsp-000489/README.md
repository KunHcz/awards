# JSP-000489: countable-family splitting with infinite color classes

For every sequence of infinite sets on an arbitrary ground type, this package constructs one
coloring by the natural numbers such that **every set contains infinitely many points of every
color**. In particular, every positive finite number of colors works, and Bernstein's Property B
lemma for a countable family follows without any restriction on pairwise intersections.

**This does not settle the uncountable-index question in Erdős 602 / JSP-000489.**
A sequence of sets is a countable family, even when the sets or their union are uncountable.
Dropping restrictions on intersections does not remove the countable-index assumption.

The [proof](JSP489.lean) contains eight audited theorems. The [statement correspondence](STATEMENT.md)
and [prior-art assessment](PRIOR_ART.md) separate this contribution from existing disjoint-family
and single-set proofs. Suggested unconfirmed recipient placeholder: `RECIPIENT-JSP000489-A`.

## Reproduction and trust boundary

The package pins Lean 4.34.0 (commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`),
mathlib `5ed2965256430c3649e86755f9576b54eca72435`, and all eight transitive Git dependencies.
Run from this package directory with that Lean version and Python 3.9 or later:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Tactic
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier preserves the bundled historical evidence by writing to `verification-output/`
by default. It checks dependency pins and source cleanliness, removes only the local package's
build outputs, rebuilds with warnings treated as errors, audits every theorem, and runs the
bundled `leanchecker --fresh` on the entire imported and local environment. Deliberately false
proofs and semantic mutations must be rejected. The verifier and exact inputs are hashed in
[evidence/verification.json](evidence/verification.json).

This is local verification by the submitter. The checker is Lean's own kernel implementation,
not a separately implemented checker or independent human reviewer. Pinned mathlib caches
were used and replayed; a complete source rebuild of all mathlib dependencies is not claimed.
Repository record validation is not mathematical verification, and local tests are not online CI.

## Attribution and submission status

This is a new implementation of known mathematics, developed with ChatGPT assistance for
submitter `KunHcz`. Worldwide first-formalization priority has not been established. This is a
self-submission with a direct interest in the outcome. Our original source and documentation
are [Apache-2.0](LICENSE); imported mathlib retains its own attribution and license.

No catalog, candidate, award, eligibility, recipient-identity, or payment record is changed.
Please review statement fidelity, exact contribution, prior art, eligibility, required independent
verification, and any archival requirements. A submitted PR and successful local checks do not
constitute an award. The broad catalog problem is not declared solved by this scoped contribution.
