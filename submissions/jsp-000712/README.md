# JSP-000712: exact positive rational densities of divisor-subset sums

For every fixed natural target `t`, the integers whose distinct divisors can sum to `t` have an
**existing, positive, rational natural density**. The proof supplies a finite algorithm for that
rational number and a uniform bound on the counting error. It proves convergence of the actual
ratio of qualifying integers in `[1,N]`, not a statement conditional on a density existing.

**This does not settle the asymptotic question as `t` tends to infinity in Erdős 859 / JSP-000712.**
No logarithmic decay rate, asymptotic constant, or improvement on Erdős's bounds is claimed.
The finite-period method is classical; no new mathematical discovery is asserted.

The [Lean source](JSP712.lean), [statement correspondence](STATEMENT.md), [prior-art review](PRIOR_ART.md),
and [verification record](evidence/verification.json) specify the exact result.
Suggested unconfirmed recipient placeholder: `RECIPIENT-JSP000712-A`.

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
