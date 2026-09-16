# Prior art and contribution boundary

## English

The earlier formalized quadratic result is recorded at
[Formal Conjectures commit 24a4308](https://github.com/google-deepmind/formal-conjectures/blob/24a4308a38b97e3e5b7da6ccff57157de432a1c1/FormalConjectures/ErdosProblems/477.lean#L44).
It came from the AlphaProof example `x^2-x+1` and the subsequent restricted-coefficient
generalization. That older file also restricts polynomial inputs to positive integers;
this package uses the full integer value set in the current problem. We do not claim
that enlarging the input domain proves every positive-input variant. The current [reference statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/477.lean) still identifies the
`a | b`, `a != 0`, `b != 0` variant separately from the square case.

The general difference identities and pigeonhole argument are explained by Sarosh
Adenwalla in [the original discussion](https://www.erdosproblems.com/forum/thread/477).
Those mathematical ideas are not claimed as new. Our contribution is the present
unrestricted Lean proof, including negative leading coefficients, zero linear
coefficient, arbitrary complements, a polynomial-degree bridge, and a reusable
lattice-plus-bound criterion.

No same-ID official pending PR was located in the initial `JSP-000388` search, and the
batch registrations in PR #40 were considered. Code searches for `Erdos477` and broader
quadratic/complement terms did not establish an earlier full-scope implementation.
These searches are limited by indexing and naming. We make no first-formalization
claim and invite review against any earlier proof. The earlier restricted proof must
retain its own credit. Submission-time checks appear in
[evidence/prior-art-check.json](evidence/prior-art-check.json).

No part of this contribution claims the separate construction of exact complements to
higher even powers, or a resolution of the cubic case. No catalog or award status is
changed by this package.
