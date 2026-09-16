# A counterexample to the TUZ exponent bound

**Result:** Conjecture 3.7 of Tengely–Ulas–Zygadło, arXiv:2008.01501v1 (2020), is false as stated for all finite decompositions. An explicit solution has `n = 2`, `k = 185`, and largest exponent `392`, whereas the proposed upper bound is `2(n+k) = 374`.

The same list also works for `n = 1`; we use `n = 2` throughout the main certificate, and its first exponent is `n + 1 = 3`. All exponents are distinct positive integers in strictly increasing order.

This is an independently discovered counterexample and Lean formalization, not a translation of the classical Borwein–Loring family in [PR #60](https://github.com/TheJustinSunPrize/awards/pull/60). Worldwide priority is **not established** by the searches recorded here. The original paper’s Corollary 3.6 already supplies ingredients for a longer 191-term counterexample; see [PRIOR_ART.md](PRIOR_ART.md). This is a statement-correction and certificate submission, not an unqualified claim to a new mathematical breakthrough. No award is claimed.

## Exact scope

The target is the **universal upper bound** `a_k <= 2(n+k)` in Conjecture 3.7 of [the source paper](https://arxiv.org/abs/2008.01501). The conjecture as printed does not restrict solutions to greedy or minimum-length representations. Our counterexample is not greedy: for `n=2`, the greedy representation already uses `{3,6,8}`.

The result does not settle a greedy-only reformulation, the weaker exponential bound `a_k <= 4(2^k-1)`, the all-positive-`n` existence question, or the infinite-series questions associated with Erdős 261. The verified counterexample preserves the lower inequality `n+k <= a_k`.

The work is related to **JSP-000226**, but we request a separately scoped proposition record or a scope determination by the maintainers. We do not change the combined catalog entry to solved, eligible, or awarded. This proof is distinct from PR #60, which only formalizes a pre-existing infinite family.

## Evidence

- [PROOF.md](PROOF.md): complete witness, exact integer certificate, and statement correspondence.
- [DyadicBound.lean](DyadicBound.lean): 11 checked declarations, including the negation of the entire universally quantified bound.
- [witness.json](witness.json): exact exponent list.
- [evidence/verification.json](evidence/verification.json): clean rebuild, all declaration axiom audits, fresh-environment kernel replay, and six negative controls.
- [evidence/independent-arithmetic.json](evidence/independent-arithmetic.json): independent Python rational and integer calculations.
- [PRIOR_ART.md](PRIOR_ART.md): source and priority qualifications.

The Lean replay uses the same Lean kernel, not an independent implementation. Independent human review and official prize verification have not occurred. The proof uses no placeholder, unproved auxiliary assumption, or native-evaluation oracle.

## Reproduce

Use Python 3.9+ and the Lean version in `lean-toolchain` (Lean 4.34.0). The manifest and lakefile pin mathlib and its dependencies.

```sh
python3 scripts/check_witness.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
lake update
lake exe cache get Mathlib.Tactic
python3 scripts/verify.py
```

`verify.py` removes only this package's generated `.lake/build`, rebuilds with warnings as errors, audits all target declarations, and replays imported and local logical declarations from an empty environment. It also rejects a changed exponent, repeated exponent, wrong right-hand side, false arithmetic, a placeholder proof, and an added assumption.

To reproduce discovery, rather than trusting discovery output as a proof:

```sh
c++ -O3 -std=c++17 -Wall -Wextra -Werror scripts/search_dyadic_bound.cpp -o /tmp/search_dyadic_bound
/tmp/search_dyadic_bound 392
```

The search reports `n=1`; replacing it by `n=2` leaves the left side unchanged. The independent verifier and Lean proof both check the `n=2` witness with its more permissive bound directly. No minimality or optimality claim is made.

## Attribution and review request

The conjecture is due to Szabolcs Tengely, Maciej Ulas, and Jakub Zygadło. The counterexample search, verification and formalization in this package were developed with ChatGPT assistance for submitter `KunHcz`. This is a self-submission with a direct interest in its evaluation. Recipient identity and allocation are left for the authorized procedure; suggested placeholder: `RECIPIENT-JSP000226-UPPER-A`.

Please review the precise proposition, its relationship to the catalog, prior art, mathematical/formalization attribution, and eligibility. Passing local checks or creating a PR is not an award. No payment details, private contacts, or identity documents are included.

Our original source and documentation are provided under [Apache 2.0](LICENSE). The cited paper is not redistributed and retains its authors' rights.
