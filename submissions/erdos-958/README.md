# Erdős 958: complete counterexamples to the eventual line-or-circle classification

This package formalizes the circular-arc-plus-centre construction of **Felix Christian Clemen, Adrian Dumitrescu and Dingyuan Liu (2025), Observation 5.1**. It is known mathematics, not a new mathematical discovery.

For **every integer n >= 4**, it constructs an actual finite set of exactly n points in the standard Euclidean plane such that:

- There are exactly n-1 distinct distances, whose unordered-pair multiplicities are exactly 1,2,...,n-1.
- The points are not all on any line and are not all on any circle.

Consequently the proposed classification for all sufficiently large n is false. This is not a certificate for just one small exceptional configuration. The proof ends with `Erdos958.original_classification_false`, the direct negation of the full eventual classification by equidistant line or circle points.

## Contents

[The complete Lean source](Erdos958.lean) contains 41 named theorems. [Statement correspondence](STATEMENT.md) explains the quantifiers and the checked connection between increasing-index pairs and the reference statement's finite-set definitions. [The mathematical proof](PROOF.md) is a self-contained explanation of the construction. [Prior art](PRIOR_ART.md) records ownership, scope, source pins and the limits of the priority search.

[Verification records](evidence/verification.json) contain the actual local results, dependency revisions, theorem axiom inventories, semantic negative controls and source digests. [The verifier](scripts/verify.py) and [its tests](scripts/test_verify.py) allow reproduction.

## Reproduce

Use Python 3.9+ and the official Lean toolchain manager. The package pins Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`; the committed manifest pins all other dependencies.

```sh
lake exe cache get Mathlib.Analysis.InnerProductSpace.PiL2 Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.Geometry.Euclidean.Sphere.Basic Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional Mathlib.Tactic
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier writes to `verification-output/` by default, preserving the included evidence. It checks all dependency pins and tracked source cleanliness, removes only this package's generated build directory, rebuilds with warnings treated as errors, audits every named theorem and replays all imported and local logical declarations into a fresh Lean kernel environment. It rejects deliberately false arithmetic, proof placeholders, added axioms, duplicated arc points, wrong multiplicities and counting ordered pairs without dividing by two.

The replay uses **the same Lean kernel implementation**, not an independently implemented checker or independent human review. Pinned mathlib compiled caches are replayed, not all rebuilt from source. Python combinatorial tests and floating-point geometry diagnostics are supplemental checks, not the proof of the universal claim. Repository record tests are not official mathematical validation or online CI.

## Intake and prize scope

This is an AI-assisted self-submission by `KunHcz`, with a direct interest in review. Proposed recipient placeholder: `RECIPIENT-ERDOS958-A`. Attribution, priority, eligibility, any allocation and independent verification remain for the maintainers to determine.

We have not confirmed a matching JSP catalog identifier. Please review this as an **Erdős 958 problem recommendation / catalog-correspondence request with complete formal evidence**, not as an already accepted numbered claim. In particular, the superficially similar JSP-000199 entry must not be conflated with this classification question or with the separate general-position crescent problem: our configurations have many cocircular arc points.

No million-dollar/Pinnacle work is included. No fixed non-Pinnacle payment is asserted. No catalog, candidate, recipient or award status is changed. Our original implementation is [Apache-2.0](LICENSE); the reference definitions retain the attribution in [NOTICE](NOTICE). The cited research paper is not redistributed.
