# Erdős 751: the arbitrary-graph extension

This contribution extends the existing finite-graph Lean proof of Erdős 751 to **arbitrary vertex types**, including infinite and uncountable graphs. If a graph is not 3-colorable, it has two simple cycles whose lengths differ by one or two. Consequently, the proposed arbitrarily large separation between cycle lengths is impossible, with or without a lower bound on girth.

**This is known mathematics, not a new mathematical discovery.** Our contribution is the previously unfilled finite-to-infinite formalization step and its verification package. The finite theorem belongs to **SpringSense Innovation Institute** and is explicitly attributed throughout.

We have not established an exact matching JSP catalog identifier. Please treat this as a **problem recommendation and scoped formal-evidence submission**, not as an accepted claim on a numbered bounty. In particular, `JSP-000751` is a different problem and is not used here.

## Proof and scope

- [Erdos751Extension.lean](Erdos751Extension.lean): eight new declarations and a separately identified audit of the imported finite theorem.
- [STATEMENT.md](STATEMENT.md): definitions, quantifiers, proof argument, and correspondence to both original questions.
- [PRIOR_ART.md](PRIOR_ART.md): the finite proof, compactness theorem, missing-step evidence, and licensing limitations.
- [evidence/verification.json](evidence/verification.json): actual local validation results and fixed source hashes.

The extension does not claim the more general finite theorem assuming only minimum degree three. Instead, it uses the existing four-chromatic finite-graph theorem. No theorem, lemma or mathematical oracle is postulated.

## Reproduction

Use Python 3.9+ and Lean 4.23.0 as pinned by `lean-toolchain`. The older version is intentional: it permits the existing finite proof to be used **byte-for-byte unchanged**.

```sh
python3 scripts/fetch_upstream.py
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Finsubgraph Mathlib.Combinatorics.SimpleGraph.Coloring Mathlib.Combinatorics.SimpleGraph.Paths Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph Mathlib.Combinatorics.SimpleGraph.Ends.Defs Mathlib.Combinatorics.SimpleGraph.Trails Mathlib.Combinatorics.SimpleGraph.Girth Mathlib.Tactic
python3 scripts/verify.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
```

The verifier checks every Git dependency pin and all nine fetched source/configuration hashes. It removes generated build outputs for our extension and the fetched finite-proof package, then rebuilds both from source with warnings as errors. It audits the eight new theorems and the imported final theorem, checks five deliberately invalid proofs, and replays the complete transitive logical dependencies of all nine audited targets with Lean's own kernel.

### Replay driver

The Lean 4.23 binary distribution used here does not bundle `leanchecker`. Its official `Lean.Environment.replay` implementation also attempts to register the built-in quotient declaration group repeatedly when replaying all quotient records, causing a duplicate-name panic in our initial experiment. The failed experiment is not a successful verification.

[scripts/Replay.lean](scripts/Replay.lean) adapts the dependency traversal in the official Lean 4.23.0 replay implementation. It uses `Kernel.Environment` directly to avoid elaborator private-name metadata collisions, and initializes the canonical built-in quotient group exactly once through `Quot.lift`. Every replayed declaration is passed to the official `Kernel.Environment.addDeclCore` with kernel checking enabled; generated constructors and recursors are compared with their original records. All nine target theorems and their complete transitive logical dependencies are replayed, while unrelated imported declarations are outside this targeted replay. Two additional controls check that the same kernel accepts `True.intro : True` and rejects `True.intro : False`. The verifier rejects a panic, missing completion marker or control, timeout or nonzero exit. The driver is not imported by the mathematical proof. It is an adapted replay driver, not an unmodified bundled checker.

This remains the **same Lean kernel implementation**, not an independently implemented checker or independent human review. Mathlib uses pinned upstream compiled caches; the finite proof and extension are rebuilt from source, and their complete target dependency closures are replayed. A full replay of all imported declarations, including unrelated material, exceeded the experiment budget and is not claimed.

## Attribution, rights and review

The finite proof is fetched from the pinned public source identified in [upstream-hashes.json](upstream-hashes.json). No explicit redistribution license was located for that snapshot. Therefore its source files are **not redistributed or relicensed in this submission**; `.upstream/` is ignored by Git. Reviewers fetch those public files directly for local verification. Permanent redistribution or archival of the third-party files may require the authors' permission. Our own source and documentation are [Apache-2.0](LICENSE).

The extension and verification were developed with ChatGPT assistance for submitter `KunHcz`. This is a self-submission with a direct interest in review. Suggested recipient placeholder: `RECIPIENT-ERDOS751-EXTENSION-A`. No identity, allocation, award tier, eligibility or acceptance is asserted.

Please review the mathematical statement, the precise additional contribution, attribution, catalog inclusion and eligibility. No existing catalog, recipient, candidate or award record is altered. Submission and local verification are not official prize approval.
