# Erdős 1008: sharp rectangular C4 extremum and the Folkman obstruction

For a complete bipartite graph with part sizes `s,t`, every subgraph containing no four-cycle has at most

\[
 t+\binom{s}{2}
\]

unordered edges. This package proves that the bound is attained whenever `s>=1` and `t>=choose(s,2)`. It supplies both a universal upper bound and an actual attaining graph, not just a numerical search.

For Folkman's graph `K(n,n^2)`, the exact maximum is `n^2+choose(n,2)` for every `n>=1`, while the host has `n^3` edges. The proof then fully refutes the original uniform `m^(3/4)` guarantee in Erdős 1008. The displayed example `K(10,100)` has 1,000 edges; its largest four-cycle-free subgraph has exactly 145 edges. Both sides of that example are Lean theorems.

## Contribution and limits

The mathematics is classical: the obstruction is credited to Folkman, and the pair-counting method belongs to the Kővári–Sós–Turán tradition. This is an AI-assisted Lean implementation, **not a discovery claim**. It does not replace the known Conlon–Fox–Sudakov/Hunter positive `m^(2/3)` result or the earlier formalization of that positive result. It does not solve rectangular Zarankiewicz numbers outside the stated sharpness range.

A matching JSP catalog identifier has not been established. This is a problem-correspondence/recommendation and formal-evidence submission for **Erdős 1008's original negative question and the exact rectangular variant**, not a numbered accepted claim. No catalog, recipient, eligibility or award records are changed. The submitting account has an interest in recognition of this contribution. Eligibility, role attribution, priority and any amount remain for the organizers to determine.

## Proof and evidence

- [Erdos1008.lean](Erdos1008.lean): 26 named theorems, each included in the axiom audit.
- [PROOF.md](PROOF.md): complete mathematical argument.
- [STATEMENT.md](STATEMENT.md): original-statement correspondence and edge/cycle conventions.
- [PRIOR_ART.md](PRIOR_ART.md): source ownership, earlier proof and limited search scope.
- [evidence/verification.json](evidence/verification.json): actual local verification results and pinned input hashes.

Only pinned mathlib modules are imported. `cycleGraph 4`, injective graph copies and ordinary unordered `edgeSet.ncard` are used. A proved equivalence connects those definitions to the right-neighborhood pair condition. No external solver, unproved reference theorem or native evaluation axiom is used.

## Reproduce

Run in this directory with the official Lean toolchain manager and Python 3.10 or later:

```sh
lake exe cache get Mathlib.Tactic Mathlib.Combinatorics.SimpleGraph.Bipartite Mathlib.Combinatorics.SimpleGraph.CycleGraph Mathlib.Combinatorics.SimpleGraph.Copy
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

Lean 4.34.0, mathlib `5ed2965256430c3649e86755f9576b54eca72435`, and all nine Git dependency revisions are pinned. The verifier rebuilds this package with warnings as errors, audits all 26 theorem closures, replays imported and local declarations using `leanchecker --fresh`, and runs seven erroneous-proof controls. Reproduction writes to `verification-output/` and preserves submitted evidence.

The fresh replay uses the same official Lean kernel, not an independently implemented checker or a human reviewer. Dependency caches are replayed, not all rebuilt from source. Python exhaustive small-graph and exact-integer tests supplement rather than establish the universal mathematical statements. Repository record tests do not certify the mathematics. Local success is not official review or an award.

Code is [Apache 2.0](LICENSE); see [NOTICE](NOTICE) for attribution.
