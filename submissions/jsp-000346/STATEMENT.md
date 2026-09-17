# Statement correspondence and verification boundaries

## Original question

[JSP-000346](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000346) asks for an increasing density-one sequence with distinct products over different nonempty consecutive blocks. The [reference Erdős 421 statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/421.lean) supplies the interval predicate.

This package proves necessary omission bounds, **not the existence statement**. The final results assume only `StrictMono d` and `DistinctBlockProducts d`. They assume no density, prime-distribution estimate, omission bound or unproved external mathematical result.

`DistinctBlockProducts d` is injectivity of `(u,v) -> product_{i in [u,v]} d(i)` on pairs satisfying `u<=v`. Endpoints are included and blocks are nonempty. `missing B N` is the actual interval `[1,N]` filtered by nonmembership; zero is not counted. The source definition retains attribution in NOTICE.

## Three arguments in one package

| Part | Declarations | Exact scope |
| --- | --- | --- |
| Initial 17 theorems | `consecutive_indices` through `product_distinct_half_root` | Local ambient adjacent-product obstruction; coefficient `1/2` with fourth-root error. |
| Retained-successor extension, 14 theorems | `retained_product_not_mem` through `product_distinct_full_root_eventually` | Original full block condition; coefficient `1`, fourth-root error, and an explicit eventual theorem for every positive epsilon. |
| Minimal-crossing extension, 23 theorems | `blockProduct_zero` through `omission_example_one_trillion` | Original full block condition; logarithmic error and the sharper factorial-parameter bound, including two exact numerical corollaries. |

The 54 theorem declarations are proof components, not 54 independently solved problems.

## Minimal-crossing theorem map

`blockProduct_interval` equates the finite prefix product with the original closed index interval. `retained_term_two_le` derives exclusion of zero and one from the original hypothesis. `retained_term_index_lower`, `blockProduct_factorial_lower` and `blockProduct_power_lower` supply proved lower bounds for every start.

`crossing_exists`, `crossing_spec`, `crossing_min` and `crossing_le` define and control the **first** prefix product exceeding a cutoff. `crossing_two_le` rules out a singleton. `crossingDomain_room` guarantees enough retained factors remain below the cutoff, after excluding at most `L-1` terminal starts.

`crossing_product_missing` uses the original interval injectivity, not a weaker local hypothesis. `crossing_product_upper` bounds the first crossing by `M^2`. `crossingHole_injective` handles missing/missing, retained/retained and mixed pairs. `block_crossing_omission` injects the actual finite domain into omissions at the original cutoff `N`.

The two principal specializations are:

```text
product_distinct_factorial_error:
  floor(sqrt N) < (L+1)! -> floor(sqrt N) <= E(N) + (L-1)

product_distinct_logarithmic_error:
  floor(sqrt N) <= E(N) + Nat.log 2 (floor(sqrt N))
```

`L-1` is natural subtraction. Both theorems include `N=0`; `Nat.log 2 0=0`. The factorial condition may hold with `L=0` only when the square-root cutoff is zero, so no positive-domain crossing is asserted in that case. The explicit examples are kernel-checked consequences, not substituted test data.

## Why hypothesis distinctions matter

`AvoidsAdjacentProduct` concerns ambient consecutive integers. The full property instead concerns consecutive retained values, even across gaps. `{2,4,8}` satisfies the former but violates the latter. The earlier negative control asking for coefficient one under only the weaker local condition remains applicable.

The new proof needs minimality and terminal-start removal. Multiplying past the first crossing can leave `[1,N]`; allowing a terminal start can require a factor above `M`. Two additional proof mutations exercise these failures. The full suite also rejects false arithmetic, proof placeholders and custom axioms. A failed mutation establishes rejection of that proof, not impossibility of every potentially stronger mathematical statement.

## Tests and review limits

Independent Python checks examine every subset of `{2,...,12}` satisfying the finite original block condition, greedy finite prefixes and exact crossing images. All numerical arithmetic is integral. These finite diagnostics do not establish the universal theorem; Lean does.

A fresh replay uses the same Lean kernel implementation, not an independent human or independently implemented checker. The package neither establishes global priority nor proves optimality, attainability or the density-one existence construction. Official record flags and million-dollar work are untouched.
