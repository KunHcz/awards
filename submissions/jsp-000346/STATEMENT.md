# Statement correspondence

## Original problem and claimed component

The official [JSP-000346 catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000346) asks for a strictly increasing density-one sequence whose products over different nonempty consecutive blocks are distinct. The corresponding reference statement is [Erdős 421](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/421.lean).

This package proves a necessary quantitative restriction on **every** such sequence, and more generally on every set satisfying the adjacent-product obstruction. It does not prove the density-one existence statement. It requests review as a scoped quantitative contribution, without changing the catalog's solution or eligibility flags.

## Definitions and hypotheses

`DistinctBlockProducts d` is injectivity of the interval-product function on pairs `(u,v)` with `u <= v`. Thus intervals are nonempty, include both endpoints, and are distinguished by both their starting and ending indices. A singleton block and a two-element block are different. The predicate is adapted from the pinned reference statement, with its attribution retained in NOTICE.

`block_products_avoid_adjacent` uses strict monotonicity to show that values `a` and `a+1` must have consecutive indices. It then compares their two-term product with the singleton containing `a(a+1)`. The local obstruction is derived, not assumed about the original sequence.

`missing B N` is the filter of the actual natural-number interval `[1,N]` by nonmembership in `B`. It never counts zero. `omittedCount` is its cardinality. Finite natural subtraction and integer square roots are handled before the conversion to real inequalities.

No `HasDensity` hypothesis, analytic conjecture, prime distribution estimate, geometric counting theorem, or external proof package is assumed. The final results do not need the reference statement's extra positive-first-term hypothesis; they therefore apply to its sequences in particular. Neither `False` nor the desired omission bound appears as an assumption.

## Proof map

| Theorems | Role |
| --- | --- |
| `consecutive_indices`, `block_products_avoid_adjacent` | Connect the literal consecutive-block condition to the local obstruction. |
| `index_bounds`, `pairProduct_strictMono` | Place all selected triples within the cutoff and separate the small endpoints from all products. |
| `hole_cases`, `hole_not_mem`, `hole_mem_missing`, `holes_injective` | Choose real omissions and prove that no two selected triples use the same omission. |
| `indices_card`, `omission_bound_nat`, `omission_bound_integral` | Exact finite counting, including empty intervals and small cutoffs. |
| `nat_sqrt_le_real`, `real_sqrt_lt_nat_succ`, `omission_bound_real` | Convert the integer bound to the explicit real fourth-root-error inequality. |
| `omission_bound_eventually` | For every positive error tolerance, prove the bound at all sufficiently large cutoffs. |
| `product_distinct_omission_bound`, `product_distinct_half_root` | Final statements under the original sequence condition. |

The complete declaration inventory and axiom reports are included in the verification configuration and evidence. These 17 declarations form one contribution, not 17 separate problems.

## Checks and boundaries

The semantic mutations collapse different hole choices, remove the scale-separation cutoff, and demand an unsupported coefficient-one bound. Each must fail. Exact bounded hitting-set tests independently check the local counting problem; finite prime and rapidly increasing power sequences exercise the block definition, while `{2,4,8}` shows that the local condition is genuinely weaker than full product-distinctness.

The coefficient-one counterexample in the Python tests is a **finite local-obstruction set**, not a product-distinct sequence and not a counterexample to Pratt's density-one bound. No optimality assertion follows from that test. The tests are diagnostic; the universal theorems are Lean proofs.
