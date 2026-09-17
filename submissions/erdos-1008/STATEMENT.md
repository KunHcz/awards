# Statement correspondence and scope

The reference is [Erdős Problem 1008](https://www.erdosproblems.com/1008) and its [pinned formal statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1008.lean). Its modern positive `m^(2/3)` theorem and original negative `m^(3/4)` question are different statements. We address the latter and prove an exact rectangular extremum supporting Folkman's obstruction.

## Exact predicates

`incidence F` is a simple graph on `α ⊕ β`. A left vertex `a` is adjacent to right vertex `b` exactly when `a` belongs to the finite set `F b`. There are no same-part edges and no loops.

`PairUnique F` says that a two-element left set cannot be contained in the neighborhoods of two different right vertices. It is an intermediate condition, not an extra assumption on the final result. `pairUnique_of_free` and `free_of_pairUnique` prove its equivalence to `(cycleGraph 4).Free (incidence F)` by analyzing actual injective copies. The forbidden copy is not required to be induced: additional edges cannot hide a cycle.

`H.edgeSet.ncard` is mathlib's cardinality of the set of unordered edges. `incidence_edges` proves that this equals the sum of the right degrees. It is not the sum of both sides' degrees. `incidence_neighbors` reconstructs every `H <= completeBipartiteGraph α β`, so the universal result covers every permitted subgraph.

## Final theorem map

| Theorem | Exact scope |
| --- | --- |
| `rectangular_upper` | For all finite left/right types, every actual C4-free subgraph has at most `t+choose(s,2)` edges. No lower bound on `s` or `t` is needed. |
| `rectangular_attained` | For every natural `s,t` with `s>0` and `t>=choose(s,2)`, an actual graph attains the upper bound. |
| `rectangular_exact` | The attaining witness and universal upper statement together express the exact maximum, without a potentially vacuous supremum definition. |
| `complete_edges` | The complete bipartite host has exactly `s*t` unordered edges, including empty sides. |
| `folkman` | The reference `erdos_1008.variants.folkman` statement: `K(n,n^2)` has `n^3` edges, and every subgraph exceeding `n^2+choose(n,2)` contains a C4. All natural `n`, including zero. |
| `folkman_exact` | For every positive `n`, the Folkman upper bound is attained. |
| `no_uniform_three_quarters` | The full negation of the reference positive-constant/all-finite-graphs/all-subgraphs guarantee with real exponent `3/4`. |
| `three_quarters_answer` | The logical negative-answer form, with `False` in place of the reference's `answer(False)` macro. No proposition is smuggled into an answer expression. |
| `ten_by_hundred_attained`, `ten_by_hundred_upper` | Both halves of the exact numerical example, 145 edges inside a 1,000-edge complete bipartite graph. |

The remaining named theorems are the graph, counting and real-power bridges. The full inventory is recorded in `verification-config.json` and every name is audited. The 26 declarations form this single contribution, not 26 solved prize problems.

## Boundaries and nonclaims

The upper bound includes `s=0`, `t=0`, degree-zero vertices, and graphs with no edges. Attainment covers `s=1,t=0`. It requires the advertised range; deleting it would make the assertion false, for example at `s=2,t=0`.

The negative-answer proof uses an arbitrary positive real constant, not a fixed numerical constant or a bounded list of graphs. It imports no theorem from the unproved reference file. The known positive `m^(2/3)` guarantee is not re-proved or claimed as this submission's work. There is no claim of exact extremal values for all rectangular sizes, global first priority, or official award status.
