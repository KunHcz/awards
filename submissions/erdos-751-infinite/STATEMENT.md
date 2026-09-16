# Statement correspondence and proof

## Mathematical result

For any simple undirected graph `G` on any vertex type, if `G` cannot be properly colored with three colors, there exist two simple cycles whose lengths differ by 1 or 2.

Equivalently, if the finite-or-infinite chromatic number is at least 4, there are natural numbers `m < n <= m+2` which are both cycle lengths of `G`. No finite, countable, locally finite, connected or positive-girth assumption is added to this conclusion.

## Definitions

`G.Colorable 3` is mathlib's usual proper 3-colorability: a graph homomorphism to the complete graph on `Fin 3`. `G.chromaticNumber` is mathlib's extended natural number chromatic number; it is infinity if no finite coloring exists. The theorem uses this directly and also has an equivalent no-3-coloring formulation, so no finite-coloring premise is hidden in the statement.

`CycleLength G n` means that some closed walk in `G` is a **simple cycle** and has length `n`. It is not an arbitrary closed walk, which could repeatedly traverse an edge and create spurious lengths. The finite theorem's `BV.Cycle` wrapper includes exactly a base vertex, a closed walk, its `IsCycle` proof and a length-at-least-three proof. Our wrapper-independent final conclusion uses the standard mathlib walk and `IsCycle` predicate.

## Proof

1. By the finite homomorphism compactness theorem, if every finite subgraph of `G` is 3-colorable then `G` is 3-colorable. The codomain is the fixed finite complete graph on three vertices. Taking the contrapositive, a graph which is not 3-colorable has a finite subgraph `H` which is not 3-colorable.
2. The finite subgraph `H` has chromatic number at least 4. Apply the separately attributed existing finite theorem `Erdos751.Main.erdos_751_strong` to obtain simple cycles of lengths differing by 1 or 2.
3. The inclusion `H -> G` is an injective graph homomorphism. Map each cycle's walk along it. Injectivity preserves the `IsCycle` condition, and mapping a walk preserves its length.
4. Order the two distinct lengths to obtain `m < n <= m+2` in `G`.

All these steps are Lean theorems in this submission, using already proved imports rather than additional axioms.

## Both original questions

The first question asks whether graphs of chromatic number 4 can have all different cycle lengths separated by an arbitrarily large prescribed gap `k`. Our `answer` negates this full universally quantified assertion by taking `k=3`.

The second question imposes an additional arbitrarily large lower bound on girth. Our `answer_with_girth` negates that assertion as well: the impossible separation already fails, independently of the girth constraint. The girth condition is expressed without a special convention for acyclic graphs as `g <= m` for every cycle length `m`. This has the same meaning as a girth lower bound and cannot weaken the separation contradiction.

The reference statement repository is:
https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/751.lean

Its `erdos_751.parts.i` and `.parts.ii` quantify over unrestricted vertex types. Its `.variants.finite` records only the finite result and explicitly identifies the missing finite-to-infinite step. Our extension addresses that gap. We do not claim the general minimum-degree-three theorem stated separately in that file.

## Eight new declarations

The extension proves `colorable_of_finite_subgraphs`, `finite_noncolorable_witness`, `lift_cycle`, `close_cycles_of_not_three_colorable`, `close_cycle_lengths`, `not_three_separated`, `answer`, and `answer_with_girth`.

The axiom audit separately prints the imported `Erdos751.Main.erdos_751_strong`. It is not counted as a ninth new theorem and its finite-graph proof is not claimed as our contribution.

## Scope of verification

The proof's target file contains no placeholder or user-added assumption. The accompanying verification report distinguishes the newly checked declarations, the imported finite result, source rebuilds, complete target-dependency replay, invalid-proof tests, and the lack of independent human or prize review. The trusted implementation remains the pinned official Lean kernel and its runtime; a replay is not an independently implemented verifier.
