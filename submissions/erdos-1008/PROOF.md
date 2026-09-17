# Complete proof

Let the left and right vertex sets have sizes `s` and `t`. A graph is a simple undirected graph. A four-cycle means an injective, not necessarily induced, copy of the ordinary cycle on four vertices. Each edge is counted once.

## 1. Four-cycles and shared pairs

Write `F(b)` for the set of left neighbors of right vertex `b`. The graph is four-cycle-free exactly when a two-element left subset belongs to at most one `F(b)`.

If distinct right vertices `b,c` share distinct left vertices `a,a'`, the sequence `a,b,a',c` gives a four-cycle. Conversely, every four-cycle in a bipartite graph alternates between the two parts and gives such a repeated pair. The implementation proves both directions by constructing or analyzing an injective copy of mathlib's `cycleGraph 4`.

## 2. The upper bound

Let `d_b=|F(b)|`. The two-element subsets of the neighborhoods are disjoint subsets of the universe of all left pairs. Consequently,

\[
 \sum_b\binom{d_b}{2}\le\binom{s}{2}.
\]

For every nonnegative integer `d`, including zero,

\[
 d\le1+\binom d2.
\]

Summing and counting each unordered edge by its unique right endpoint gives

\[
 e(H)=\sum_b d_b\le t+\sum_b\binom{d_b}{2}\le t+\binom{s}{2}.
\]

The neighborhood graph is proved equal to every subgraph of the complete bipartite host, so this is an upper bound for all such simple graphs, not just graphs represented in a restricted format.

## 3. Attainment in the stated range

Assume `s>=1` and `t>=choose(s,2)`. Choose a left vertex `a0`. Use one right vertex for each two-element left subset, adjacent precisely to its two elements. Make the other `t-choose(s,2)` right vertices leaves adjacent to `a0`.

A left pair occurs in exactly one degree-two neighborhood, and in no leaf neighborhood. The graph is therefore four-cycle-free. Its edge count is

\[
 2\binom{s}{2}+\left(t-\binom{s}{2}\right)=t+\binom{s}{2}.
\]

A finite equivalence reindexes the right vertices by `Fin t`, with all cardinalities proved. This is a witness on exactly the declared vertex type. When `s=1,t=0`, both parts of the construction are empty and the edge count is zero. The sharpness conditions are necessary for the formula as stated: `s=2,t=0` would predict one edge on an edgeless host, and `s=0,t>0` also cannot attain the displayed upper bound.

## 4. Folkman's family

Set `s=n,t=n^2`. The host has exactly `n^3` edges. Since `choose(n,2)<=n^2`, the construction applies for every `n>=1`, and its maximum four-cycle-free subgraph size is exactly

\[
 n^2+\binom n2.
\]

The original Folkman statement follows as well: every subgraph with more than this many edges contains a four-cycle. That implication and the host count also cover `n=0`.

## 5. Refuting the uniform three-quarters guarantee

Suppose there were `c>0` such that every finite graph with `m` edges had a four-cycle-free subgraph with at least `c*m^(3/4)` edges. Choose a natural `k>max(1,2/c)` and use the host with `n=k^4` above.

Its edge count is `k^12`, so the proposed guarantee is `c*k^9`. However, the upper bound gives at most

\[
 n^2+\binom n2\le2k^8<c k^9,
\]

because `c*k>2` and `k>0`. This is a contradiction. The identity `(k^12)^(3/4)=k^9` is proved over the actual real-power operation. The contradiction quantifies over every positive `c`, every finite vertex type and every simple host graph; it is not a test of a single constant.

## 6. Numerical instance

For `s=10,t=100`, there are 45 left pairs and 55 extra leaves. The constructed graph has `2*45+55=145` edges. The universal upper theorem excludes 146 edges in any four-cycle-free subgraph of that same 1,000-edge host. Both facts are explicitly instantiated in Lean.

## What is not claimed

The modern positive `m^(2/3)` guarantee is not proved anew here. The result does not give exact maxima in every rectangular parameter range, nor an exact inverse-Turán function for arbitrary hosts. The counting argument and Folkman obstruction are known mathematics. Global formalization priority and reward eligibility are not established by these proofs.
