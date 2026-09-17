# A disjoint-obstruction proof

Let `B` be a set of positive integers, and let `E(N)` be the number of integers in `[1,N]` outside `B`. Assume that different nonempty consecutive blocks in the increasing enumeration of `B` have different products. The argument below also applies to finite sets whenever the same block condition is defined.

## The local obstruction

If `a >= 2` and both `a` and `a+1` belong to `B`, they are consecutive in its increasing order. Their two-term block has product `a(a+1)`. Therefore `a(a+1)` cannot itself belong to `B`: its singleton block would have the same product as a different block. This is the obstruction used in Pratt's Proposition 7.1.

We now assume only this local obstruction. No asymptotic density or prime-distribution result is needed.

## Disjoint triples

Fix a natural cutoff `N`, and put

\[
 r=\lfloor\sqrt N\rfloor,\qquad s=\lfloor\sqrt r\rfloor.
\]

For every integer

\[
 \lfloor s/2\rfloor+1\le k\le\lfloor(r-1)/2\rfloor,
\]

consider

\[
 T_k=\{2k,\ 2k+1,\ (2k)(2k+1)\}.
\]

The two small elements lie in `[1,r]`. Since `2k > s` and `(s+1)^2 > r`, the product is strictly larger than `r`. It is at most `r^2`, hence at most `N`.

The triples are pairwise disjoint. Different even-odd pairs are disjoint. The products strictly increase with `k`. A product cannot equal any small element because it lies beyond `r`.

The local obstruction forces at least one missing element from each triple. Pairwise disjointness ensures these omissions are all different. Consequently,

\[
 E(N)\ge
 \max\left(0,\left\lfloor\frac{r-1}{2}\right\rfloor-
                 \left\lfloor\frac{s}{2}\right\rfloor\right).
\]

For `r=0`, the Lean expression uses natural subtraction before division; it still equals zero. All other empty-interval cases are also included.

Let `m` denote the displayed integer bound and `p = floor((r-1)/2)`. The floor inequalities give

\[
 r\le2p+2\le2m+2\lfloor s/2\rfloor+2\le2m+s+2.
\]

Thus, at every cutoff,

\[
 r\le2E(N)+s+2.
\]

## Real and asymptotic bounds

Since `sqrt(N) < r+1` and `s <= sqrt(sqrt(N))`,

\[
 E(N)\ge\frac{\sqrt N-\sqrt{\sqrt N}-3}{2}.
\]

For a given `epsilon > 0`, choose a natural `M > max(2,4/epsilon)`. At every `N >= M^4`, the error `sqrt(sqrt(N))/2 + 3/2` is at most `epsilon sqrt(N)`. This proves

\[
 E(N)\ge(1/2-\epsilon)\sqrt N
\]

at all sufficiently large cutoffs, not merely along a subsequence.

## Comparison and limitations

Pratt's Proposition 7.1 states the unconditional coefficient `1/3` and the stronger coefficient `1` for sets of density one. The disjoint-triple selection improves the former to `1/2`. It does not supersede the latter. The proof gives a necessary omission bound, not the density-one existence construction, and does not establish optimality for the full consecutive-block condition.

The argument and Lean implementation were developed with ChatGPT assistance in this submission. The local obstruction is credited to the cited source. Whether the strengthened bound has appeared elsewhere is not established.
