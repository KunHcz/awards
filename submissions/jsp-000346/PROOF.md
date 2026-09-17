# Minimal block crossings and an inverse-factorial omission bound

Let `d(0)<d(1)<...` be a sequence of natural numbers. Assume that products over distinct nonempty consecutive index intervals are distinct. Put `B=range(d)` and `E(N)=|[1,N] \ B|`. Counts exclude zero. No density hypothesis is used.

## 1. Elementary consequences of the original hypothesis

Every retained value is at least 2. If `d(i)=0`, the block `[i,i+1]` and the singleton `[i,i]` have equal products. If `d(i)=1`, the block `[i,i+1]` and the singleton `[i+1,i+1]` have equal products. Either contradicts the hypothesis.

Strict increase therefore gives `d(i)>=i+2`. For the product of `l` terms starting at `i`, write

\[
 P(i,l)=\prod_{j=0}^{l-1}d(i+j),\qquad P(i,0)=1.
\]

Termwise bounds give

\[
 P(i,l)\ge 2^l,\qquad P(i,l)\ge\prod_{j=0}^{l-1}(j+2)=(l+1)!.
\]

If `l>=2`, the product `P(i,l)` is not a retained value: equality with `d(k)` would identify the nonempty interval `[i,i+l-1]` with the singleton `[k,k]`. Distinct such intervals also have distinct products.

## 2. The first product to cross a cutoff

Fix `M>=1`. For each start `i`, define `ell(i)` to be the least nonnegative length with `P(i,ell(i))>M`. Such a length exists by `P(i,l)>=2^l`.

If `d(i)<=M`, then `ell(i)>=2`, because the empty product and the one-term product are both at most `M`. Minimality gives

\[
 P(i,\ell(i)-1)\le M.
\]

Suppose all factors through the crossing are at most `M`. The last factor then shows

\[
 M<P(i,\ell(i))\le M^2.
\]

This upper bound is why the crossing must be minimal. Taking an arbitrary later block does not work: with initial terms `2,3,5` and `M=5`, the first crossing is `6<=25`, whereas extending the block gives `30>25`.

## 3. Remove only the terminal starts lacking enough factors

Fix natural numbers `N,M,L` with `M^2<=N`. Suppose `P(i,L)>M` for every start `i`.

There are finitely many retained values at most `M`. Let their indices be `0,...,t-1`, where `t` is the first index with `d(t)>M`. Such an index exists because `d(i)>=i`.

From all positive integers `[1,M]`, remove the last at most `L-1` retained values. Call the resulting domain `D`. Thus

\[
 |D|\ge M-\max(L-1,0).
\]

For any retained input `d(i)` in `D`, one has `i+L<=t`. Therefore at least `L` consecutive retained factors from that start remain at most `M`. Since `P(i,L)>M`, the first crossing occurs within those factors and its product is at most `M^2`.

The Lean definition removes the image of `j -> d(t-1-j)` for `0<=j<L-1`, with natural subtraction. If there are fewer than `L-1` retained values, repetitions of index zero do not increase the number removed. If there are none, the repeated value is above `M`. These cases preserve both the cardinal bound and the retained-start argument. If `M=0`, the domain is empty and the final count is immediate.

## 4. Inject the entire domain into the actual omitted integers

For `x in D`, define

\[
 h(x)=\begin{cases}
 x,&x\notin B,\\
 P(i,\ell(i)),&x=d(i)\in B.
 \end{cases}
\]

A missing input maps to an omitted positive integer at most `M`. A retained input maps to a product in `(M,M^2]`, hence in `[1,N]`. That product is omitted by Section 1.

The map is injective. Missing inputs map to themselves. Products from distinct retained starts correspond to different nonempty intervals and are distinct by the original hypothesis. A missing image is at most `M`, while a retained image exceeds `M`, so the two kinds cannot collide.

Consequently

\[
 \boxed{M\le E(N)+\max(L-1,0).}
\]

This is a finite inequality at every cutoff; it is not an assertion only along a subsequence.

## 5. Factorial and logarithmic specializations

Take `M=floor(sqrt(N))`. The condition `M<(L+1)!` guarantees `P(i,L)>M` for every `i`, yielding

\[
 \boxed{M<(L+1)!\ \Longrightarrow\ M\le E(N)+\max(L-1,0).}
\]

Alternatively set `L=floor(log_2 M)+1`. Then `2^L>M` and the power lower bound gives

\[
 \boxed{M\le E(N)+\lfloor\log_2 M\rfloor.}
\]

Here the natural-number logarithm at zero is zero. The exact factorial choice is usually sharper. For example, when `N=100000000`, use `M=10000` and `L=7`, since `8!=40320>10000`. This proves `E(N)>=9994`. For `N=1000000000000`, take `L=9`, because `10!=3628800>1000000`; the result is `E(N)>=999992`. Both examples are separate Lean corollaries of the universal theorem.

## 6. Earlier results retained in the package

An earlier retained-successor injection used only two-term products, separated above `M` by discarding all inputs at most `sqrt(M)` and one terminal value. It proves

\[
 \lfloor\sqrt N\rfloor\le E(N)+\lfloor\sqrt{\lfloor\sqrt N\rfloor}\rfloor+1,
 \qquad E(N)\ge\sqrt N-N^{1/4}-2,
\]

and, for every `epsilon>0`, eventually `E(N)>=(1-epsilon)sqrt(N)`. The new block-crossing theorem improves the finite error. The independently checked older eventual theorem is retained rather than adding an unnecessary real-log limit proof.

The initial disjoint-triple argument used the strictly weaker local condition `a,a+1 in B` implies `a(a+1) notin B`, for `a>=2`. It proves only a half-root bound with a fourth-root error. That result remains useful for sets not satisfying the original full interval hypothesis. Its coefficient-one mutation must still be rejected.

## Attribution and limits

The comparison source is the pinned Pratt Proposition 7.1: unconditional coefficient `1/3`, and coefficient `1` with density one. The successive injection arguments were developed in this work. They strengthen that specified comparison but do not refute Pratt's valid weaker statements.

Worldwide priority is not established. No construction attaining these bounds, optimality result, or new proof of the density-one existence theorem is claimed. Computational tests are diagnostics; the quantified results are proved in Lean without placeholder proofs or nonstandard axioms.
