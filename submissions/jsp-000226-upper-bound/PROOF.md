# An explicit counterexample to a terminal-exponent bound

## Proposition

There are 185 distinct positive integers, in increasing order,

\[
3=a_1<a_2<\cdots<a_{185}=392,
\]

such that

\[
\frac{2}{2^2}=\sum_{i=1}^{185}\frac{a_i}{2^{a_i}},
\qquad 392>2(2+185)=374.
\]

Consequently, the universal upper bound in Conjecture 3.7 of Tengely, Ulas and
Zygadło, *On a Diophantine equation of Erdős and Graham*, arXiv:2008.01501v1,
printed page 11, is false. The paper is published in Journal of Number Theory
217 (2020), 445–459, DOI 10.1016/j.jnt.2020.05.006; our exact statement reference
is the arXiv v1 PDF, not an uninspected later variant.

## Complete witness

The following is the list of exponents, not numerically approximated fractions:

```text
3 6 9 10 12 14 18 19 21 22 24 26 29 30 33
34 35 36 39 42 43 45 47 48 49 50 52 53 58 59
61 65 66 68 69 71 75 80 81 82 83 84 85 87 92
93 95 96 97 100 101 107 108 109 112 116 120 121 124 126
127 128 129 132 135 138 140 141 142 147 148 150 151 152 154
155 157 158 160 163 164 167 172 173 175 177 179 181 182 183
184 185 187 189 194 197 200 201 203 204 206 207 209 211 213
217 221 222 224 226 229 234 235 243 248 249 251 253 254 259
260 261 262 263 264 269 272 274 275 276 277 278 279 281 283
288 289 290 291 295 298 302 303 306 308 309 314 315 316 317
319 320 321 324 326 332 333 334 335 337 338 343 344 345 347
348 349 352 356 360 363 364 365 366 368 369 370 371 373 377
379 381 387 390 392
```

## Exact proof

The list is strictly increasing, has 185 entries, starts at 3, and ends at 392.
The integer identity

\[
\sum_{a\in A}a\,2^{392-a}=2^{391}
\]

is certified by direct exact integer arithmetic. Both sides equal

```text
5043456793138493339171717132818382567050206626619577173497381555743452386751642958261026080625269202023248382759272448
```

Divide by the positive integer \(2^{392}\). This gives the required sum \(1/2=2/2^2\).
The largest exponent is 392, whereas \(2(n+k)=2(2+185)=374\), a violation by 18.

This argument does not depend on the discovery algorithm. For example, with
Python's standard library and the adjacent `witness.json` file:

```python
import json
from fractions import Fraction

A = json.load(open('witness.json', encoding='utf-8'))['terms']
assert len(A) == 185 and all(0 < a < b for a, b in zip(A, A[1:]))
assert A[0] == 3 and A[-1] == 392
assert sum(a * 2**(392-a) for a in A) == 2**391
assert sum(Fraction(a, 2**a) for a in A) == Fraction(2, 2**2)
assert A[-1] > 2 * (2 + len(A))
```

The Lean proof additionally checks the full negation of the universally
quantified bound, not only these assertions. `scaled_integer_identity` and
`rational_identity` are separately kernel-checked exact calculations.
`strictly_increasing`, `positive`, `length_eq`, and `last_eq` check the
side conditions. `conjecture_false` instantiates every hypothesis at this witness
and derives the contradiction `392 <= 374`.

## Statement correspondence and exclusions

A tuple of strictly increasing exponents is represented by a finite Lean list.
The tuple length is the list length; `List.Pairwise (<)` expresses strict
increase. Because the last entry is also the largest entry, bounding every list
entry is equivalent to bounding the terminal exponent. `weightedSum` is a sum
in the exact rational field, not a floating-point approximation.

The source conjecture quantifies over all solutions; it does not say that a
solution must be greedy or use the fewest possible terms. This distinction is
essential: the same left side already has the greedy representation with
exponents `{3,6,8}`. Our counterexample does **not** refute a greedy-only or
minimum-term reformulation.

Nor does it refute the lower bound `n+k <= a_k`, the weaker exponential bound
stated after it, or prove that every positive integer has a decomposition.
The infinite-series questions of Erdős 261 remain outside the claim.

## Discovery method

The original search works backwards from the last exponent `a`, keeping an
integer tail numerator `r` on denominator `2^a`. A previous exponent `b=a-d`
can be added only when `2^d` divides `r`; the new numerator becomes
`b + r/2^d`. A path terminates at left-hand exponent `n=b` when `r/2^d=b`.
The dynamic program minimizes `n+k` among its stored paths and checks whether
the terminal exponent exceeds twice that value.

The supplied bounded C++ program found the displayed list with `n=1`.
Since `1/2^1=2/2^2`, the list also gives the `n=2` witness checked directly in
Lean. The latter also meets the stronger side condition `a_1=n+1`.
The search is a discovery tool only: no optimality, smallest counterexample,
or correctness theorem about the dynamic program is claimed.

## Attribution and priority

The 2020 authors receive credit for the equation's investigation and this
conjecture. The displayed witness and its formal proof were independently
produced in this research session with ChatGPT assistance. The original paper’s Corollary 3.6 supplies blocks that can be combined into a
longer 191-term counterexample with the same maximum. We reconstructed and checked
that fact after finding the shorter list above; see [PRIOR_ART.md](PRIOR_ART.md).
No priority for the underlying ingredients is claimed. We have not located an
earlier separately published refutation, but that does not establish worldwide priority. Human statement review, prior-art review and prize
eligibility remain to be determined.

Primary source: https://arxiv.org/pdf/2008.01501v1 .
Related problem: https://www.erdosproblems.com/261 .
