# Exact density: definitions, quantifiers, and proof

## Relation to the original question

Erdős Problem 859 defines `d_t` as the density of integers whose distinct divisors have a subset
summing to `t`, and asks whether `d_t` is asymptotic to `c1/(log t)^c2`. The website credits Erdős
[Er70] with existence of the density and logarithmic upper/lower estimates. We formalize the
existence and positivity component with an exact rational formula, not the estimates or the open
asymptotic equivalence. The reference Lean file leaves its `positive_density` variant unproved.

## Literal property and finite predicate

`DivisorSum t n` means that a finite subset of `Nat.divisors n` sums to `t`.
There is no reuse of a divisor: the witness is a `Finset`. Positive summands in a sum equal to `t`
are all at most `t`. Thus, for positive `n`, the property is equivalent to `Good t n`, which checks
only subsets of `{1,...,t}` and verifies divisibility of each member. Both directions are proved.

The theorem counts positive integers `1,...,N`. Standard natural density using `[0,N)` is the same:
the two counting windows differ by at most one element at each endpoint, so their normalized
count difference tends to zero. The proof makes no claim that `Nat.divisors 0` contains all natural
divisors; zero is avoided by counting `Good t (j+1)` for `j<N`.

The proof also covers `t=0` consistently: the empty subset represents zero for every positive
integer, giving density one. The original `t>=1` statement is an immediate restriction.

## Finite formula and quantitative proof

Put `L=t!` and `C=# {j in [0,L) : Good t (j+1)}`. All integers from 1 through t divide L,
so `Good t (n+L)` is equivalent to `Good t n`. Factorial is a convenient valid period, not a claim
about the smallest period or an efficient implementation for large t.

For any predicate p with period L and `N=qL+r`, the proof establishes exactly

`count_p(N)=q*count_p(L)+count_p(r)`.

Since `0<=count_p(r)<=r<L` and `0<=C/L<=1`, it follows that

`|count_p(N)-N*C/L|<=L`.

Dividing by positive N and squeezing against `L/N -> 0` proves that the counting ratio converges
to `C/L`. The factorial L itself is representable (use `{t}` for positive t), so `C>=1` and this
rational density is strictly positive. Its upper bound is one. No analytical theorem about divisor
sums is assumed: convergence is proved from the finite identity.

The final theorem `literal_divisor_sum_density` connects the computable periodic count to the
literal divisor-subset predicate on `[1,N]`. Its conclusion explicitly quantifies over a positive
rational limit. The finite count and real casts prevent natural-number truncating division from
being mistaken for density.

## Verification

All target and auxiliary theorems have explicit axiom reports. Uniform periodicity, the
quotient/remainder count, absolute error and real limit are proved with unbounded quantifiers.
Exact Python enumeration cross-checks small targets and overlapping ways to make the same target;
these experiments do not establish the general theorem. Negative controls alter the period and
density denominator, in addition to standard false-proof controls.
