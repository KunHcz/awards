# Mathematical argument

This is an exposition of the known construction credited to Clemen, Dumitrescu and Liu (2025), Observation 5.1. The Lean implementation proves each step over the real numbers, without numerical approximations.

Fix m >= 3 and let n=m+1. Put theta=pi/(3(m+1)). Take the origin O and the m unit-circle points

```text
P_j = (cos(j theta), sin(j theta)),  j=0,...,m-1.
```

## Distances and multiplicities

Every distance from O to an arc point is 1. For two arc points with index difference d, the squared Euclidean distance is

```text
2 - 2 cos(d theta),  1 <= d <= m-1.
```

Since 0<d theta<pi/3, this squared distance lies strictly between 0 and 1. Since cosine is strictly decreasing on [0,pi], these m-1 chord lengths are pairwise different. They are also all different from the radial distance 1. There are therefore exactly m=n-1 distances.

The radial distance has multiplicity m. A chord with difference d occurs in exactly the pairs (P_0,P_d),...,(P_(m-1-d),P_(m-1)), giving multiplicity m-d. This accounts for every pair and yields precisely m,m-1,...,1. Their sum is m(m+1)/2, as required by the total number of unordered pairs.

The implementation proves the counts by explicit bijections of finite types. It also proves the two-to-one relation between oriented pairs of actual points and unordered pairs, so the reference statement's off-diagonal count divided by two is recovered exactly.

## The points are not collinear

The origin and P_0=(1,0) lie on the horizontal axis. But P_1 has positive second coordinate because 0<theta<pi. Hence no line can contain all the points. In Lean this is proved from the standard collinearity characterization by scalar multiples of a common direction, not from a custom predicate.

## The points are not cocircular

Suppose all the points lie on a circle with centre C=(a,b) and radius R. Comparing its squared-distance equation at the origin with that at P_j gives

```text
a cos(j theta) + b sin(j theta) = 1/2.
```

For j=0, this says a=1/2. For j=1, multiply the equation by 2 cos(theta), then use the double-angle identities in the equation for j=2. The resulting equations imply cos(theta)=1, contradicting 0<theta<pi. The required points j=0,1,2 exist because m>=3.

This excludes every circle centre and radius, not just the unit circle used to place the arc points.

## Full quantifiers

Given any n>=4, take m=n-1. Injectivity gives exactly n points, and the conclusions above give their exact profile and both geometric exclusions. Given any proposed eventual threshold N, choosing n=max(N,4) produces a counterexample beyond that threshold. Equidistant line and equidistant circle sets are in particular collinear or cocircular, so the proposed eventual classification is false.

Reference: <https://arxiv.org/html/2505.04283v1#S5>.
