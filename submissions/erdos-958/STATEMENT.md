# Statement correspondence and completeness

## Original question

The original classification question is recorded as Erdős Problem 958 and in Clemen–Dumitrescu–Liu, *On the mutiplicities of interpoint distances*, arXiv:2505.04283v1, Introduction Question (4) and Section 5, Observation 5.1.

For sufficiently large n, does a planar n-point set with distance-multiplicity profile (n-1,n-2,...,1) have to consist of equidistant points on a line or circle? The negative answer must supply arbitrarily large counterexamples; an isolated four-point exception would be insufficient.

Primary source: <https://arxiv.org/html/2505.04283v1#S5>.

## Exact formal target

The reference statement was inspected at the fixed revision:

<https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/958.lean>

Its distance definitions are in:

<https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Geometry/Metric.lean>

Our final theorem `Erdos958.original_classification_false` uses the same natural-number thresholds, finite-set cardinality, full eventual quantification, distance-set image, and equidistant-line/circle predicates. The reference's `answer(False) ↔ P` is supplied as the logically equivalent `¬ P`. `Plane` is exactly `EuclideanSpace ℝ (Fin 2)`, not the maximum-norm metric on a product type and not an abstract distance table. The circle predicate uses `arc t = !₂[cos t, sin t]`, a transparent abbreviation for the same coordinates.

`finite_counterexamples` proves the stronger uniform statement for **every n >= 4**, with a finite point set of exactly n elements. The final classification proof chooses n=max(N,4), so it does not exploit a small-cardinality edge case or weaken “all sufficiently large n”.

## Counting bridge

The proof first indexes the centre by 0 and the m arc points by 1,...,m, with n=m+1. `points_injective` proves those n indexed points are genuinely different. `pointSet_card` independently establishes the finite image has cardinality n.

For the internal counting argument, `Pairs m` contains index pairs i<j and therefore enumerates each unordered pair once. This is exactly the convention used in the paper's introductory definition of multiplicity.

The final theorem does **not** depend on accepting an informal equivalence of conventions. It uses the reference definitions literally:

```lean
finiteDistances A = A.offDiag.image (fun p => dist p.1 p.2)
finiteMultiplicity A d = (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2
```

`orientedPair_injective`, `orientedPair_mem` and `orientedPair_surjective` provide the bijection between a Boolean orientation times an increasing-index pair and an ordered off-diagonal pair of actual points. `orientedPair_dist` proves reversal preserves the distance. `finiteMultiplicity_eq` restricts this bijection at each distance and proves the division by two gives exactly the internal unordered-pair cardinality. `finiteDistances_eq` proves the two distance sets also coincide.

Thus the result does not accidentally count (a,b) and (b,a) twice, include diagonal zero distances, or assert only that some selected distances have the requested counts.

## Geometry and classification bridge

The two geometric exclusions use mathlib's ordinary `Collinear ℝ` and `EuclideanGeometry.Cospherical`. The latter quantifies over every centre and radius in the plane. They are stronger than merely excluding our construction's own circle or one particular line.

`equidistant_line_collinear` and `equidistant_circle_cospherical` prove that the reference equidistant predicates imply those ordinary geometric properties. The final theorem then negates the original classification directly, rather than stopping at the stronger auxiliary non-collinearity/non-cosphericity result.

## Explicit exclusions

This does not classify all point sets with the profile. It does not solve the general-position crescent problem, which imposes further restrictions on collinear/cocircular subsets. It does not assert n=1,2,3 examples with impossible geometric exclusions. It does not prove every other result in the source paper, establish discovery priority, establish first-formalization priority, or claim a specific reward. No conjectural lemma or unproved geometric input is assumed.
