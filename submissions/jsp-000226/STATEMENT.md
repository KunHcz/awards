# Statement correspondence

## English

### Original source and claimed scope

The original equation appears in Erdős–Graham, *Old and new problems and results in
combinatorial number theory* (1980), p. 63. Borwein–Loring, *Some questions of Erdős and
Graham on numbers of the form sum g_n/2^{g_n}*, Mathematics of Computation 54 (189) (1990),
377–394, provides the consecutive-block family. Tengely–Ulas–Zygadło restate the
identity explicitly in Remark 2.2 of
[arXiv:2008.01501v1](https://arxiv.org/html/2008.01501v1#S2), published in Journal of
Number Theory 217 (2020), 445–459. The problem page also credits an earlier infinitude
proof by Cusick as reported by Erdős.

[The JSP catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000226) groups several questions.
[The reference Lean statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/261.lean) separates the infinitude statement
`erdos_261.parts.i`, the all-positive-integers statement `parts.ii`, and the
infinite-series questions. This package proves the complete first subproblem and the
related sharp fixed-term extremal statement from TUZ Theorem 2.1(i), with its equality case.

### Definition fidelity

`Representable n` requires `t >= 2`, a function `a : Fin t -> Nat` which is injective,
positive values for every index, and equality in the rational numbers. No division is
natural-number division. The denominator `2^a` is always positive. The constructed
terms `n+i+1` are strictly increasing, so they also satisfy the ordered convention of
the original paper. Injectivity counts different exponents, not repeated copies.

### Proof map

| Lean theorem | Mathematical role |
|---|---|
| `block_sum` | Telescoping identity for every natural starting point and finite length. |
| `family_bound` | The family value is at least its index, ruling out a finite repeated witness family. |
| `family_balance` | Controls natural subtraction in the formula: `family m + m + 2 = 2^(m+1)`. |
| `family_identity` | Exact rational identity for the consecutive block. |
| `family_representable` | At least two distinct positive summands for every `m >= 2`. |
| `infinitely_many_representable` | For any bound `b`, a qualifying positive family member exceeds `b`. |

`m=0` and `m=1` are harmless cases of the identity, but are not used as multi-term
representations. The final proof uses `m=b+2` for an arbitrary bound. It does not merely
verify the first few family members or assume the target infinitude statement.

### Verification limits

The file uses the pinned mathlib arithmetic and finite-sum library. All sixteen printed
axiom reports contain only Lean's standard foundations, and the complete imported
environment is replayed. No custom conjecture, special-purpose oracle, proof hole, or
native-evaluation shortcut is used. Negative controls deliberately change the family
formula and collapse the summands to repeated exponents; both fail proof checking.

The complete first subproblem is not the complete JSP entry. No catalog status change
or claim about the still-unproved all-`n` and infinite-series parts is requested.

### Sharp fixed-term maximum and equality case

For each `k >= 2`, define `OrderedDecomposition n k` by the existence of a strictly
increasing `a : Fin k -> Nat` with positive values and the exact rational equality
`n/2^n = sum_i a_i/2^a_i`. Then:

```text
IsGreatest {n : Nat | 0 < n and OrderedDecomposition n k} (2^(k+1)-k-2).
```

The bound is Theorem 2.1(i) of TUZ; Remark 2.2 establishes sharpness using the
Borwein–Loring family. Our proof also states the equality case explicitly:
at the maximum, every such ordered representation has `a_i = n+i+1` in zero-based
Lean indexing. This is a formalized consequence of the same elementary comparison,
not a claim to a new mathematical discovery.

The function `w(a)=a/2^a` is nonincreasing for positive integers and strictly decreasing
from `a=2`. Positivity and the presence of at least two terms force every exponent
to exceed `n`; strict ordering then gives `a_i >= n+i+1`. Comparing the sum against
the consecutive block and using `block_sum` gives `n+k+2 <= 2^(k+1)`.
At the maximum both sums are equal, so each termwise inequality is an equality.
All comparison exponents are at least three, where strict decrease forces equality
of the exponents themselves.

The hypothesis `k >= 2` is essential: for `k=1`, the equality `2/2^2 = 1/2^1`
does not obey the stated maximum. The weight proof retains the other boundary
case `w(1)=w(2)` rather than incorrectly treating the weights as strictly decreasing
on all positive integers. The verifier changes the sharp bound and the equality
case independently; both mutations must fail.

Additional audited declarations are `dyadicWeight_pos`, `dyadicWeight_succ_le`,
`dyadicWeight_antitone`, `dyadicWeight_strict`, `exponent_after_start`,
`ordered_exponent_bound`, `sharp_start_bound`, `family_ordered`, `maximal_start`,
and `maximal_representation_unique`.
