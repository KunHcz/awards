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
infinite-series questions. This package proves only the complete first subproblem.

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

The file uses the pinned mathlib arithmetic and finite-sum library. All six printed
axiom reports contain only Lean's standard foundations, and the complete imported
environment is replayed. No custom conjecture, special-purpose oracle, proof hole, or
native-evaluation shortcut is used. Negative controls deliberately change the family
formula and collapse the summands to repeated exponents; both fail proof checking.

The complete first subproblem is not the complete JSP entry. No catalog status change
or claim about the still-unproved all-`n` and infinite-series parts is requested.
