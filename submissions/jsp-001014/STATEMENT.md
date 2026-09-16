# Statement correspondence and proof

## English

### Sources and exact scope

The official bank entry is [JSP-001014](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-1001-1022.md#JSP-001014). Its short description is not used to discard hypotheses or strengthen an award claim.

The detailed source is [Erdős problem 1209](https://www.erdosproblems.com/1209), inspected on 2026-09-16. Its first question asks whether sufficiently fast growth of an increasing integer sequence forces infinitely many prime-preserving translates whenever one exists; its second asks the squarefree analogue. The page already explains a diagonal counterexample to both questions. The other questions concern the specific sequence `2^(2^k)`.

The reference Lean statements are [`Erdos1209.erdos_1209.parts.i` and `.parts.ii`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1209.lean), at revision `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. They quantify over natural-valued sequences and natural shifts. Their growth condition is an arbitrary pointwise lower-bound function. This reference repository is not imported into our proof.

The original bibliography recorded on the problem page is P. Erdős, *A survey of problems in combinatorial number theory*, Ann. Discrete Math. (1980), 89–115. This submission does not assert a first discovery date or a new mathematical resolution.

### Definitions

`Nat.Prime p` is mathlib's standard primality predicate. `Squarefree n` is mathlib's standard algebraic squarefreeness: every `d` with `d*d` dividing `n` is a unit. Over the natural numbers the only unit is 1; over the integers the units are 1 and -1. Thus, finding a divisor `(s+1)^2` for a positive `s` disproves squarefreeness even when `s+1` is composite.

`StrictMono a` means `a(i) < a(j)` whenever `i < j`. All terms are proved prime, hence positive. The input `f` is **any** function `Nat -> Nat`; it is not required to be computable or bounded. The construction actually gives `f(k) < a(k)`.

In the integer extension `Prime (z + (a(k) : Int))` is integer-ring primality, which includes negative associates. The theorem therefore rules out even this larger prime-translate class for nonzero shifts. At zero every term is a positive natural prime, so the ordinary positive-prime interpretation has the same singleton conclusion.

### Natural-shift construction

Fix a positive shift `s` and a bound `B`. Set `m = (s+1)^2`. Since consecutive integers are coprime, `gcd(s,m)=1`; consequently the residue `-s` is a unit modulo `m`.

Dirichlet's theorem supplies a prime `p > B` with

```
p = -s  (mod (s+1)^2).
```

Hence `(s+1)^2` divides `s+p`. If `s+p` were squarefree, `s+1` would be a unit, contradicting `s>0`. This proves `prime_with_square_obstruction` without an assumed existence oracle.

For an arbitrary growth bound `f`, choose `a(0)` using shift 1 above `f(0)`. After choosing `a(k)`, choose `a(k+1)` using shift `k+2`, above `max(f(k+1),a(k))`. The resulting sequence is strictly increasing, prime-valued, and exceeds `f` pointwise. At index `k`, the shift `k+1` produces a nonsquarefree term.

Now let `n>0` be **any** natural shift. Taking `k=n-1` shows that `n+a(k)` is not squarefree, hence not prime. Zero is a good shift because every `a(k)` is prime and thus squarefree. The good-shift sets are therefore exactly `{0}`.

The final theorems `answer_prime` and `answer_squarefree` negate the full assertions

```
there exists a growth bound f such that
for every strictly increasing a above f,
if there exists a good shift,
then the good-shift set is infinite.
```

The quantifier over `f`, the existence of at least one good shift, and the infinitude conclusion are all present. The result is not a finite example or a claim about only some growth rates.

### All-integer-shift extension

Enumerate all nonzero integers explicitly:

```
shift(2t)   = t+1,
shift(2t+1) = -(t+1).
```

The file proves `shift_ne_zero`, the two evaluation identities, and `shift_covers`: every nonzero integer occurs. Negative shifts are therefore not silently omitted.

For a nonzero integer `z`, put `m=(|z|+1)^2`. The integers `|z|` and `|z|+1` are coprime, so `-z` is a unit modulo `m`. Dirichlet supplies an arbitrarily large natural prime `p` in that residue class. Then `m` divides `z+p` in the integers, making `z+p` nonsquarefree. The same recursive construction, now indexed by `shift(k)`, obstructs every nonzero integer shift while preserving the zero shift. It gives both integer good-shift sets exactly `{0}`.

### Correspondence table

| Requirement | Checked declaration |
| --- | --- |
| Arbitrarily large obstructing primes exist | `prime_with_square_obstruction`; `IntegerShifts.obstruction` |
| Every term is prime and above the supplied bound | Each namespace's `sequence_spec` |
| Strict increase | Each namespace's `sequence_strictMono` |
| No omitted positive shifts | Natural `squarefree_shift_iff`, using `n=k+1` |
| No omitted negative shifts | `IntegerShifts.shift_covers` |
| Exactly one good prime shift, not merely finitely many | Each namespace's `prime_shift_iff` and `simultaneous_counterexample` |
| Exactly one good squarefree shift | Each namespace's `squarefree_shift_iff` and `simultaneous_counterexample` |
| Exact negation of reference problem 1209(i) | `JustinSunPrize.JSP001014.answer_prime` |
| Exact negation of reference problem 1209(ii) | `JustinSunPrize.JSP001014.answer_squarefree` |

### What is not claimed

No statement is proved here about whether `n+2^(2^k)` is always squarefree, infinitely often prime, or infinitely often squarefree. The existing Barschkis/GPT proof that it cannot always be prime is a different result. We do not change the official catalog's global status or claim that all of Erdős 1209 is solved.

These are new proof files implementing a pre-existing mathematical argument. A first-formalization claim would require broader priority review than the searches performed here. Local axiom audits and bundled kernel replay do not establish independent human review, designated operator verification, award eligibility, or an award.
