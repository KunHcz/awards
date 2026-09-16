# Statement correspondence

## English

### Original problem and the quadratic subproblem

[The JSP catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000388) concerns an additive complement to a polynomial's
integer value set. [Erdős 477 and its comments](https://www.erdosproblems.com/forum/thread/477)
distinguish the quadratic obstruction from the higher-degree positive construction.
[The reference Lean file](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/477.lean) includes a quadratic variant requiring `a | b`
and nonzero `a,b`. This package removes both restrictions on `b`; only the mathematically
necessary leading coefficient condition `a != 0` remains.

The difference-set argument for general quadratics is credited in the source comments
to the combined work of AlphaProof and Sarosh Adenwalla. This is not a claim to discover
that argument. The earlier square case is attributed there to Sekanina (1959).

### Exact meaning of uniqueness

`ExactComplement f A` means that for **every** integer `z` there exists exactly one
pair `(u,v)` in `A × range f` with `z=u+v`. Two inputs `x,y` with `f(x)=f(y)` do not
create different pairs. This avoids the false shortcut of treating the noninjectivity
of a quadratic as a counterexample on its own. The set `A` is unrestricted: it may be
empty, finite, infinite, positive, negative, or unbounded in either direction.

### Proof

An infinite subset of the integers has two distinct elements congruent modulo any
nonzero integer `q`. If the difference set `range f - range f` contains every multiple
of `q`, these two elements give **different value pairs** with the same sum. Consequently
an exact complement would have to be finite.

A finite complement cannot work when `f` is bounded on one side: its translates remain
bounded on that side and cannot cover all integers. Every genuine quadratic is bounded
on one side. Explicit bounds proved in the code are `f(x) >= c-b^2` when `a>0` and
`f(x) <= c+b^2` when `a<0`.

Finally,

```text
b != 0: f(k)-f(-k) = 2*b*k;
b == 0: f(k+1)-f(k-1) = 4*a*k.
```

The corresponding modulus is nonzero. This proves the obstruction for **all** integer
coefficients with `a != 0`, not only a fixed example or a finite coefficient range.

### Lean interface and boundary checks

`no_quadratic_complement` is the coefficient form;
`answer_quadratic` expands the original target/value-pair quantifiers;
`no_degree_two_polynomial_complement` applies to every `p : Polynomial Int` with
`p.natDegree = 2`, after proving the leading coefficient nonzero and expanding its
evaluation. The last theorem `linear_has_complement` proves that `f(x)=x` does have the
complement `{0}`, so dropping the degree-two restriction would change the answer.

All thirteen declarations are included in the axiom inventory and full environment
replay. One negative control changes `2*b` to `3*b`; another removes the nonzero
leading-coefficient hypothesis. Both must fail. The public claim remains a fully
proved subproblem, not a proof of the higher-degree existence theorem.
