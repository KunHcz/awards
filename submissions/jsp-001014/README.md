# JSP-001014: unique prime and squarefree translates

## English

This submission formalizes the **known diagonal Dirichlet construction** answering the first two questions of [Erdős problem 1209](https://www.erdosproblems.com/1209), associated with [JSP-001014](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-1001-1022.md#JSP-001014). It supplies complete proofs of those two statements and an extension covering **all integer shifts**, not just nonnegative ones.

It does **not** claim a new mathematical discovery or a solution of every question grouped under Erdős 1209. In particular, the separate questions about the fixed sequence `2^(2^k)` are outside this contribution. This is a formalization submission, not an award announcement.

## Result

For every function `f : Nat -> Nat`, there is a strictly increasing sequence `a` of natural primes, with `a(k) >= f(k)` for every `k`, such that

- the set of natural shifts preserving primality of every term is exactly `{0}`;
- the set of natural shifts preserving squarefreeness of every term is exactly `{0}`.

The stronger integer-domain construction gives both singleton conclusions for **every integer shift**, including negative shifts. The natural-domain file also proves the exact negations of the original existential-growth-threshold assertions.

These are infinite, universally quantified theorems. No finite search bound, assumed prime generator, unproved number-theoretic hypothesis, or finite enumeration stands in for the conclusion. The existential prime choice is justified by mathlib's proved Dirichlet theorem.

See [STATEMENT.md](STATEMENT.md) for definitions, correspondence, a mathematical proof, and exclusions.

## Proof files

| File | Content |
| --- | --- |
| [JSP1014/NaturalShifts.lean](JSP1014/NaturalShifts.lean) | Nine theorems, including `answer_prime` and `answer_squarefree`, with the complete growth and infinitude quantifiers. |
| [JSP1014/IntegerShifts.lean](JSP1014/IntegerShifts.lean) | Eleven theorems, including completeness of the enumeration of all nonzero integers and the two singleton-translate conclusions. |
| [scripts/verify.py](scripts/verify.py) | Clean rebuild of this package, twenty-declaration axiom audit, fresh-environment kernel replay, and five negative controls. |

## Pinned reproduction

Install the official Lean toolchain manager `elan`, Python 3.9 or later, and Git. From this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.NumberTheory.LSeries.PrimesInAP Mathlib.Data.Nat.Squarefree Mathlib.Tactic
python3 scripts/verify.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
```

The toolchain is **Lean 4.34.0**, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. The mathlib revision is **`5ed2965256430c3649e86755f9576b54eca72435`**. The committed Lake manifest pins transitive packages. The verifier refuses a mismatched toolchain, mismatched mathlib revision, modified tracked mathlib source, missing/repeated theorem audit, or unapproved axiom dependency.

New verification output goes to ignored `verification-output/`; the recorded run is retained in [evidence/](evidence/). The script deletes only this package's generated `.lake/build/` outputs before rebuilding. It does not delete dependency builds or source files.

The bundled `leanchecker --fresh JSP1014` replays imported and local constants into a fresh kernel environment. It uses the **same Lean kernel implementation**, not an independent verifier. Cached upstream mathlib artifacts are used; a full source rebuild of all dependencies is not claimed. Local reproduction and a successful repository CI check are not official verification or prize adjudication.

## Attribution, priority, and intake

Mathematical credit belongs to the pre-existing construction recorded on the problem page. The page does not establish an original discoverer or date for that elementary construction; neither is invented here. The separate Fermat-shift proof credited to Enrique Barschkis and GPT is not copied or claimed.

This Lean implementation was prepared with ChatGPT assistance on **2026-09-16**. We request review of its formalization contribution. First-formalization priority, eligibility of formalizing this older construction, award level, and payment are **not asserted**. The proposed recipient remains `RECIPIENT-jsp-001014-A`, pending authorized confirmation. This is a self-submission with a direct interest in the outcome, not an independent review.

`submissions/jsp-001014/` is proposed as an intake location for the website's Lean-containing PR requirement. It is not a new candidate-record schema. Please redirect the package if another official path is required. No problem-bank flag, solver credit, recipient profile, committee signature, candidate record, or award record is changed. Required designated verification, permanent external archival, recipient confirmation, and committee decisions remain with the operator.

## License

The source and new documentation in this package are provided under [Apache-2.0](LICENSE). Imported libraries retain their own attribution and licenses. The formal statement and proof are newly written here; the Formal Conjectures repository is used as a statement reference, not imported as a source of assumed theorems.
