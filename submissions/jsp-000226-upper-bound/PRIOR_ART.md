# Sources, prior art and precise contribution

## Primary statement

S. Tengely, M. Ulas and J. Zygadło, *On a Diophantine equation of Erdős and Graham*, arXiv:2008.01501v1 (4 August 2020), Conjecture 3.7, printed page 11.

- Versioned source: https://arxiv.org/pdf/2008.01501v1
- Bibliographic record: https://arxiv.org/abs/2008.01501
- Journal: Journal of Number Theory 217 (2020), 445–459.
- DOI: https://doi.org/10.1016/j.jnt.2020.05.006

The PDF statement was visually checked. It states the bound for all solutions; the subsequent plot concerns greedy solutions. These two quantifier scopes must not be conflated. The published journal's bibliographic record and indexed statement were located, but the exact formal target here is the accessible arXiv v1 statement.

## Important pre-existing material in the same paper

After the 185-term witness was found and certified, we checked the occurrence of terminal exponent 392 in the paper. Corollary 3.6, printed page 10, already reports greedy blocks with

```text
left exponent    number of terms    terminal exponent
8                13                 32
32               9                  46
46               169                392
```

Substituting the second block for 32 and the third block for 46 in the first block yields a decomposition of `8/2^8` with `12+8+169=189` terms and terminal exponent 392. Prepending the terms with exponents 3 and 6 yields a decomposition of `2/2^2` with **191** terms. This is also a counterexample, because `392 > 2(2+191)=386`.

We reconstructed these blocks with the stated greedy procedure and checked the exact rational identity and exact integer certificate. See [paper-derived-witness.json](paper-derived-witness.json) and [evidence/paper-derived-arithmetic.json](evidence/paper-derived-arithmetic.json). That secondary witness is checked with Python; the main **185-term** witness is the one independently formalized and replayed in Lean.

Thus the ingredients of a longer counterexample were already present in the 2020 paper. We do not claim that the entire underlying construction is new, that the 185-term list is minimal, or that this resolves the authors' possible intended greedy-only question. The precise contribution is an independently found shorter explicit witness, its complete Lean certificate, and identification of the failure of the universal wording. This prior-art qualification is central, not a footnote to an unqualified breakthrough claim.

## Related submissions

- JSP-000226: https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000226
- Our earlier PR #60: https://github.com/TheJustinSunPrize/awards/pull/60

PR #60 formalizes the classical Borwein–Loring infinite family. It does not address the universal terminal-exponent upper bound. This package is a different, expressly scoped proposition and must not turn the entire combined JSP record or all of Erdős 261 into a solved problem.

The current Erdős 261 statement and its forum, the official prize PR search for JSP-000226, searches for the paper identifier and conjecture number, and relevant indexed public code were checked on 16 September 2026. We did not locate a separately published prior refutation in those searches. Search coverage is incomplete and absence of a result is not a priority certificate. Existing 2020 data are credited above regardless of whether their implication has previously been noticed.

## Review status

No independent human review, journal acceptance, worldwide priority determination, official prize verification or award has occurred. Please decide whether the precise wording issue and its formal certificate fall within the catalog or should be treated as a separate correction/community contribution. No award tier or allocation is asserted.
