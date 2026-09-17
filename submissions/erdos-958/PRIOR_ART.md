# Prior art, provenance and scope

## Mathematical ownership

The mathematical construction is Observation 5.1 in Felix Christian Clemen, Adrian Dumitrescu and Dingyuan Liu, *On the mutiplicities of interpoint distances*, arXiv:2505.04283v1, 7 May 2025:

<https://arxiv.org/html/2505.04283v1#S5>

The original eventual classification appears in that paper's introductory Question (4), and is recorded as Erdős Problem 958. We claim no discovery of the circular-arc-plus-centre construction or the negative answer. The package is an AI-assisted implementation of its complete Lean proof, including the original-statement bridges.

Our formal theorem uses n>=4. This is the geometrically valid range for simultaneous non-collinearity and non-cocircularity, and suffices for the original eventual classification question.

## Existing formal statement

The inspected public statement is pinned to formal-conjectures commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`:

<https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/958.lean>

The theorem in that snapshot is a statement with an unfilled proof, not a completed formalization imported by this package. Its ordinary finite-set metric definitions were inspected in `FormalConjecturesForMathlib/Geometry/Metric.lean`. The copied/adapted definitions retain the original Apache-2.0 attribution in `NOTICE` and the proof file header. We import only the pinned mathlib modules listed in the proof.

## Limited pre-publication search

On 17 September 2026, exact original-problem-number searches in the prize repository and a GitHub Lean-code search for `Erdos958` returned no matching submission/proof. The official PR title/body snapshot used in initial selection contained 226 records. These are limited indexed searches, not an exhaustive equivalence check of every proof or a worldwide priority guarantee. The final source and PR checks are recorded in `evidence/prior-art-check.json`.

### Existing four-point formalization found in follow-up review

A subsequent direct source check found the following existing proof, whose header credits **Aristotle and Boris Alexeev**:

<https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos958.lean>

That file proves the distance profile and failure of line/circle classification for four named points. Its final `not_erdos_958` refutes a classification quantified over all finite sets. This package instead constructs counterexamples for every `n >= 4` and directly refutes the **eventual** classification for all sufficiently large sizes. The difference is the cardinality quantifier, not a claim that no previous Lean work existed. No proof code was copied from that file. It was inspected for this scope comparison, not rebuilt here. Its authors retain their formalization credit; our initial negative keyword-search result does not establish first-formalization priority.

A broader distance-multiplicity search found this relevant scope warning:

<https://github.com/TheJustinSunPrize/awards/issues/57>

That issue asks to restore the general-position constraints in JSP-000199. It is a public correction request, not a maintainer ruling. Regardless of its eventual handling, our source claim is the line-or-circle classification of Erdős 958, not the general-position crescent question. Our arc points are deliberately cocircular, and we do not claim they satisfy the latter's restrictions.

## Prize relationship

A matching numbered JSP entry has not been established. The submission requests catalog inclusion or correspondence review for **Erdős 958**, with complete formal evidence. It must not be recorded as a solution of JSP-000199, as a numbered accepted claim, or as a million-dollar/Pinnacle project. No fixed non-Pinnacle reward or personal allocation has been confirmed.

The formalization was completed in September 2026, while the mathematical result predates 2026. Application of the prize's completion-date rule, attribution, first-formalization priority and any amount remain for the organizers to determine. The local checks are not independent human review or an official award decision.

The original proof implementation and verification files are Apache-2.0. The cited paper is not redistributed. Source definitions, mathlib and Lean retain their original ownership and licenses.
