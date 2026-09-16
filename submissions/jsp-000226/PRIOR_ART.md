# Prior art and contribution boundary

## English

The mathematical result is old. Credit for the displayed family belongs to Borwein and
Loring (1990); the source page also reports Cusick's earlier infinitude proof. This
submission claims the present Lean proof and reproducibility package only.

The reference Formal Conjectures file at commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152` lists the identity, its representation property,
and `erdos_261.parts.i` as unfilled proof statements. The code here was written for this
project using the published identity and mathlib. It does not import those placeholders.

The official pending PR list, including PR #40's batch registration of existing proofs,
and searches for `JSP-000226`, `Erdos261`, and `borwein_loring` were checked before
implementation. No same-scope proof submission was located in those checks. Search
coverage, indexing delays, other symbol names, and unpublished work remain limitations.
This is not a certification of first-formalization priority.

The package does not repackage the existing JSP-001014 submission: its statement,
mathematical construction, and proof are different. Generic validation code is reused
from this project's tooling. Submission-time screening is recorded separately in
[evidence/prior-art-check.json](evidence/prior-art-check.json).

References: [Erdős 261](https://www.erdosproblems.com/261),
[original family publication](https://www.jstor.org/stable/2008700),
[2020 paper, Remark 2.2](https://arxiv.org/html/2008.01501v1#S2),
[reference statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/261.lean).
