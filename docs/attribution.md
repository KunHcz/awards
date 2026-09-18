# Recipient eligibility and contribution attribution

Public records credit mathematical and formalization contributions using their published sources. These contributions may come from different people or teams.

For solver and Lean credits in the problem bank, see the [attribution conventions](../problems/README.md#attribution-conventions). Each **Attribution basis** row links to the evidence supporting those credits.

Recipient identities require confirmation before publication. Keep identity documents, private contact details, written agreements and private payment arrangements out of public issues and repository files. Public identity attestations and contribution descriptions must be authorized for publication.

A contribution credit or candidate record does not announce an award. Confirmed recipients appear in the relevant [award record](../awards/README.md).

## Claiming an award

Use the [award claim form](../.github/ISSUE_TEMPLATE/claim-award.yml) only
for your own contribution. The issue author's GitHub account is the applicant
account; entering someone else's account in the text does not change the applicant.
Proxy applications and collection on another person's behalf are not accepted.
Every application must include the problem-bank link, the original Lean proof
repository URL and a follow-up contact email. The repository must belong to the
same GitHub account that submits the issue. The contact email is public; provide
an address intended for public correspondence. It is a communication channel,
not independent identity evidence. Link related claims for the same problem and
update an existing application instead of submitting duplicates.

Only complete solutions to the original problem are accepted. Partial mathematical
results and incomplete Lean formalizations are not eligible. Select mathematical
solution, Lean formalization, or both, and link the problem-bank entry for the
JSP ID in the issue title. Maintainers use its existing proof, source and attribution references
together with the required original repository URL; applicants do not need
to resubmit proof materials. Explain only unresolved account-to-contributor links
or attribution discrepancies. If catalog information is missing or incorrect,
link a correction issue or PR and resolve the relevant discrepancy before claim
approval. A declaration in the form is not proof of identity or contribution;
maintainers must verify it before approving the claim.

### Mathematical solver verification

Use the complete proof or publication and attribution evidence already linked in
the problem-bank entry, including the recorded co-contributions. Do not ask the
applicant to duplicate those references. A new GitHub account is permitted; prior
GitHub activity is not a condition for a mathematical claim.

Maintainers assess whether the result solves the full original problem and whether
the evidence supports the claimed contribution. They independently locate an
established author contact channel in the publication, institutional profile or
historical project, and ask the author to confirm their connection to the applicant
account, the issue and the contribution description. Do not rely solely on a new
contact address supplied by the applicant. Where such a channel is unavailable,
use additional historical evidence and independent corroboration; the identity
remains pending until the evidence is sufficient. Co-authorship alone does not
establish sole credit or resolve competing claims.

Applicants must propose an independently verifiable way to confirm their identity.
No single verification method is mandatory.
Possible methods include:

- Send confirmation to `thejustinsunprize@hejustinsun.com` from an author email
  independently located in the paper. Maintainers verify control of that established
  mailbox through a fresh reply or challenge; a displayed sender name, forwarded
  message or screenshot alone is insufficient.
- Respond to a fresh challenge through an established institutional or author
  website already publicly linked to the author.
- Sign a fresh challenge using a historical key already independently associated
  with the author. A newly created key with only a self-declared name is insufficient.
- Propose another verifiable method or a combination of historical records and
  independently contacted corroborators for maintainer review.

The identity confirmation must bind the applicant to the GitHub account, claim
issue, problem ID and claimed role(s). Maintainers assess whether the evidence
establishes the identity connection and may request additional
verification. A claimed affiliation, profile link or proposed method alone does
not verify identity. Name the intended method in the public issue, but keep private
evidence in the designated private channel. Email is one option, not a requirement
to obtain or regain access to a particular mailbox.

### Lean contributor verification

Check the original Lean proof repository URL supplied in the claim. Its owner must
be the issue author's GitHub account; a mirror or collection of someone else's
proof is not an acceptable original source. Compare it with the pinned proof
version, theorem and attribution references in the problem-bank entry. Applicants
do not need to repeat branch, commit or theorem details already recorded there.
Resolve missing or conflicting references through a linked catalog correction.
Keep proof source and build artifacts in the external repository.

The applicant must be the actual contributor using their own account associated
with the proof contribution. Repository ownership, being the last committer, or
uploading someone else's code does not establish authorship. Commit author text
and screenshots alone are insufficient. Work committed through a bot, shared
account or another contributor requires a documented connection to the actual
applicant and manual review; it does not permit someone else to claim for them.

Submitting the issue confirms control of the submitting GitHub account. Maintainers
must separately match that account to the formalization author identified in
source records such as `sources.yaml` or the original repository's authorship
credits. A catalog display credit based on repository ownership is insufficient.
If source attribution does not establish the account-to-author connection, use
the independent identity-verification process described for mathematical solvers;
the claim remains pending until that connection is verified. Posting the issue
does not by itself establish authorship or mathematical correctness. Lean-only
applicants may leave the identity-verification-method field blank only when source
attribution establishes the connection. Applicants claiming both roles must still
complete the mathematical solver identity verification.

### One person claiming both contributions

Use one issue with both roles selected. Review the mathematical and Lean evidence
from the catalog separately; approval of one role does not approve the other. Once identity is
confirmed, associate both contributions with the same recipient rather than
creating duplicate identities. Each approved contribution is handled under its
applicable award decision, with duplicate claims checked before payment.

### Payment arrangements

After contribution and identity verification and award confirmation, maintainers
agree payment arrangements with the recipient through the designated private channel.

Maintainers privately link the verified recipient, claim and approved contribution
roles to the agreed payment arrangements. Changes require fresh confirmation
through the verified recipient channel. Each approved contribution remains
recorded separately.

### Maintainer review record

The process is: self-application, contribution review, identity verification,
recipient and award confirmation, public announcement, private payment
arrangements, then payment.
Record mathematical and Lean review outcomes separately, including not applicable
where appropriate. Retain the catalog revision and proof references used in the
review so later catalog changes do not silently change the reviewed claim. In the
public issue, record the review outcomes and authorized public evidence. Retain
private verification and payment materials in the designated private channel.

Only maintainer-reviewed outcomes establish verification. Applicant edits and
checkboxes cannot mark a claim verified. An issue form cannot technically prevent
impersonation or proxy submissions; maintainers reject those claims during review.
These review notes are not new award-record lifecycle values and do not change
the existing requirements for confirmed recipients or published award records.
