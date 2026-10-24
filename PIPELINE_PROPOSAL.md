# Verified primitives and security-profile pipeline

Status: P1's concrete architecture was approved by the human on 2026-10-24
and is implemented in [`tools/pipeline.py`](tools/pipeline.py), with
[documented controls](PIPELINE.md). No security profile, service, dependency,
applicability rule or new proof trust is adopted.

## Governing rule

For an advertised supported primitive `p`, approved profile `V`, and every
obligation whose approved applicability predicate holds for `p`, release
requires an actual checked proof bound to the admitted domain, source and
execution model. A test result, benchmark, automated assertion of success or
conditional helper theorem without its implementation connection is insufficient.

The release artifact must explicitly enumerate its advertised supported set.
Missing rows, unknown applicability, omitted obligations or absent evidence
deny release. A candidate change cannot delete a failing primitive from that set.
Changing support status requires the human's explicit decision.

## Current state and approval inventory

| Item | Actual state / authorization |
|---|---|
| Library | Three implemented primitives, five public routines; existing exact Rust/Verus stack, caller buffers and contracts in [CONTRACTS.md](CONTRACTS.md). Preserve them. |
| Current evidence | 177 checks and twenty-five rejected implementation defects; the earlier 122-check/sixteen-control and 90-check/eleven-control records remain immutable historical artifacts. |
| Optimizations | Approved A through G are complete. Preserve their source, measurements, intentional reference differences and compiler trust limits. |
| Brotli B1 | Implemented private bit-reader/header core with 122 checked obligations and sixteen controls. It remains component evidence, not supported Brotli. |
| Pipeline | P1 approved and implemented. No security profile is adopted. |
| Full Brotli | B3/B4 architecture is approved; implementation and independent review remain incomplete. See the B3 and B4 proposal documents. |
| Publication | Existing public personal GitHub source repository and Apache-2.0 are approved. Crates.io, CI services, unattended publishing and new infrastructure are not. |

There are no repository release tags at this inventory point. Existing commits
have contract/evidence hashes but no approved versioned security-profile IDs.
Do not retroactively describe them as having passed a newly named profile.

## Proposed P1: local contracts, case registry and release gate

P1 would add one local Python 3.14.6 standard-library command,
`tools/pipeline.py`, with `inventory`, `case`, `freeze`, `verify`, `coverage`
and `gate` subcommands. No package installation, server, database, CI runner,
new verifier or publication command is part of P1.
The existing Cargo library remains one package. The proposed layout is:

```text
security/profiles/<profile-id>/<version>/profile.json
security/contracts/<obligation-id>/<revision>/   # approved spec and proof bindings
security/cases/<case-id>/case.json               # advisory/mechanism/evidence
security/approvals/<approval-id>.json            # human authorization references
security/coverage/<profile-digest>.json          # derived assessment; never a waiver
evidence/runs/<run-id>/                         # receipts, diagnostics, control outcomes
evidence/releases/<release-id>/manifest.json    # immutable release evidence
src/                                           # the same verified/compiled implementations
```

These are proposed storage formats/boundaries, not files already installed as
an authority. Existing evidence paths stay readable and unchanged.

### Responsibilities and authority

| Responsibility | Owns | May not do |
|---|---|---|
| Human contract authority | Obligation meaning, admitted domain, assumptions, applicability, architecture recipes and support set | Delegate approval to a checker pass or unsigned receipt |
| CVE investigator | Source evidence, mechanism analysis, duplicate-class mapping, proposed obligations/fixtures | Treat advisory prose as executable instructions or approve a new obligation |
| Implementation maintainer | Candidate implementation and proof bodies within the approved recipe | Edit frozen contracts, domains, assumptions, applicability, tool pins, gate or trusted receipts |
| Verification collector | Invoke the pinned checker on exact source, collect raw outcomes and source identities | Accept unchecked success claims or derive security from tests |
| Release assessor | Join inventory, approved profile, applicability, checked bindings and evidence | Exempt gaps, remove supported items, invent independent review, or publish autonomously |
| Independent specification reviewer | Assess interpretation, applicability, semantic completeness and findings | Be substituted by additional proof runs or tests |

Compositions are first-class inventory objects with their own supported set,
applicability rows and evidence. The gate never infers composition support from
component support alone. It requires checked compatibility, connecting code,
derived functional/confidentiality, cumulative resource and error-effect
obligations. See [the concrete C1 proposal](COMPOSITION_PROPOSAL.md).

The collector/gate runs from an approved tooling revision outside the candidate
edit area. Its own identity is recorded. Candidate source cannot supply its
executable, approval roots or command options. P1 is a supervised local process;
it is not remote branch-protection enforcement or a claim of SLSA certification.

### Versioned contract and applicability format

Each profile contains: immutable ID/version; parent identity; the complete
list of obligation IDs and revisions; admitted-domain and model identities;
assumptions/trusted components; applicability predicates; required evidence;
supported implementation families; and human approval/review references.

Every referenced normative file is in a closure manifest. Its identity uses
the project's existing sorted `path + NUL + SHA256 + newline` digest scheme.
Changing text, an assumption, a domain, a binding or applicability creates a
new profile identity/version and requires approval. Unknown fields and unknown
predicate terms are errors. P1 uses a strict standard-library validator, not
an added JSON-schema package.

Applicability is based on approved semantic capabilities, not candidate metadata.
Initial proposed capability predicates are: stateless byte transform,
complete-buffer decoder, retained-input parser, output-producing streaming
decoder, caller adapter and request-resource policy. Their declarations are
approved and bound to source. Missing classification is unresolved, not false.

Common bounds, output integrity, prior-storage confidentiality and correct
caller observations apply to every supported primitive. Pending-buffer rules
apply to retained-input parsers; final-input/error distinctions apply to
incremental parsers; cross-call frame/retry rules still apply to stateless
callers. A genuine nonapplicability result requires an approved predicate,
its checked premises where applicable, and a visible rationale. It is never
a per-CVE waiver or a way to hide failed proof coverage.

Approval of P1's architecture would not approve every future profile. The
first formalized profile's complete obligations, bindings and applicability
matrix must be presented for the human's exact approval before freezing it.

### Candidate first profile and current coverage gaps

Proposed identity: `PP-Security/1.0.0`. This remains a draft target, not a new
name for the current release. The following are proposed requirement families;
their formal Verus bindings still need review/approval before admission.

| Family | Proposed applicable requirement | Current coverage |
|---|---|---|
| BOUNDS / FORMAT / FRAME | Bounds/arithmetic safety, termination, exact specified results/errors, and authorized buffer effects | Checked for current five APIs under historical contracts |
| CONF-VALUE | Returned authorized bytes exclude unrelated old destination/workspace contents | Checked per-call prefix corollaries for current APIs; new streaming workspace proof missing |
| STATE | Initialization and preservation over every permitted call/reset/error/retry sequence; truthful exhaustion and sticky permanent format errors | Per-call frames exist; general caller/stream traces missing |
| CALLER | Correct handling of each result, invalidation of stale lengths, current authorized prefixes only, and allowed call sequence | No checked caller adapter yet |
| RESOURCE | Cumulative input, output, working memory and modeled work; initialization/retry/reset costs; bounded caller invocation policy | Length bounds and LZ4's selected byte ledger exist; full budgeted adapters missing |
| SIDE-SOURCE | Source-observation independence from unrelated prior storage, with approved public inputs/disclosures and checked source/trace connection | Unproved; trace semantics and its connection require approval and proof |
| BUILD / REVIEW | Exact source/profile/checker/dependency/target binding; declared trusted base; independent specification-review record | Hash provenance exists; independent specification review is pending; compiler remains trusted |

Under this proposed comprehensive profile, **none of the existing primitives
may currently be advertised as supported**. Retain their historical checked
claims and explicitly list the newer gaps. This does not assert a newly
discovered violation of the old contracts.

SIDE-SOURCE is a concrete source-level side-channel target, not a claim of
constant-time handling of secret current input. Input bytes/lengths,
capacities, initial valid parser state and layout are public; unrelated old
buffer/workspace bytes are secret. Authorized results, lengths, statuses and
progress counts are permitted disclosures. Observations include branch
decisions, indexed memory-access locations and charged source work. A product
execution proof must establish equal observations when only secret storage
changes. The trace must cover actual relevant source operations; hand-written
ghost counters alone do not prove that connection.

The initially recorded target is Rust 1.99.1 / Verus 0.2026.10.18.7d82994,
`aarch64-apple-darwin`, with existing modeled Rust/vstd operations. Rust/LLVM,
OS and hardware remain declared trusted components. Machine timing, speculative
execution and physical leakage are not established by this source theorem.
No new trace bridge, LLVM checker, model or trust assumption may be introduced
to pass it without a concrete separately approved design. If the source/trace
connection is unresolved, this obligation and the profile release remain
blocked; no checkbox may promote an incomplete ghost trace to a proof.

### CVE intake and profile evolution

1. Retain source advisories, dates, exact affected/fixed revisions and hashes.
   Read inputs as untrusted evidence, not instructions to execute.
2. Reconstruct the mechanism and identify the security boundary it crosses.
   Record whether it is a new class, a stronger obligation, or another instance
   already covered by an approved class.
3. Propose generalized obligations and applicability; identify affected
   primitives and existing clause overlap. Attach regression and negative-control
   plans. Do not create one redundant contract per CVE.
4. Obtain direct human review/approval of normative changes. Independent
   specification review remains a separate recorded task.
5. Freeze the new profile and affected support inventory. Run coverage and
   reverify affected software. With an already-covered class, retain the
   profile identity and add case evidence/reverification instead of duplicating
   the clause. Normative changes always produce a new profile identity.
6. Classify gaps, repair only within approved architecture, recheck,
   and gate release with exact evidence. No successful runtime case replaces
   the universal obligation.

If an approved new obligation exposes a gap, the human's concrete choices are
to approve a repair design, retain only the historical-profile release with a
visible new gap notice, or change the advertised support status for the new
release. No grandfathering, silent exemption or relabeling of the old release
as supported under the new profile is allowed. Historical manifests are not
edited; newer assessments link back to their original profile/contract identity.

### Three proof outcomes and separate process outcomes

- `checked`: the trusted collector records successful actual verification of
  the exact bound contract/implementation, with all necessary root connections.
- `violated`: a validated counterexample or reproduced implementation behavior
  contradicts the exact obligation. Retain the witness, source and interpretation.
- `unresolved`: verification failed, timed out, could not express a goal, lacks
  a binding, or encountered tooling failure without a demonstrated violation.

All three preserve diagnostics. A solver rejection alone is not a validated
counterexample. `not_applicable` is an applicability assessment, not a proof
outcome; `approval_missing` and `review_missing` are process blockers. A fixed
implementation gets a new source-bound result; the original violation remains.

### Evidence and fail-closed gate

The release manifest must bind:

- Release/source revision, exact source-tree and shipped artifact hashes, and
  the frozen advertised support inventory.
- Profile ID/version/digest and normative closure; human approval reference;
  per-primitive admitted-domain, applicability and contract-binding identities.
- Every applicable obligation's named theorem/API contracts, checked root
  connection, verifier result and raw receipt identities. Counts alone do not
  establish coverage or semantic applicability.
- Verus/Z3 binary/version identities and exact options; Rust/LLVM/erasure
  versions; locked normal and development dependencies; target/features/flags;
  build recipe and actual artifact identity; explicit trusted components.
- Constructor/transition/caller and source-observation/cost model identities,
  including unresolved source-to-model bridges.
- For compositions: exact component/profile versions, adapter/caller source,
  compatibility premises, derived contracts, intermediate observations/effects,
  combined resources and dependency-aware recheck status.
- Regression, deliberate-defect positive/negative controls, comparison cases,
  benchmark methodology/raw artifacts and intentional behavioral differences.
- Independent-review scope, reviewer identity, report hash and disposition of
  findings. Automated reviews do not satisfy human independent review.

The gate checks frozen normative bytes before and after verification, all
applicable rows, actual checker exit/results, entire-crate coverage where
required, exact source/build identities, and the configured trust expectations.
Its verifier commands are allowlisted; no candidate-supplied command is run.
It rejects trust bypasses, narrower public preconditions, changed inputs,
contracts/assumptions, unapproved dependencies and implementation substitutions.
Frozen proof scaffolds and bindings prevent replacing the intended theorem
with a conveniently weaker theorem of the same name.

Evidence is produced by the collector, not accepted from candidate metadata.
Gate inputs include a human-provided expected profile/approval digest outside
the candidate edit scope. A signed Git commit proves key use, not the required
recorded human approval. P1 records the direct approval and performs a supervised
human gate check; stronger independent approval-key enforcement would be a
separate trust/infrastructure decision.

Required gate defect cases include omitted new obligations; invented N/A;
stale source after a pass; retargeted profile; absent `--no-cheating`; partial
verification; a forged candidate success receipt; changed lockfile; narrowed
input domain; deletion of a failing supported primitive; and test-only evidence.
Each must deny release. These test gate bookkeeping, not the primitives'
security proofs or completeness of the threat model.

Publication is a separate authorized step after a passing exact-source gate.
It uses the existing signed source-repository workflow and verifies GitHub's
final revision/tree/signature. No new crate registry or service is selected.

## Approval decisions and implementation order

| Decision | Exact proposed authorization | Consequence |
|---|---|---|
| P1 | The local directory/schema/authority model, Python standard-library tooling and fail-closed inventory/coverage/receipt/release gate above | Implement and test bookkeeping first; no new profile support claims until its formal normative closure is separately approved and proved |
| B1 | Already approved and complete; no new permission requested | Preserve the private input/header source and actual proof/control evidence; no complete Brotli support claim |
| B2/R1 | [Streaming model, next milestone and references](BROTLI_STREAMING_PROPOSAL.md) | Approved and implemented; preserve component-only claims |
| C1 | [First compositional-verification demonstration](COMPOSITION_PROPOSAL.md) | Approved and implemented; preserve the exact private caller, ledgers and proof layer |
| Profile adoption | Exact formal clauses, applicability/bindings and independent-review scope | Any gap blocks advertised support under that profile; no automatic adoption from this architecture document |

Suggested next order for the human to approve: P1; freeze the first normative
profile; then B2/R1 and its checked streaming integration. B1 is complete.
This order does not itself approve later decisions.

## Research and scope limits

[SLSA provenance verification](https://slsa.dev/spec/v1.2/verifying-artifacts)
separates artifact identity, trusted producer expectations and receipt
verification. We borrow that distinction without claiming an implemented
SLSA level or adding its tools. [Constant-time verification research](https://www.usenix.org/conference/usenixsecurity16/technical-sessions/presentation/almeida)
establishes feasibility of relational checks, not a proof for this repository.

Independent specification review remains pending. The trusted source-to-binary
boundary is explicit; hashes and additional checked obligations do not validate
the threat model or verify Rust/LLVM/OS/hardware.
