# Brotli B3c compressed-header metering addendum

Status: **Candidate M1 approved exactly as written by the human on
2026-10-29.** Candidate M2 remains unapproved.

Candidate C1 requires every B3c adapter to reserve exact B3a/B3b action work
before the first mutation. Candidate W1 separately fixes the private
`CompressedMetaBlockDecoder::step(input, end_of_input) -> CompressedHeaderStep`
interface, and `CompressedHeaderStep` contains only `consumed` and `status`.
The current unpublished C1 adapter bridges that mismatch with the deliberately
conservative reservation
`17_728_416 + 5_640 * budget-limited-input-bytes`. That bound is not an exact
ledger and cannot be used as completion evidence.

Both candidates below preserve the public Brotli API, caller-owned workspace,
W1/E1 serialized bytes and tags, C1 workspace assignment, status/error mapping,
dependencies, safe-Rust boundary, bounded loops and proof trust boundary. Both
remove the conservative constants and add unchanged-specification undercharge
controls for every newly exposed formula. Neither candidate changes supported
format claims or completes B3d/B4.

## Candidate M1: B3c-owned read-only planning and reservation

Keep the exact W1 `CompressedMetaBlockDecoder` and `CompressedHeaderStep`
interfaces unchanged. `advance_serialized_compressed_header` remains the sole
owner of `RequestBudget` and drives one existing B3b phase action at a time.

Before a mutating phase action, the adapter performs a read-only plan over the
current serialized state and the budget-limited input prefix. It charges each
planning input-byte, bit, prefix-record, table or context-cell read as it is
performed, computes the exact remaining writes/cell visits/state transitions
for that one action, reserves that amount, and only then invokes the existing
phase helper. MTF and coverage retain their approved pre-scan/formula/atomic
execution order. The adapter repeats until the existing W1 stopping condition:
`NeedInput`, `Complete` or permanent failure.

The consequence is that B3c continues to own resource policy and B3b remains
independent of the public budget type. The cost is a larger proof surface:
read-only plans must be proved to select exactly the same next phase action as
the existing mutating helpers, and every plan/execution pair needs an exact
frame and unchanged-specification undercharge control.

## Candidate M2: budget-aware private B3b metered driver

Keep the existing W1 `step` method and result type for the checked B3b component,
and add one `brotli_input.rs`-private metered driver used only by the C1 adapter.
The driver receives `&mut RequestBudget`, performs the same W1 phase loop, and
charges exact input reads, bit/record/cell visits, writes and transitions
immediately before each action. It returns the existing
`CompressedHeaderStep`; no work field or persistent counter is added.

The consequence is less duplicate planning logic and direct incremental
charging. It also makes the private B3b driver depend on the B3c public-core
budget representation and moves resource-policy ownership across the existing
W1/C1 component boundary. The original unmetered W1 `step` remains available
only for its private component proofs and tests; C1 decoding uses the metered
driver.

## Approval requested

The human approved **Candidate M1 exactly as written** on 2026-10-29.
Candidate M2 remains unselected.

## Nested transition rule

On 2026-11-03 the human explicitly selected **charge nested resets/starts
separately**. The scope and examples are recorded in
`BROTLI_M1_TRANSITION_RULE_DECISION.md`. C1's 425-unit construction/reset charge
remains fixed.

## Implementation checkpoint

M1 remains **incomplete**. The current implementation is a reviewable B3c
checkpoint, not an exact-resource or complete-decoder claim.

Candidate read-only planners and prepaid executors cover block counts, initial
block-length symbols and suffixes, distance parameters, literal context modes,
block type/length trees, tree groups, and late context-map MTF/coverage/handoff.
The B3c adapter now repeats supported planned actions instead of invoking the
conservative driver immediately after its first successful action. W1's `step`
interface and serialized tags remain unchanged.

The 2026-11-02 continuation corrected three concrete planning/execution gaps:

- Tree planning retains newly produced code lengths in a local 704-byte image,
  copies only the already initialized builder prefix, charges those reads, and
  calculates installation work from the replayed image. Reading the original
  workspace at installation time missed newly decoded spans.
- Serialized execution advances the completed auxiliary alphabet through its
  existing zero-input transition before storage. That transient B3a result has
  no E1 serialized tag; attempting to store it previously rejected valid
  complex trees. The planner performs the same transition.
- Installed-symbol planning now rejects an out-of-width canonical record before
  reversal and uses the existing checked reversal helper, matching W1's
  malformed-record behavior.

The new dense and sparse complex-tree regression exercises every byte split
under three old-workspace fill patterns, checks that planning preserves the
workspace, checks the charged planning total, compares planned consumption and
status with execution, and checks the resulting builder lengths. The distance
reservation fixture also initializes the block counts that precede its phase.

Five additional deliberate-defect controls cover the simple/canonical install,
repeat-serialization, initial-symbol and serialization-base arithmetic
contracts. These controls do not establish full planner/action refinement.
The preceding checkpoint's source-bound verification and runtime results are recorded in
`evidence/brotli-b3c-m1-checkpoint.json` and
`evidence/brotli-b3c-m1-verification.json`.

The fresh whole-crate run completed with **1,058 verified, 0 errors** and
`--no-cheating`. Release validation passed 68 library tests, nine primitive
tests, the source trust-bypass check and the upstream comparison: **79 tests**.
All **21 arithmetic undercharge mutations** across five metering groups were
rejected after that unchanged whole-crate positive control. Distance mutations
are scoped to their named function so a repeated formula in another helper
cannot redirect the control. Full checker output, source identities and the
retained rejection transcripts are bound in the checkpoint evidence.

### Context-tree-count continuation

The B3c dispatch boundary now plans and prepays context-map phase 0 as a
separate existing W1 action. The plan charges its input-byte and bit reads
before parsing. It reserves queue and variable-integer serialization, the
decoded tree count, phase transitions, and the full zero-map initialization
when the count is one. EOF reserves the existing four terminal bytes and its
transition before recording `Truncated`.

Checked contracts bind planned consumption, logical queue bits, variable-integer
phase, tree count and next context phase to the existing W1 transition. The
single-tree case proves every initialized map cell is zero. Additional frame
contracts preserve every workspace byte outside the action's scalar fields and
active map. A failed execution reservation preserves the complete workspace and
all remaining credits; successful execution debits its reserved work and input
exactly. Workspace/encoding failures from cursor loading are distinguished from
input truncation.

The runtime matrix compares entire workspace images with W1 for both map kinds,
minimum/intermediate/maximum map lengths, old-byte patterns, queued and supplied
bits, integer phases, and exact/one-short work limits. It also checks empty
input, EOF, input-credit exhaustion and entry through the B3c dispatch loop.
Thirteen additional defect controls cover work formulas, planning/execution
debits, late reservation, decoded count, zero-map values and progress framing.
Fresh whole-crate and control results for this continuation are recorded in
`evidence/brotli-b3c-m1-context-count.json`.

The continuation's whole-crate run passed **1,067 verified, 0 errors** with
`--no-cheating`. All **81 release tests** passed: 70 library tests, nine
primitive tests, the source trust-bypass check and the upstream comparison.
The **13 new controls** and **21 existing metering controls** rejected all
deliberate defects after that unchanged whole-crate positive control. The
counter-update proof uses the pinned checker's per-function solver isolation;
all functions remain checked, with no assumptions or trust shortcuts added.

This slice proves the named logical-state, frame and quota properties. It does
not close the remaining proof that every source action matches the complete
work ledger, or byte-for-byte plan equality inside the serialized cursor.
The frame uses the union of phase-0 write regions; smaller per-status write
footprints remain a separate obligation.
The conservative W1 fallback can still traverse later context tree counts
after entering an unsupported phase; full M1 coverage requires replacing that
fallback as well.

### Context-bit continuation

The B3c dispatch boundary now also plans and prepays the existing W1 context
bit actions in phases 1, 2, 5 and 6: RLE selection, RLE prefix width, repeat
suffix/zero expansion, and MTF enablement. The plan charges input-byte and
completed-field bit reads before replay. It keeps the budget in B3c and invokes
`advance_context_bits_phase` only after reserving the execution formula.
W1's `step` interface and serialized state remain unchanged.

The bit-action formula is:

```text
read_work + 10 queue writes + 1 bit-action transition
+ NeedInput: 0
+ Truncated: 4 terminal writes + 1 terminal transition
+ Value:
    phase 1, zero / phase 2:
        76 tree-start writes + 1 tree-start transition
        + 1 max-run write + 1 context-phase write + 1 context transition
    phase 5, valid repeat:
        repeat map writes + 4 progress writes + 1 pending-run reset
        + 1 context-phase write + 1 context transition
    phase 5, overshoot:
        4 terminal writes + 1 terminal transition
    phase 1, nonzero / phase 6:
        1 context-phase write + 1 context transition
```

The tree-start writes comprise 66 scalar clears, one pending-span clear, one
region write, six tree/alphabet bytes and two builder-initialized bytes. The
formula's equality and exact debit are checked separately from the still-open
complete source-operation ledger binding.

The strengthened W1 bit-transition contract now includes EOF and repeat
overshoot. Checked plan/action relations bind consumption, logical unread bits,
next context phase, tree-start fields, repeat extent and newly zeroed map cells.
The existing tree-start helpers now expose their byte frames. The bit-action
frame preserves every byte outside its phase-category scalar/map regions.
Execution reservation failure preserves the entire workspace and all remaining
credits; planning charges remain spent. Input-credit exhaustion preserves the
advanced partial queue and is distinguished from final input truncation.

The runtime matrix compares complete workspace images with W1 for **5,376**
configurations, each with exact and one-short execution work. It covers both
map kinds, maximum map sizes, three old-byte patterns, all repeat widths 1–16,
queued/supplied bits, every input split and both EOF settings. Separate cases
check multi-call suffix resumption, exact map-end expansion, one-cell overshoot,
planning-credit failure, input-credit exhaustion and B3c dispatch. Seventeen new
unchanged-specification controls target formulas, debits, reservation order,
next-state values and unrelated-byte preservation.

The negative-test runner now requests `--multiple-errors 0` from the same
pinned checker: one reported contract failure is sufficient to reject a
mutant. This avoids extended searches for additional reports after a defect
has already been detected. It changes error reporting only; no source
contract, admitted input or production verifier input is changed.

The fresh whole-crate run passed **1,075 verified, 0 errors** with
`--no-cheating`. All **83 release tests** passed: 72 library tests, nine
primitive tests, the source trust-bypass check and the upstream comparison.
All **51 deliberate defects** were rejected after that unchanged whole-crate
positive: 17 new bit-action controls, 13 tree-count controls and 21 arithmetic
metering controls. The only later harness change limits additional error
reports; every production verifier input remains identical.

Validation for this continuation is recorded in
`evidence/brotli-b3c-m1-context-bits.json`. M1 and B3c remain incomplete.
Logical queue agreement does not prove byte-for-byte equality of every local
queue representation. The byte frame is a union of phase write regions;
minimal per-status write footprints and a complete ledger remain open.
Executor correspondence is conditioned on its explicit predicted-status check;
a universal no-mismatch theorem remains open.

At that checkpoint, the remaining M1 obligations were:

- Context phases 3 and 4 still enter the conservative driver: temporary-tree
  construction and installed-tree context symbols/direct values/run setup.
  That driver can traverse later planned phases internally without returning
  to B3c dispatch. Complete/failed W1 observations also retain it. Both
  conservative constants remain reachable.
- Prove complete plan/action state and frame refinement. Current executor
  checks compare consumption and status; they do not compare every successful
  symbol, serialized byte or source action.
- Audit and bind every planning table/cell read, logical transition and replay
  write to the approved exact ledger, including B3a internal table reads and
  local MTF simulation/coverage behavior.
- Add unchanged-specification controls for those complete relations and every
  remaining action path, then remove the conservative driver.

Whole-crate verification checks the contracts actually written in the source.
It does not close these explicitly missing contracts or substitute for the
remaining B3c refinement, confidentiality, resource, control-mapping and release
gates. B3d and B4 remain separate.

### Option A and installed-symbol continuation

The human selected separate nested reset/start transitions on 2026-11-03.
The named input-private initialization formulas now apply that rule to tree,
context-map/VAR_UINT8, installed-prefix, tree-group and B2 Ready starts. The
425-unit construction/reset charge is unchanged. The complete policy and
formula table are in `BROTLI_M1_TRANSITION_RULE_DECISION.md`.

Context phase 3 now plans the existing serialized temporary-tree action, and
phase 4 plans installed-tree symbols and their zero/direct/repeat setup
effects. MTF, coverage and handoff are separate existing W1 actions; their
planning no longer performs an uncharged local MTF transform. Complete, failed
and invalid subphase observations have prepaid terminal paths. Both previous
conservative reservation constants and the conservative driver are removed.
This removes a known coverage gap; it does not establish every replacement
formula or refinement obligation.

The installed-symbol model binds the first stopping record, malformed-record
failure, successful symbol identity, consumption, active physical queue bytes,
prefix state and actual bit/record/input read count. Both W1 execution and B3c
read-only replay refine that model, and a checked determinism lemma equates
their results and read counts. Initial block-length and context-symbol
executors use this relation before their result checks. Their prepaid
execution contracts retain exact debits and unchanged workspace on failed
reservation. The public/private result representations remain the approved
two fields; no runtime work-result field is added.

The code-description field contract now covers every terminal, zero-input,
partial-input, EOF and successful field action, including active physical queue
bytes. Determinism is checked through simple descriptions, auxiliary symbols,
repeats and pending spans. This is a field-action theorem; it does not yet
prove the complete serialized-tree planner.

Context-bit and context-tree-count execution now prove their predicted status
and consumption without assuming the status match. Valid serialized cursors
exclude the formerly unconstrained internal-error alternative. With execution
credit available, both executors prove exact input and work debits. The
input-private body-symbol helper also connects successful results to the same
installed-tree model and proves work of `2 * read_units + 17`: planning and
replay reads, one metadata visit, 15 serialized byte writes and one transition.
Its approved crate-private adapter signature and result remain unchanged.

Two source-derived defects were corrected. Initial block-length suffix
decoding reads two immutable range-table cells in planning and again in replay;
those four units are now charged. A malformed temporary-tree destination was
previously predicted as success. The planner now preserves W1's workspace
error, consumption and validation timing. Tests also cover malformed queue,
region, alphabet and code-description state, and exact/one-short terminal
reservation for an unknown initial block-length subphase.

Current remaining M1 obligations:

- Complete serialized-tree, block-count/suffix, distance/context-mode,
  tree-group, tail and terminal plan/action state and byte-frame refinement.
- Complete source-operation ledger binding, including internal B3a
  table/cell reads and malformed canonical-builder/install paths. Formula
  equality alone is insufficient.
- Complete outcome-specific frames and failure-path accounting, then bind
  every outstanding relation to unchanged-specification defect controls.

At that checkpoint, `process_complex_code_length` read `CODE_LENGTH_ORDER`;
`auxiliary_singleton` reads all 18 auxiliary lengths; and auxiliary canonical
lookup performed further length-table scans. `plan_serialized_tree` then
prepaid its bit read before calling the field decoder, without a complete
separate precharge for those nested table reads. The zero-input transition
after a completed auxiliary alphabet also invokes the 18-cell singleton scan.
The continuation below addresses these individual reads. The complete-ledger
claim remains denied.

The human explicitly selected **charge the 18 loads as table reads** on
2026-11-03. `read_aux_lengths`
loads the 18 auxiliary lengths from serialized parser state before later
indexed lookups. Counting those loads adds 18 table-read units for each full
load in planning or replay, beyond later indexed lookups. A rejected partial
load charges its actual inspected prefix. Treating the copy as state-loading
bookkeeping is unselected. This approval does not change ordinary scalar
fields, interfaces, storage or the 425-unit construction/reset charge. The
implementation is included in the saved-table continuation below.

M1, B3c and the supported-decoder release gate remain incomplete. B3d's
call-sequence and source-observation theorems, B4's quarantining caller and
profile, and the named independent human specification review remain separate
requirements. The whole-crate checker proves the written contracts; it cannot
close contracts that have not yet been written.

### Validation of the nested-transition/symbol checkpoint

The frozen production source passed the entire pinned `--no-cheating` check:
**1,138 verified, 0 errors**. All **87 release tests** passed: 76 library tests,
nine primitive tests, the source trust-bypass scan and the upstream comparison.
After that unchanged whole-crate positive, all **68 deliberate defects** across
11 metering/refinement suites were semantically rejected. Exact source,
validation, tool, artifact and log identities are recorded in
`evidence/brotli-b3c-m1-option-a.json`.

The negative-test classifier now also recognizes the checker's precondition
and nested-proof-requirement failure labels. For the repeat-guard-removal
control, an explicit existing loop/write bound is checked with the original
guard before checking the same obligation with the guard removed. Function
contracts and admitted inputs are unchanged. Earlier checker resource failures
are retained and are not counted as successful defect rejections.

The separately developed table-ledger continuation and its saved auxiliary
load charges were outside that checkpoint's frozen source. A regression there
demonstrated a valid private 704-symbol tree completing in byte chunks but
failing in one slice at the previous 2,000-action cap. The human explicitly
approved the 5,696-action correction on 2026-11-04 in
`BROTLI_M1_TREE_ACTION_BOUND_DECISION.md`.

### Saved tables, tree actions and approved F2 correction

The continuation prepays each auxiliary-table candidate/count/canonical cell
read, the singleton scan, simple-symbol comparisons and the `CODE_LENGTH_ORDER`
lookup. The field planner reserves its local replay's bit and table reads
before invoking the unchanged W1 field action. The initial saved-length load
charges both its pre-scan and local replay; rejected loads charge only the
inspected prefix. Each subsequent W1 descriptor reload contributes its 18
saved-length reads to the planned execution work. The zero-input auxiliary
completion has its own lookup and transition charges.

Canonical validation plans now retain the exact first failing length/space
prefix, or the full invalid/valid classification. Malformed builder plans
retain W1's error and consumed prefix. A successful tree plan proves its
reported planning work equals the actual planning debit and its consumption
stays within the supplied input. Block-tree and tree-group planners propagate
those properties and preserve the other budget counters. Loose mathematical
bounds on computed work totals do not change RequestBudget policy.

Both tree loops use the approved 5,696-action cap and prove their cap
fallthrough unreachable using a rank bounded by `8 * alphabet_limit + 63`.
They drain an already-pending span before advancing. Drainage proves the exact
builder cells written, preservation outside the span and initialized counter,
and unchanged workspace/decoder on inconsistent-position failure. Descriptor
stores preserve bytes outside their designated scalar fields; the drained
lengths survive serialization. These are named local relations, not a complete
serialized-tree plan/action theorem.

The pending-span correction exposed the false F1 classification of
`quickfox_repeated`. Candidate F2 was explicitly approved on 2026-11-04:
that fixture must decode to its pinned 176,128 bytes; `monkey` retains its
zero-output sticky rejection for this checkpoint, with the observed
`ContextMapRepeat` reason and native disagreement recorded as unresolved.
Strict advertised-tree coverage and the fixed `compression` fixture remain.

The pre-F2 frozen source passed **1,174 whole-crate checks, zero errors**, then
all **87 deliberate defects** across 13 suites were rejected. The final F2
source and additional debit/frame contracts require their own unchanged
whole-crate positive and defect controls. The final source passes **95 release
tests**: 84 library, nine primitive, one trust scan and one upstream comparison.
The fixture checks include all 57 input splits of `quickfox_repeated` and
one-byte, 31-byte, exact and excess output buffers across whole, one-byte and
seven-byte input chunks, with untouched output suffixes.

Complete serialized-tree state/outcome agreement, the full operation ledger,
remaining header/body failure relations, B3d, B4 and independent human review
remain open. M1 and the supported-decoder release gate remain incomplete.

### Final F2-source validation

The unchanged final source passed the entire pinned `--no-cheating` check: 1174 verified, zero errors. All 95 release tests passed, and all 118 deliberate defects across 19 suites were rejected after that positive. Exact source, harness, tool, compiled-artifact, approval and transcript identities are bound in `evidence/brotli-b3c-m1-f2.json`. The earlier resource-limited check is retained and is not counted as a semantic rejection. M1 and all later release gates remain incomplete.

### Block-count plan and execution continuation

Within the approved M1/E2 input-private boundary, the block-count planning
pre-scan and detailed plan now share an exact VAR_UINT8 read model. A checked
uniqueness lemma equates their work receipts before the adapter's runtime
consistency check. The plan binds the initial serialized queue/field phase,
the consumed prefix, the decoded VAR_UINT8 outcome and the existing execution
formula. Valid serialized read state guarantees a plan; the `kind >= 3`
handoff retains its existing zero-read, zero-consumption behavior.

The existing W1 block-count transition now exposes truncation's actual queue
and field-state effects instead of treating every failure as unconstrained.
Its value action is total under its existing preconditions and retains the
exact count, initial-length, next-kind and tree-start relations. Checked
determinism connects the planner to that transition. The outer dispatcher
preserves the relation, and B3c execution proves the predicted status,
consumption, exact input/work debits and preservation of the other counters
when the plan and input/work credits are valid. Insufficient execution work
retains the existing unchanged-workspace and unchanged-budget result.

Outcome-specific byte frames cover the cursor, count/initial-length update,
tree-start image, handoff and truncation terminal image. Bytes outside those
documented regions remain unchanged. The executor spells out its three
supported block-count status comparisons and the existing limited-input
NeedInput mapping; this exposes the unchanged behavior to the checker without
altering its runtime interface or result representation.

All **96 release tests** pass, including the new block-count matrix. It varies
kind, VAR_UINT8 phase, retained bits, input, finality, limited-input mapping and
exact/one-short execution credit, and compares both status and the complete
workspace image with W1. Six new unchanged-specification controls target the
pre-scan receipt, planned status/consumption, execution input debit,
limited-input terminal mapping and an unrelated padding write. Final
whole-crate verification and the expanded 20-suite/124-defect run are pending.

The guarantees above apply to successful plans from their stated serialized
read domain. They do not narrow executable inputs or finish malformed-state
classification, the complete source-operation ledger, other header/body
actions, B3d, B4 or independent human review. Fixed write/transition formulas
remain the approved formulas; this continuation does not claim a complete
witness of every source operation. K1 remains held for human review and its
prefix-module proof boundary is unchanged.

### Final block-count-source validation

The unchanged source passed 1176 whole-crate checks with zero errors. All 96 release tests passed, followed by 124 semantic defect rejections across 20 suites. Exact source, harness, approvals, tool, compiled-artifact and transcript hashes are bound in `evidence/brotli-b3c-m1-block-count.json`. Full M1 and decoder release obligations remain open, and K1 remains held for human review.

### Distance and malformed-context-count continuation

The existing six-bit distance-parameter transition now exposes the exact
decoded postfix, direct-distance count, alphabet size, retained cursor,
consumption and next phase. Its frames preserve every byte outside the queue,
the three parameter fields and the applicable outer/terminal image. A shared
read-cost model binds the pre-scan to the detailed plan, and determinism binds
the plan to W1 execution. Valid-plan execution proves the expected core result,
input/work debits and unchanged other counters, including the limited-input
mapping and failed-work-reservation identity.

A runtime comparison also exposed an admitted malformed-state discrepancy in
the later context-mode path. For a zero/oversized literal count or an
initialized count beyond it, W1 stores its InternalState terminal image. The
adapter previously returned the corresponding core error before that action,
leaving the B3b outer phase unchanged and spending zero work. The fix forecasts
the existing four-write/one-transition failure, reserves its five units and
invokes the unchanged W1 helper. Selected proofs cover that failure image,
zero consumption, exact debit, and unchanged workspace/budget when credit is
short. This is an internal admitted-state refinement issue, not a demonstrated
wire-stream acceptance bug.

The continuation passes **98 release tests** and a **732-check input-module
preflight**. Neither substitutes for its pending whole-crate positive. Twelve
new unchanged-specification controls cover distance receipt/status/consumption,
parameter stores, and malformed-count planning/latching/error mapping. They
remain gated on a fresh unchanged whole-crate positive, expanding the run to
22 suites and 136 defects.

The failed malformed-count comparison is retained as exact compressed output
with its original byte hash and diagnostic source. The existing field-parser
proof uses the repository's supported solver-context isolation at its existing
effort limit; no logical contract, admitted input or runtime budget is changed
by that checker configuration.

At that checkpoint normal context-mode agreement still needed an additional
success guarantee from the existing prefix writer contract. The human has now
approved K2 as recorded below. K1's separate hold remains active. The complete
operation ledger, remaining malformed-state paths, other phases, B3d, B4 and
independent human review remain open; M1 and the release gate remain incomplete.

### Approved K2 context-mode read continuation

The human explicitly approved K2 on 2026-11-09. Its decision is recorded in
`BROTLI_M1_CONTEXT_MODE_PROOF_BOUNDARY_DECISION.md`. The existing prefix writer
now guarantees success for the stated valid workspace/window and index below
256, under its unchanged requirements. Its executable body and signature are
unchanged. The canonical-code definitions and installer contract held under K1
are untouched.

Input-local proofs bind a pending context-mode action to the exact two-bit
read: the decoded value, next initialized count, retained cursor, consumed
input, status, and outcome-specific byte frame. The admitted proof domain is
`1 <= literal_count <= 256`, `initialized < literal_count`, with a valid
serialized queue. Existing executable inputs and all existing requirements
are unchanged. The previously added malformed-count guarantees remain intact.

The pre-scan and detailed plan have the same checked read cost. Checked
determinism connects a valid plan to W1 execution through the outer dispatcher.
The existing prepaid executor guarantees the corresponding result, exact
execution-work and input debits, unchanged other counters, limited-input
mapping, and complete workspace/budget preservation on failed execution
reservation. The work formulas remain `read_work + 11` for NeedInput,
`read_work + 16` for truncation, and `read_work + 15` for a value. Planning work
is charged separately, as already approved.

One runtime matrix compares all four mode values, empty input, retained one-
and two-bit queues, both EOF settings, first/interior/last initialized cells,
limited-input mapping, and exact/one-short execution work with W1's entire
workspace image. Ten new unchanged-contract controls target the K2 success
guarantee, planning receipts, outcomes, stored value/count, input debit and
limited-input mapping. They expand the combined distance/malformed-count/K2
validation to 24 suites and 146 deliberate defects.

The focused checks and all **99 release tests** pass. The fresh whole-crate
positive and subsequent deliberate-defect run are pending. The earlier
distance whole-crate attempt has no completion receipt and is retained as
interrupted; it is not counted as a positive. The initial K2 attempt was also
stopped before completion to correct a prefix-control extraction bug found by
static inspection; no mutant ran before a whole-crate positive.

The next whole-crate attempt completed the changed modules without reported
errors but was still spending most of its time in serial constant-data proofs.
It was stopped before completion. A global-isolation check did not eliminate
that bottleneck. Fourteen existing data functions now use the same proof-only
`spinoff_prover` annotation already used elsewhere in this crate, permitting
independent solver scheduling. Removing just those annotations reproduces the
entire original data source byte for byte. Their bodies, contracts and
constants, the pinned tools and the global resource limit are unchanged.
Final validation is restarted on the source containing these annotations;
earlier incomplete attempts are retained and are not positives.

These guarantees cover individual pending reads under the stated domain and
valid-plan execution, not the complete context-mode-list handoff, all malformed
queue states, an end-to-end source-operation ledger, or arbitrary sequences of
public calls. Remaining M1, B3c/B3d/B4 and independent-review obligations stay
open, and the supported-decoder release gate remains incomplete.

The broad block-count limited-input mutant exhausted the checker before producing a semantic failure. Its exact output and failed suite are retained and are not counted as rejections. Restricting that mutant to its named BlockCount phase produced the expected semantic failure under every unchanged original library contract. The final harness passed a fresh whole-crate positive and all 99 release tests; the repaired six-control suite then passed. Other passing controls retain their actual preceding positive, whose library hashes exactly equal the final source. No earlier failure is reclassified.

### Final distance and K2 source validation

The unchanged source passed **1,182 whole-crate checks with zero errors**. All **99 release tests** passed. Across **24 suites, 146 distinct deliberate defects** were rejected after their recorded unchanged-library whole-crate positives. Every rejection has a retained semantic checker failure without resource/compiler failure. Exact source, harness, approved K2 delta, tool, compiled-artifact and transcript identities are bound in `evidence/brotli-b3c-m1-k2.json`. K1 remains held. The named pending-read and distance/malformed-count guarantees do not complete M1 or the decoder release obligations.

### Context-mode handoff and saved-cursor failures

The K1 source review is recorded in `BROTLI_M1_K1_REVIEW.md`. It found no
contradiction between K1's proposed classification and the existing installer,
but it does not approve the boundary or prove the proposed guarantees. The
separate K3 proposal records the success guarantee needed from the existing
block-length helper for normal suffix agreement. Both exact human approval
requests remain pending at this source checkpoint. The prefix module is
unchanged from the preceding checked commit.

Independent M1 work now binds the completed context-mode-list transition to
the exact W1 map-start image, retained bytes, zero consumption and 18-unit
reservation. The map-start helper exposes its existing fourteen writes and
reset image; the handoff preserves all bytes outside those fields and the
outer-phase byte. Both nested reset transitions retain their already-approved
charges. The owner proves exact work debit on success and unchanged workspace
and budget on a short reservation, including when the saved queue is invalid
but this zero-input transition does not read it.

A runtime comparison found another admitted-state discrepancy: malformed
saved queues in block-count, distance and pending context-mode actions, and
malformed VAR_UINT8 encoding in block-count, bypassed W1's terminal image and
spent no work. All 66 exact/short-credit, EOF and error-image comparisons
failed before the correction. The actual output, source snapshot and hashes
are retained in `evidence/m1-finish-bad-cursor-before-fix*`.

The existing read-only pre-scan now exposes its precise rejection domain. On
those rejections the owner forecasts W1's existing four terminal writes and
one transition, reserves five units and executes the original W1 action.
Checked helper, dispatcher and execution contracts bind the error, zero
consumption, terminal image, input preservation and exact work debit. With
fewer than five units both workspace and budget stay unchanged and the result
is ResourceLimit. The regression passes after this correction. These are
internal admitted-state refinement defects, not demonstrated malformed-wire
acceptance defects.

All 101 release tests pass. Twelve new unchanged-contract controls cover the
handoff reset image, quota, consumption and frame, plus cursor error
classification, rejection forecasting, terminal execution and work debit.
The complete run expands to 26 suites and 158 defects, gated on a fresh
unchanged whole-crate positive. Full M1 remains incomplete: canonical/tree
replay, normal suffix agreement, the complete source-operation ledger and
remaining phase/failure relations and their controls still need closure.
B3c/B3d/B4 and independent human review remain separate release obligations.

### Approved K1/K3 proof continuation

The human explicitly approved K1 and K3 as written on 2026-11-09, superseding
the earlier holds noted at historical checkpoints above. K1 now opens exactly
the named existing mathematical definitions and CODE_SPACE and proves the
existing canonical installer's eligible-domain success/error classification.
Input-private induction equates that classification with M1 planning. The
original canonical-record correctness, frames, runtime guards, signature and
admitted inputs remain intact.

K3 strengthens only the existing block-length decoder's success guarantee.
Normal suffix action, planning, execution and owner relations now bind the
logical bit read, decoded length, consumption/status, next-state effects,
outcome-specific frames, exact combined work/input debits and short-reservation
identity. The mathematical owner relation carries a concrete plan witness;
it does not add a runtime field or change W1's interface or result type.

The final library passed **1,207 whole-crate checks with zero errors** and
`--no-cheating`. The first whole attempt's actual 1,205/one-error result remains
retained. An explicit ghost proof of the initial zero-iteration multiplication
identity resolved that loop-entry obligation. Final source and harness are
bound in `evidence/m1-k1-k3-attempt03-source-freeze.json`. All **33 deliberate defects across five affected suites** were rejected after
their recorded whole-crate positives on identical library bytes. Eight are new
K1/K3 controls and 25 cover the existing builder, table-read/canonical-planning
and suffix-formula behavior. Exact transcripts and ordering are recorded in
`evidence/brotli-b3c-m1-k1-k3-controls.json`. An older table-control marker stopped before
its mutation because it omitted K1's newly checked proof statement; its failed
output is retained and is not counted as a rejected defect.

The full runtime suite is **102 passed, one failed**. The failing
`m1_repeat_class_switch_survives_serialized_roundtrip` regression demonstrates
that the W1 codec loses previous repeat-length history at a class switch,
producing eight zeros instead of the expected three in an admitted decoder
field sequence. It is not yet a full compressed-stream/native witness or a
memory-safety violation. Candidate K4 in
`BROTLI_M1_REPEAT_STATE_DECISION.md` proposes the exact private-byte correction
and remains unapproved and unimplemented. F2's separate fixture policy stays
unchanged.

The source audit in `evidence/m1-loader-ledger-audit.json` also confirms extra
phase-validation indexed reads after the 18 auxiliary loads. For example, a
successful complex-prefix load reads 36 length cells; a complex-symbol load
with a valid singleton reads 54. These are source-derived counts, not a checked
complete work ledger. The executor reloads the serialized decoder each tree
iteration, so the current candidate's 18-unit copy allowance does not cover
those scans. Exact inspected-prefix/error accounting and full replay still
need proof and correction within the approved policy.

M1 remains incomplete. The remaining ledger, tree replay, malformed header/body
relations and full control closure, B3c/B3d/B4 and independent human review are
still open. This checkpoint has not been committed or pushed and does not
promote a supported decoder or mathematical safety completion claim.

### Approved K4 repeat-history correction

The human subsequently approved K4 as written. This supersedes the outstanding
K4 hold described at the historical K1/K3 checkpoint above. Byte 71 now retains
previous repeat history; tag six uses existing byte 174 for current repeat
length, rejecting values above 15 and deriving its existing suffix width.
Tag seven, fixed workspace, write counts/formulas, W1 interfaces, 5,696-action
caps, the 425-unit construction/reset charge and F2 expectations are unchanged.

Checked private images cover copied lengths and complete repeat progress.
Storage succeeds in the original valid workspace domain; correctly encoded
valid repeat states reload successfully. Queue rebasing uses the existing
serialized-queue relation, preserving logical bits and active bytes while
ignoring unused local padding. A checked lemma transfers the reloaded field
transition to the original state. The actual tree loop binds these guarantees
through its ghost repeat-image invariant; no persistent runtime field is added.

Final K4 evidence: **1,210 whole-crate checks, zero errors**, **104 passing
runtime tests**, and **21 semantic defect rejections in three affected suites**.
The original lost-history regression now produces three zeros as expected.
The broader matrix covers 2,048 history/resumption configurations, tag seven
and invalid current lengths. Existing F2 fixtures retain their approved results.
See `evidence/brotli-b3c-m1-k4.json`. Failed, interrupted and superseded runs
are retained and excluded from positive/rejection counts.

M1 remains incomplete. Candidate K5 in
`BROTLI_M1_LOADER_VALIDATION_METERING_DECISION.md` explicitly proposes the next
read-unit/private-receipt change and is not implemented. The current loader
validation scans still lack the complete metering/refinement closure. Complete
tree/action/ledger and malformed-state controls, later B3c/B3d/B4 work and
independent human review remain open; no supported decoder or complete
mathematical safety claim is made.

### Approved K5 loader table accounting

The human approved K5 as written on 2026-11-10, superseding the historical K5
hold above. Four saved simple-symbol words and every reached validation table
operand are now counted in planning and W1 reload forecasts. The new private
pre-scan flag distinguishes a valid full scan from an invalid final cell.
Early exits retain their exact prefixes; singleton validation still precedes
its later prefix-width check. Each forecast read is charged as performed, and
the original loader is invoked only after its complete read count is prepaid.
Existing mutation/reset formulas, W1 interfaces, ownership, workspace, runtime
caps and the 425-unit reset charge remain unchanged.

The source scan models are bound by checked loop/call counters, loader-exit
assertions and a successful-load phase-count guarantee. Initial and per-reload
adapter assertions bind the new receipts to those source-level logical units.
Final evidence: **1,235 whole-crate checks, zero errors**, **106 passing runtime
tests**, and **33 semantic defect rejections across three affected suites**.
See `evidence/brotli-b3c-m1-k5.json`. Failed and superseded checks are retained.

This completes K5's accounting change, not M1. Complete serialized-state/tree
replay and the remaining header/body, frame, source-ledger and control closure
still require work. Later decoder phases and independent human review remain
separate; no release gate or supported-format claim is promoted.


### General descriptor storage and reload agreement

The M1 continuation now checks the general serialized decoder image for every
stored description phase. Successful loads establish the image, and every
valid encoded image reloads to the expected phase, alphabet and active queued
state. The image retains the original loader guards, auxiliary-cell bounds,
rank alignment and alphabet metadata. Store guarantees are conditional on the
existing retained-history and builder context where those fields are needed;
no original executable requirement or root guarantee was narrowed.

The encoder proofs bind simple symbols, auxiliary progress, symbol/repeat
history, pending spans, completed descriptions and error tags. They preserve
the auxiliary snapshot across unrelated scalar writes. Successful span drains
produce the next stored image. The actual bounded tree loop now carries and
checks storage/reload agreement for all successfully stored phases, extending
the earlier repeat-only proof. Nonterminal field refinement transports across
reload; terminal states retain the same phase, alphabet and logical queue and
consume no input. Unused in-memory queue bytes are outside serialization.

Source counters check the existing symbol-array and auxiliary-array writes,
complex-code/progress helpers, each payload branch and the enclosing four
writes. Runtime behavior, W1 interfaces, budgets, workspace, 5,696-action caps,
the 425-unit reset charge and F2 fixture policy are unchanged.

Fresh verification passed **1,246 whole-crate checks, zero errors**, with
`--no-cheating`, followed by **66 distinct semantic defect rejections across
seven affected suites**. All **106 release runtime tests** pass. Twelve new
controls cover saved-field corruption and storage undercounts. The first
expanded tree preflight exhausted the verifier; explicit proof handoffs then
passed. One legacy control stopped at a text-selector audit because a new
proof condition repeated its phrase. Its output and old harness are retained;
only that selector was narrowed, a fresh whole-crate positive passed, and all
four controls in that suite were rerun successfully. The other 62 controls
retain their actual preceding positive on identical library bytes and identical
suite/checker bodies. No resource or harness failure is counted as a rejection.

Exact source, harness, tool and transcript identities are recorded in
`evidence/brotli-b3c-m1-full-codec.json`. This closes the named codec proof
checkpoint. Full plan/action tree replay, remaining failure/frame and source
ledgers, complete M1 control closure, B3c/B3d/B4 and independent human review
remain open. This is not a supported-decoder or mathematical-safety completion
claim.


### Open simple-install metering decision

A subsequent source audit identified additional symbol-table operands in
`install_simple_tree` and `simple_record_exec` that the current simple-install
reservation omits. The worked two-symbol/two-symbol-alphabet case performs
seven such reads in addition to the existing eleven reserved units. This is a
source-derived accounting finding, not a measured execution-counter result or
a completed M1 resource proof.

Candidate K6 in `BROTLI_M1_SIMPLE_INSTALL_METERING_DECISION.md` proposes the exact
additional read terms, keeping the algorithms, interfaces, storage, existing
write/reset formulas and other bounds unchanged. K6 is pending direct human
approval and is not implemented. The source audit is recorded in
`evidence/m1-simple-install-k6-source-audit.json`. Independent replay/state
proofs continue. The preceding published codec checkpoint established its
named storage/reload properties and did not establish the complete work ledger.


### Normal tree-planning replay checkpoint

The checked read-only tree planner now carries a replay prefix through its
continuing iterations and binds each successful `Complete` or `NeedInput`
result to a finite trace from the initial serialized decoder and exact builder
snapshot. The proof covers copied builder cells, field reads, the transient
auxiliary start and acknowledged spans. It binds the specification to the
actual result value returned by the planner. Original requirements and all
previous guarantees remain intact; executable algorithms, statuses, interfaces,
workspace and work formulas are unchanged.

The shared mathematical trace proof establishes equal outcomes, final logical
decoder/builder states and total parser/storage units for traces with matching
initial states. Installation is explicitly excluded from that unit fold and
remains a separate obligation. The canonical scan proof also establishes unique
validation outcomes and inspected-prefix lengths.

Fresh final-source verification passed **1,266 whole-crate checks with zero
errors**, `--no-cheating`. All **106 release runtime tests** pass. Four new
normal-planner defects and six existing tree-plan/debit/frame defects were
rejected semantically after that exact unchanged-source positive: **10**.
The first status-swap controls exhausted checker resources and are retained,
not counted. Binding the proof to the actual returned value preserved every
contract and runtime behavior; a fresh whole positive preceded all ten final
controls. Exact identities are in
`evidence/brotli-b3c-m1-tree-normal-state.json`.

This checkpoint does not establish failure-result traces, the complete
executor-to-planner refinement, the complete source-operation ledger or M1.
The executor-prefix prototype remains separate and unvalidated. K6 remains
pending direct human approval and its quota correction is unimplemented.
B3c/B3d/B4, independent human specification review and the supported-decoder
release gate remain open.
