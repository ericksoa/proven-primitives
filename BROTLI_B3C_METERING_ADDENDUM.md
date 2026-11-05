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
