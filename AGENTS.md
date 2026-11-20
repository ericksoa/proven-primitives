# Proven Primitives contribution rules

This repository contains verified byte-processing primitives, their public
contracts, checked proofs, deliberate-defect controls, comparisons, benchmarks,
and release evidence. The same annotated Rust source is verified and compiled.

Every architectural decision requires direct human approval before
implementation. This includes dependencies and tools; public or private APIs;
state, storage, protocol, build, deployment, security, or trust-boundary changes;
and changes to the approved implementation approach. Approval to fix a defect,
continue a milestone, or publish does not authorize a new architectural choice.

The approved foundation is Rust/Cargo with the pinned Rust 1.99.1 and Verus
0.2026.10.18.7d82994 stack, caller-owned buffers, bounded loops, safe Rust, no
executable recursion or I/O in the verified core, strict format modes, and the
documented buffer effects. The approved dependencies and exact comparison
references are recorded in `Cargo.lock`, `evidence/dependency-review.json`, and
`REFERENCE_PROPOSAL.md`. Do not add, remove, replace, or upgrade them without
direct human approval.

The approved Base64 and LZ4 implementation work is documented in
`OPTIMIZATION_PROPOSAL.md`, `NEXT_ITERATIONS_PROPOSAL.md`,
`BATCHING_PROPOSAL.md`, and `VALIDATION_BATCH_PROPOSAL.md`. Preserve the public
contracts, complete validation before writes, error priority, safe Rust,
dependency set, and proof trust boundary.

The approved Brotli architecture is documented in `BROTLI_PROPOSAL.md`,
`BROTLI_STREAMING_PROPOSAL.md`, `BROTLI_B3_PROPOSAL.md`, and
`BROTLI_B4_PROFILE_PROPOSAL.md`. The B1 and B2 private components and R1 native
comparison are complete. B3 and B4 may proceed only within those exact approved
component, state, storage, resource, API, and trust boundaries. A completed
component is not a supported Brotli decoder; the support claim requires every
applicable profile obligation, checked evidence, independent specification
review, and a passing release gate.

The checked B3a front end now includes the exact fixed workspace/tree-record
layout, meta-block-header state machine, all simple code descriptions, the
complex auxiliary code-length alphabet, RFC repeat-coded final symbol lengths,
and canonical installation from the fixed builder region in
`src/brotli_prefix.rs` and `src/brotli_input.rs`. Preserve their source-linked
contracts and twenty-eight B3a defect controls. Tree-group orchestration,
context maps, literal/command/distance execution, and all later B3 work remain
incomplete; do not describe this slice as a decoder.

The human approved B3b Candidate W1 exactly as written in
`BROTLI_B3B_PROPOSAL.md` on 2026-10-26. Implement B3b only within W1's exact
private API, metadata encoding/order, 256-byte scalar-state layout,
initialized-range policy, source-linked atomic MTF, builder-bitmap RFC coverage,
B3a/B2 handoff, dependencies and proof trust boundary. Alternative R1 and the
other listed alternatives remain unapproved.

The human approved Candidate E1 exactly as written in
`BROTLI_B3B_W1_ADDENDUM.md` on 2026-10-26. Its serialized tag/error tables,
reset image, result fields, work formulas, authority rules and helper signatures
are now part of the approved B3b W1 boundary. Alternatives remain unapproved.

Candidate E2 in `BROTLI_B3B_W1_ADDENDUM.md` defines the narrow crate-private B2
snapshot adapter, input-local installed-tree decoder, and bounded local-helper
refactoring rule that E1 did not enumerate. The human approved Candidate E2
exactly as written on 2026-10-26. Implement only that adapter/decoder/rule;
other new cross-module APIs remain unapproved.

The checked B3b result is recorded in `BROTLI_B3B.md` and
`evidence/brotli-b3b.json`. It covers private compressed-header orchestration,
serialized state, context maps, inverse MTF, RFC coverage, tree groups,
streaming exhaustion/truncation, sticky terminal failures and the initial B2
Ready handoff. It is not a complete decoder or supported API. An
exhaustion-triggered call from the body decoder into the checked B2 adapter is
B3c work and must not be claimed as B3b integration.

The human approved Candidate C1 in `BROTLI_B3C_PROPOSAL.md` exactly as written
on 2026-10-26. Implement B3c only within its exact modules and crate-private
adapters, public private-field representations, 13,028-byte assignment, scalar
tags, immutable-data identities, terminal/call priority, four-unit escrow,
425-unit initialization charge, algorithms, proof controls, fixtures and staged
order. Alternatives C2 through C5 remain unapproved. B3d and B4 remain separate.

The human approved Candidate A1 in
`BROTLI_B3C_INTERNAL_BOUNDARY_ADDENDUM.md` exactly as written on 2026-10-27.
The additional checked crate-private scalar, raw-bit, LUT, dictionary-staging,
and body-state helpers are part of the B3c implementation boundary. Candidate
A2 remains unselected.

The human approved Candidate F1 in `BROTLI_B3C_FIXTURE_ADDENDUM.md` exactly as
written on 2026-10-27, then explicitly approved its Candidate F2 correction in
`BROTLI_B3C_FIXTURE_F2_DECISION.md` on 2026-11-04. Expect `quickfox_repeated`
to decode to its pinned bytes. Retain `monkey`'s zero-output sticky rejection
for this checkpoint, recording the observed `ContextMapRepeat` reason and the
unresolved native disagreement. Preserve strict tree coverage, its synthetic
rejections, and the fixed `compression` dictionary-transform stream.

The human approved Candidate M1 in `BROTLI_B3C_METERING_ADDENDUM.md` exactly as
written on 2026-10-29. Keep W1's exact private `step` interface unchanged;
retain budget ownership in the B3c adapter; charge read-only planning actions;
reserve each exact mutation formula before execution; and add exact plan/action
refinement plus unchanged-specification undercharge controls. Candidate M2
remains unselected.

The human selected Option A in `BROTLI_M1_TRANSITION_RULE_DECISION.md` on
2026-11-03: charge nested parser resets/starts separately from enclosing B3b
transitions. This applies to M1 compressed-header parsing; preserve C1's exact
425-unit construction/reset charge.

The human explicitly approved charging the 18 saved auxiliary code-length loads
as table reads on 2026-11-03, beyond later indexed lookups. Apply this to both
planning and replay; partial loads charge only the cells actually read. This
does not change ordinary scalar fields or the 425-unit construction/reset cost.

The human explicitly approved raising both private tree-action caps from 2,000
to 5,696 actions (`8 * 704 + 64`) on 2026-11-04, then proving the bound and
rerunning verification. This covers only `advance_serialized_tree` and
`plan_serialized_tree`; preserve the interfaces, RequestBudget policy,
workspace, parser representations and 425-unit construction/reset charge.

The human held Candidate K1 for review on 2026-11-04, then explicitly approved
K1 exactly as written in `BROTLI_M1_CANONICAL_PROOF_BOUNDARY_DECISION.md` on
2026-11-09 after the source review. Implement only its four named mathematical
definition visibility changes, CODE_SPACE visibility and installer
success/error contract. Preserve its signatures, executable algorithms,
admitted inputs, budgets, workspace and all existing record/frame guarantees.

The human explicitly approved Candidate K2 in
`BROTLI_M1_CONTEXT_MODE_PROOF_BOUNDARY_DECISION.md` on 2026-11-09. Strengthen
only `write_next_context_mode`'s success guarantee for the existing valid
window/workspace and initialized index below 256, then prove normal context-mode
agreement within the input-private boundary. Preserve its signature,
requirements, executable body, budgets and workspace. K1 was held at that
checkpoint and was subsequently explicitly approved as recorded above.

The assistant's source review in `BROTLI_M1_K1_REVIEW.md` is not the independent
human specification review required for release. The human explicitly approved
K3 as written in `BROTLI_M1_BLOCK_LENGTH_PROOF_BOUNDARY_DECISION.md` on
2026-11-09: add only the existing block-length decoder's conditional success
guarantee and its dependent M1 proofs. Preserve its signature, requirements,
executable body, tables, errors, budgets, workspace and the 425-unit reset
charge. Any other architectural decision still needs exact human approval.

The human explicitly approved Candidate K4 as written in
`BROTLI_M1_REPEAT_STATE_DECISION.md` on 2026-11-09. Preserve previous repeat
length in byte 71 and, for tag-six ComplexRepeat only, store/load current repeat
length in existing byte 174, with its existing invalid-state rejection and
extra-bit derivation. Update only that codec, its proof relations and tag-dependent
documentation. Keep tag-seven meanings, workspace size, write counts/work
formulas, W1 interfaces, 5,696-action bounds and the 425-unit reset charge.
Preserve the failed repeat-history evidence and separately approved F2 fixture
policy. Any F2 expectation change requires a separate direct human decision.

The human explicitly approved K5 as written in
`BROTLI_M1_LOADER_VALIDATION_METERING_DECISION.md` on 2026-11-10. Charge the
four saved simple-symbol entries and every loader validation table operand in
both planning and every W1 reload, preserving exact early exits. Extend only
`plan_saved_aux_load`'s private receipt to `(u64, bool)` as specified, and raise
only its proof-only initial planning bound from 740 to 798. Keep existing
mutation/serialization/reset formulas, W1 interfaces, B3c budget ownership,
workspace, 5,696-action caps and the 425-unit reset charge. K4 and the separate
F2 fixture policy remain fixed. Other architectural decisions still require
direct, exact human approval.

The general M1 descriptor storage/reload proof checkpoint is recorded in
`evidence/brotli-b3c-m1-full-codec.json`. It checks every stored phase's image,
valid-image reload agreement, successful pending-span storage and the actual
tree loop's reload/field binding, with the original admitted requirements.
This does not complete the plan/action tree trace, remaining source ledgers or
M1. It grants no additional architectural authority.

The human explicitly reviewed and approved Candidate K6 as written in
`BROTLI_M1_SIMPLE_INSTALL_METERING_DECISION.md` on 2026-11-10. Charge the
existing simple-installer symbol-table reads: seven total installation units
for a singleton, and `(3 + c) * A + 5 + c * (c + 1) / 2` otherwise. Preserve
helper signatures, algorithms, guard/error order, admitted inputs, W1 results,
B3c ownership, workspace, 5,696-action caps, 798/8,192 proof bounds, the
425-unit reset charge and F2. Add checked source counts and controls within
existing modules; no new runtime or cross-module proof API is approved. Other
architectural or quota changes still require exact direct human approval.

The normal M1 tree-planning trace checkpoint is recorded in
`evidence/brotli-b3c-m1-tree-normal-state.json`. It binds Complete/NeedInput
planner results and the initial builder image to checked replay traces. Its
mathematical unit fold excludes installation. Failure-result traces, full
executor refinement, remaining source ledgers and K6 remain open. No M1 or
supported-decoder completion claim or additional architectural authority follows.

The K6 implementation checkpoint is recorded in `evidence/brotli-b3c-m1-k6.json`.
Its exact simple-install reservations, private source operand counters and
prepayment term are checked. K6 is complete; it does not complete M1 or grant
another architectural or quota decision. Continue remaining approved M1 work.

The human approved K7 as written on 2026-11-12, then directed implementation
of the proposed K8 contracts on 2026-11-15 ("please progress and implement the
contracts"). K7's two contracts are documented in
`BROTLI_M1_INSTALL_RESULT_PROOF_BOUNDARY_DECISION.md`; K8's two supporting
contracts are in `BROTLI_M1_SUPPORTING_INSTALL_RESULT_DECISION.md`.
Implement only those exact existing result guarantees and their dependent
proofs/controls. Preserve every original signature, requirement, executable
body, admitted input, guard/error order, workspace and quota. No other
cross-module contract, visibility or architectural change is authorized.

The K7/K8 result-contract checkpoint is published in signed commit
`4084cbe3dbe51549a0a99e687de26f1ea06fe29e`
and recorded in `evidence/brotli-b3c-m1-k7-k8.json`: 1,300 whole-crate checks,
108 runtime tests and 29 semantic defect rejections. All four prefix bodies,
signatures and admitted requirements are unchanged. This completes those four
result-contract guarantees, not full M1 refinement, source ledgers or control
closure. Separate parser-failure control resource failures remain open.
The earlier K6 checkpoint is signed in history. Current source contains the
newer verified K7/K8 implementation; do not reset it to an earlier checkpoint.

The subsequent tree-outcome checkpoint is documented in
`BROTLI_M1_TREE_OUTCOME_CHECKPOINT.md` and
`evidence/brotli-b3c-m1-tree-total.json`. From a decodable saved tree start,
planning and execution now bind every result, including installation errors,
to the existing replay relation; the context-tree caller proves matching
consumption/status. The simple action extraction uses only the approved E2
input-private rule. Initial malformed encodings, complete source-operation
accounting, outcome-specific byte frames and full M1 control closure remain
open. This checkpoint grants no new architectural authority and does not
complete M1, the decoder or independent human specification review.

The malformed saved-tree start continuation is documented in
`BROTLI_M1_INVALID_START_CHECKPOINT.md` and
`evidence/brotli-b3c-m1-tree-invalid-start.json`. Under the existing predicate's
complement, the executor must fail with zero consumed input and the entire
workspace unchanged; every returned plan must likewise fail with zero
consumption. The continuation adds proof guarantees, checked logical steps and
proof invariants, plus the E2 input-private extraction of only the existing
canonical result-to-status conversion. The original installer and its result
remain at the original caller. Original requirements, signatures, models,
operations and work accounting remain. Exact error identity
outside the decodable-start domain and the other remaining M1 obligations are
still open. This grants no additional architectural authority.

The malformed-start checkpoint passed 1,307 whole-crate checks with zero
errors, 109 runtime tests and 14 semantic defect controls on the exact same
source. It does not complete the remaining M1 ledgers, frames or control
closure.

Keep the checked canonical current-state status theorem and its input-private
proof handoff when maintaining this checkpoint. The tree root uses the
existing builder definitions through checked helper contracts; the original
definitions and installer bodies remain intact. The distance-table proof uses
the existing per-function solver-isolation annotation with unchanged body,
contract and limits. These are proof-engineering details, not additional
architectural authority or M1 completion.

The context-tree error-agreement continuation is recorded in
`BROTLI_M1_TREE_ERROR_AGREEMENT_CHECKPOINT.md` and
`evidence/brotli-b3c-m1-tree-error-agreement.json`. Under valid workspace shape,
saved-description load failures are the existing InternalState, and malformed
tree starts produce equal zero-consumption/internal-error plan and execution
results. The context-tree adapter's mismatch branch is proved unreachable for
all its admitted saved states after successful planning/reservation. All
executable statements, requirements, models, policies and prior guarantees
remain. Final exact-source checks passed 1,307/0, 109 runtime tests and 19
semantic controls. Full M1 ledgers, byte frames, block/group composition and
later release obligations remain open; no new architectural authority follows.

P1's local standard-library evidence pipeline in `tools/pipeline.py` is
approved. It records strict schemas, frozen closures, proof outcomes, coverage,
and fail-closed release decisions. It may not weaken contracts, narrow admitted
inputs, introduce assumptions or admitted proofs, change applicability, or
accept tests and benchmarks in place of proofs.

Report proof status precisely. A test pass is not a proof. A safety proof does
not establish format correctness, streaming correctness, arbitrary caller
composition, side-channel behavior, service availability, or source-to-binary
correctness unless the named checked contract covers it. Public claims must name
the proved property, admitted domain, assumptions, trusted components, and any
remaining gaps.

Proof checks must reject `assume`, `admit`, unchecked or external
implementation bodies, new axioms, and weakened root bindings. Run an unchanged
whole-crate positive control before deliberate-defect controls. Preserve actual
checker outputs and distinguish checked proofs, demonstrated violations, and
unresolved obligations.

Use the installed Apple Command Line Tools 27.0 through a per-command
`DEVELOPER_DIR=/Library/Developer/CommandLineTools` setting for native builds.
Do not change the global developer selection. The project license is Apache-2.0.

The human explicitly approved Approach R exactly as written in
`BROTLI_M1_SOURCE_RECEIPT_BOUNDARY_DECISION.md` on 2026-11-17. Within that frozen
M1 helper scope, implement actual per-invocation source-count receipts through
`(T, Ghost<nat>)` returns, preserving ordinary results as the first component.
Corresponding private compiled return and direct-caller changes are approved;
public Brotli and W1 interfaces remain unchanged. Open only the named derived
`m1_canonical_nonzero_index_sum` as specified. Preserve arguments, requirements,
old guarantees, algorithms, operation/guard/error order, unit policy, budgets,
workspace, dependencies, F2 and proof trust. Receipts must originate in reached
counters/traces at every return, including partial input/errors; no reservation-
formula substitutes. Approach S is unselected. Any boundary or policy outside
that exact decision still needs direct human approval. The named M1 compressed-header source-receipt and plan/action refinement checkpoint is recorded in `BROTLI_M1_SOURCE_RECEIPTS_CHECKPOINT.md` and `evidence/brotli-b3c-m1-source-receipts.json`. Its completion is limited to the exact admitted domains and frozen source in that receipt; B3c/B3d/B4, the F2 native disagreement, independent human specification review and decoder/release gates remain separate. No new architectural authority follows.


The human explicitly approved I2 as written in
`BROTLI_B3C_CONSTRUCTOR_PROOF_BOUNDARY_DECISION.md` on 2026-11-19. Add only the
three named public closed RequestBudget observations (`limits_view`,
`remaining_work`, `remaining_initializations`), their existing-constructor
success guarantees, and the complete public Brotli constructor guarantees.
I1 remains unselected. Preserve all previous requirements/guarantees,
executable statements, error priority, workspace, 425-unit charge, dependencies
and proof trust. No other public observer or visibility change is approved.
The named constructor checkpoint is recorded in
`BROTLI_B3C_CONSTRUCTOR_CHECKPOINT.md` and
`evidence/brotli-b3c-constructor-i2.json`: 1397 whole-crate checks with zero
errors, 116 runtime tests and six semantic constructor defect rejections on
the same frozen source. A proof-only solver-isolation annotation on the
unchanged distance-symbol helper preserves its original allowance of 90;
the preceding resource-failed whole attempt is retained separately. This
completes only the constructor checkpoint. Remaining B3c work, B3d/B4, F2's
native disagreement, independent human specification review and decoder/release
obligations remain open. No additional architectural authority follows.


The broader B3c atomic-emission checkpoint is recorded in
`BROTLI_B3C_ATOMIC_EMISSION_CHECKPOINT.md` and
`evidence/brotli-b3c-atomic-emission.json`. Within C1's already-approved atomic
output/state-effect scope, the existing owner-private `emit_byte` and
`emit_uncompressed_byte` contracts now bind success to the complete serialized
workspace image and every error to an unchanged workspace/budget/output.
Their complete bodies, signatures, original requirements and guarantees remain;
there is no new public or cross-module proof API. The source retains the exact
8-work/1-output/optional-1-input debit and the 425-unit initialization policy.
The same-source gate checked 1397 whole-crate obligations with zero errors,
116 runtime tests and 44 semantic rejections across the prior 28 B3c, six
constructor and ten new emission cases. Earlier partial resource failures are
retained and are not positive/control evidence. One proof-only solver-isolation
annotation uses the existing tool without changing any production allowance.
The legacy test-only selector repair and matched temporary emission/terminal
solver allowances are recorded separately; all original assertions/classifiers
remain. Source billing is still open: the static audit finds 24 byte writes
against the eight-unit emission debit. E3 is pending direct human approval in
`BROTLI_B3C_EMISSION_WRITE_METERING_DECISION.md`; do not implement its five
return-type/24-unit changes without that approval. The actual B2 caller's
retry-bypass fault is accepted by its current weak contract, independently of
the checked rejection helper; this is a recorded proof gap, not a passing
negative control.
This is a local exact-effect/error-frame checkpoint, not complete B3c. Byte
origin, complete error classification/progress, actual B2 saved-state handoff,
phase/stream composition, later source ledgers, B3d/B4, F2's native disagreement,
independent human specification review and supported-decoder/release gates
remain open. No additional architectural decision or approval follows.


The subsequent C1 permanent-outcome/budget-validation checkpoint is recorded in
`BROTLI_B3C_B2_PERMANENT_CHECKPOINT.md` and
`evidence/brotli-b3c-b2-permanent.json`. The actual body-switch adapter now
promises zero consumption and a permanent `Failed(_)` outcome when requested
kind < 3, stored switch tag is Ready/zero, that kind's declared type count is
at most one and its remaining count is zero. Its existing loader's success
contract binds type counts, remaining counts and Ready phase to the existing
state views. `RequestBudget::new` now succeeds exactly for window limit 10..24;
all other zero quotas remain accepted. No function/type/visibility/interface,
argument, requirement, executable statement or resource policy changed.
The actual unfiltered whole positive checked 1,397 obligations with zero errors,
then six strict body-fault rejections ran on identical core source. Those source
bytes were promoted unchanged and passed 116 runtime tests; the explicit
content/location qualification and complete source/tool/log hashes are retained.
The preceding 44-case byte-effect gate remains historical and is not counted
as rerun on this snapshot. Three existing-tool isolation annotations preserve
all original allowances, including the unchanged M1 initial-length helper.
This closes only that conditional outcome and window-validation completeness.
Full B2 restore/store/call/snapshot and public-stream composition remain open.
E3 remains pending direct human approval and is unimplemented. The 24-write /
eight-work source finding is still open; its five-producer/33-caller graph is
unchanged as recorded in the new scope qualification. No E3 or other
architectural approval follows from these proofs, signatures or tests. Preserve
F2, B3d/B4, independent human specification review and release boundaries.


The human explicitly approved E3 as written in
`BROTLI_B3C_EMISSION_WRITE_METERING_DECISION.md` on 2026-11-20 ("E3 approved,
please continue"). Extend reached byte-store receipts through exactly the five
named existing producers using `(T, Ghost<nat>)`, normal result first, and only
the qualified 33 direct caller sites to propagate/discard them. Add the private
`B3C_EMISSION_WRITE_WORK: u64 = 24`, correct only the emission write debit,
success effects and minimum-work/output-block thresholds from eight to 24,
and prove the debit against reached counters/child receipts on every return.
Preserve the uncompressed wrapper's existing >=8 entry requirement and all
other original arguments/requirements/functional guarantees. Internal compiled
return changes are approved only in that exact graph. Preserve public/W1 APIs,
algorithms, ordinary error/guard order, workspace, 425-unit initialization,
four-unit escrow, all other formulas, dependencies, F2 and proof trust.
Other source-read/caller costs and B3c/B3d/B4 remain separate; another boundary,
representation, unit classification or policy choice returns to the human.


The approved E3 write-only checkpoint is recorded in
`BROTLI_B3C_E3_CHECKPOINT.md` and `evidence/brotli-b3c-e3.json`.
Exactly five producers carry reached byte-store `(T, Ghost<nat>)` receipts;
ordinary results stay on component zero and the qualified 33 caller sites are
adapted. Raw stores count 1/4/8 on success and zero on address errors; shared
and uncompressed emission count 24 on success and zero on error. Counts are
constructed only from reached primitive increments and child receipts. The
write debit/minimum is the approved private constant 24 and is bound to the
returned count, with checked source-local receipt/prepayment assertions.
The uncompressed wrapper's original >=8 entry requirement remains unchanged.
The exact-source gate passed 1398 whole-crate checks with zero errors,
118 runtime tests and 56 strict semantic rejections across four complete
suites. Static origin/ordering guards and earlier failed/interrupted results
are separate; no tool/resource/syntax failure is a rejection. Native checker
effort is matched on positive/negative copies; production allowances remain.
Arguments, old functional requirements/guarantees, ordinary algorithms and
error/guard order remain, except for approved work effects and internal return
types. Public/W1 interfaces, workspace, 425 reset/init, four escrow, other
formulas, dependencies, F2 and mathematical visibility remain unchanged.
The earlier eight-unit mismatch is corrected only for this write component.
Read prepayment, additional caller writes/transitions, remaining body/B2/stream
composition, B3d/B4, native disagreements, independent human specification
review and supported-decoder/release gates remain open. Another architectural,
API/boundary, representation or unit-policy decision requires direct human
approval; E3 grants no authority outside its exact scope.
