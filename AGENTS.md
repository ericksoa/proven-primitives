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
