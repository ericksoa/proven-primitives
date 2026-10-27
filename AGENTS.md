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
