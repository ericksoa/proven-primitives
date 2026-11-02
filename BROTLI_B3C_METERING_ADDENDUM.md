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
Current source-bound verification and runtime results are recorded in
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

Remaining M1 obligations:

- Context phases 0 through 6 still use the conservative driver: tree-count
  parsing, RLE-prefix selection, temporary-tree construction, context symbols,
  repeat suffixes/expansion and MTF enablement. Complete/failed W1 observations
  also retain that driver. Both conservative constants remain reachable.
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
