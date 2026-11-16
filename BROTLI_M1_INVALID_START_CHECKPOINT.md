# M1 malformed saved-tree start checkpoint

M1 remains incomplete. This proof continuation addresses the initial malformed
saved-tree states excluded by the preceding tree replay domain. Final
verification and controls are recorded in
`evidence/brotli-b3c-m1-tree-invalid-start.json`.

## Property and scope

Under the existing `m1_tree_has_decodable_start` predicate, a start is decodable
when an existing decoder image, serialized bit queue and valid active region
describe it. When that predicate is false on entry, the actual tree executor
must return `Failed`, consume zero input and leave the entire workspace
byte-for-byte unchanged. A returned read-only plan for the same malformed-start
domain must likewise report `Failed` and zero consumption. Planning can still
stop because its resource budget is exhausted.

The existing input-private planner and executor gain guarantees, proof blocks
and proof-loop invariants. A successful first reload supplies
an existing decoder image and queue as witnesses to the original predicate;
continuing loop iterations carry that fact. No existing executable signature,
requirement, admitted input or mathematical model changed. All prior guarantees
remain. This implements already-approved M1 refinement and frame obligations;
it introduces no architectural decision.

A small checked introduction lemma isolates that existing logical step from
the large executor proof. Its focused checks passed, followed by the focused
executor check. The earlier inline proof search was interrupted after this
equivalent isolated version passed; its source and raw output are retained
separately and count as neither a positive proof nor a semantic rejection.

The first whole run passed 1,305 checks, but one canonical-error mutant
exhausted verifier resources in the large loop. That run is retained and does
not count as complete control closure. Under approved E2, only the existing
canonical `Result`-to-status conversion is now extracted into a small
input-private helper. The original installer call, result and complete
guarantees remain directly at the original caller. The converter receives no
workspace and guarantees the exact existing conversion. The actual moved
mapping is the fault-control target; operations, order, effects and work
accounting are preserved. All pre-existing installer and root contracts remain.

Earlier broader extraction attempts obscured existing result facts, including
the completion-or-failure classification. Their failed and interrupted checks
are retained. The final extraction preserves the caller's original result
dataflow while providing a small checked fault site.

An earlier whole run also exposed a proof assertion in the existing distance-table
builder. That function is byte-identical to the signed base and passed its
unchanged focused check. It now uses the repository's existing per-function
solver isolation, with the same verifier, limits, body and contract.

For a fixed tree destination, the final canonical proof uses a checked theorem
that its status depends only on the current completed decoder, initialized
count and builder values.
Those facts connect the installer's original result to the actual loop action
without expanding final-builder validation inside the loop proof. The existing
definitions remain unchanged and are checked where used by the installer and
the theorem. All original root requirements and guarantees remain.

The prefix module, W1 interface, B3c budget ownership, workspace, K4 encoding,
F2 policy, K6 formulas, 5,696-action caps, 798/8,192 proof bounds, 425-unit reset
charge, dependencies and proof trust boundary are unchanged.

## Validation

The final whole-crate run passed **1,307 verified, zero errors**, using the
pinned tools, eight threads and `--no-cheating`. All **109 runtime tests** passed
on exactly the same source and validation inputs.

The receipt records the final pinned whole-crate `--no-cheating` check, unchanged
source and validation identities, runtime results and fourteen deliberate defects
run only after the exact-source whole positive. **All fourteen were rejected
semantically.** Four new defects try consuming
input or mutating a descriptor on malformed starts. Ten existing outcome and
normal-executor defects check the preceding trace guarantees. All mutation
sites preserve root contracts. Resource, compiler and interrupted failures do
not count as semantic rejections. Exact logs, drivers and source images are
retained with the receipt.

## Open obligations

This does not prove exact error-identity agreement between planning and
execution outside the decodable-start domain. Complete source-operation
accounting, other outcome-specific byte frames and full M1 control closure
remain open, as do remaining B3c/B3d/B4 work and independent human specification
review. The supported-decoder release gate remains incomplete.

Trusted components include the mathematical specifications and interpretation,
pinned Verus/Z3/vstd, Rust/LLVM and Apple build tools, and the machine and
operating environment. No complete M1, universal caller composition,
side-channel resistance, supported-decoder or source-to-binary correctness
claim follows.
