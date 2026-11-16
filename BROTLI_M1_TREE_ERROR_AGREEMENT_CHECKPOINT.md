# M1 context-tree result agreement checkpoint

Status: checked source passed 1,307 whole-crate checks with zero errors, 109
runtime tests and nineteen semantic defect rejections. M1 remains incomplete.

The saved-description loader now states its existing failure classification:
with a valid B3b workspace shape, a failed load returns `InternalState`. The
serialized-tree planner and executor propagate that exact error for starts
outside the existing decodable-start predicate. Together with the preceding
atomic-rejection proof, every returned plan and actual tree execution in that
domain report zero consumption and `Failed(InternalState)`.

For decodable starts, the existing checked traces still establish agreement.
The context-tree adapter now checks both cases and proves that planning and
actual execution have equal consumption and status whenever planning and
reservation succeed. Its defensive mismatch branch is unreachable under its
original requirements, including valid budget, workspace and decoder state,
outer context phase and context-tree subphase. The runtime branch remains.
Planning or reservation failure retains the original resource/error paths.

Only existing input-private result guarantees and ghost proofs
changed. All executable statements, signatures, requirements, previous
guarantees and mathematical definitions remain. The source audit compares the
loader and planner bodies byte for byte, and the executor and caller bodies
after erasing proof blocks. A checked equality binds the actual simple result's
status directly to the helper's returned status before trace construction.
W1 interfaces, B3c budget ownership, workspace, K4 encoding,
F2 policy, K6 formulas, 5,696-action caps, 798/8,192 proof bounds, 425-unit reset
charge, dependencies and proof trust boundary are preserved. No additional
architectural decision is introduced.

The final receipt is `evidence/brotli-b3c-m1-tree-error-agreement.json`. It binds
the whole-crate `--no-cheating` run, runtime validation and nineteen deliberate
defects to the exact source and validation identities. Five new faults change
existing error mappings or flag equal internal errors as a mismatch. Fourteen
existing malformed-start, outcome and trace faults remain included. All
mutation sites preserve their complete root contracts. Compiler, resource and
interrupted failures do not count as semantic rejections.

The first whole run passed 1,307 checks and all 109 runtime tests. Seventeen
controls produced semantic rejections, but an existing simple false-input-
exhaustion mutant reached the verifier's loop resource limit; the last
canonical control did not run. That incomplete control run and its exact
source are retained. The direct returned-status equality preserves every
contract and executable statement, and the final gate reruns the whole
positive and all nineteen controls on the resulting source.

This does not prove exact error identity for workspace shapes outside the
adapter's admitted domain, complete source-operation accounting, other
outcome-specific byte frames or full M1 control closure. Remaining block/tree
group composition, B3c/B3d/B4 work and independent human specification review
remain open. No supported-decoder, universal caller-composition, side-channel
resistance or source-to-binary correctness claim is made. Trusted components
include the specifications and interpretation, pinned Verus/Z3/vstd, Rust/LLVM
and Apple build tools, and the machine and operating environment.
