# M1 tree outcome agreement checkpoint

M1 remains incomplete. This checkpoint closes serialized-tree result agreement
from a decodable saved start, including workspace and installation errors.
It does not establish the complete source-operation ledger or a supported
Brotli decoder.

## Checked result and preserved boundary

The read-only planner and the actual serialized-tree executor now bind every
returned tree outcome to the existing finite replay relation when the initial
saved decoder is decodable. This includes simple destination rejection,
canonical destination error priority, invalid canonical lengths, malformed
in-progress builder results, truncation, normal completion and input exhaustion.
The context-tree caller proves equal consumption and status for those outcomes,
so its defensive mismatch branch is unreachable under that condition.

The existing simple installation and status mapping were extracted into one
input-private helper under the human-approved E2 rule. It calls the same
installer once, with unchanged effects and order. The existing canonical action
uses the approved K1/K7/K8 result contracts. Three local error aliases retain
their original values and carry checked equality facts into the planner loop.
An explicit comparison of the 23 equal scalar status pairs preserves the
original consumed-first short-circuit comparison; its logical equivalence is
checked unconditionally.

Original executable signatures, requirements and prior guarantees are
preserved. The prefix module is byte-identical to signed baseline
`4084cbe3dbe51549a0a99e687de26f1ea06fe29e`. W1 interfaces, B3c budget ownership,
workspace, K4 encoding, F2 policy, K6 formulas, 5,696-action caps, 798/8,192 proof
bounds and the 425-unit construction/reset charge are unchanged. The source
audit expands the simple helper extraction before comparing named executable
calls; it is source-derived evidence, not binary-equivalence verification.

## Validation

The final whole-crate check passed **1,304 verified, zero errors**, using the
pinned tools, eight threads and `--no-cheating`. All **109 runtime tests** passed.
The new runtime regression exercises 56 configurations across all six tree
regions, including simultaneous destination errors and invalid code lengths,
checks read-only planning and exact result agreement, and checks the whole
workspace is preserved on completed-state rejection.

All **22 deliberate defects** were rejected semantically after the exact-source
whole positive: six new installation-outcome controls and sixteen affected
result, plan/debit/frame and normal-executor controls. Results are recorded in
`evidence/brotli-b3c-m1-tree-total.json`. The six new controls mutate actual
simple/canonical error mappings, the planner's three returned error aliases,
and the caller's error comparison. All selected mutation sites preserve root
contracts. Three alias faults are rejected by exact computed contradictions
(`expression simplifies to false` at the checked `compute_only` assertion),
before SMT. These are semantic proof failures; tool errors, resource exhaustion
and interrupted checks are excluded. The classifier accepts that diagnostic
only for those three named cases and still rejects resource/tool failures.

Earlier attempts are retained separately. Attempts 01–03 include resource-only
mutant failures. Attempt 04 was interrupted and has no positive result.
Attempt 05 passed 1,304 checks, then its older harness misclassified a genuine
computed contradiction. Attempt 06 reruns the whole positive and all final
controls with the corrected classifier. None of the incomplete earlier
control runs count toward the final checkpoint.

## Open obligations

Initial malformed encodings outside the decodable-start predicate, complete
source-operation accounting, outcome-specific byte frames and full M1 control
closure remain open. Remaining B3c/B3d/B4 work and independent human
specification review also remain open. The existing mathematical trace unit
fold excludes installation; outcome agreement alone does not close that gap.

Trusted components include the mathematical specifications and interpretation,
pinned Verus/Z3/vstd, Rust/LLVM and Apple build tools, and the machine and
operating environment. No complete M1, universal caller composition,
side-channel resistance, supported-decoder or source-to-binary correctness
claim follows from this checkpoint.
