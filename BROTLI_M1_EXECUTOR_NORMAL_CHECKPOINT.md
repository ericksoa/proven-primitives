# M1 executor normal-result checkpoint

Status: this verified normal-executor candidate is incorporated into the
current working source together with the later K7/K8 result contracts. Its
original exact-source evidence is retained. The K6 checkpoint is signed in
history, and the current verified source and evidence are being published in
the following signed commit. M1 and the supported-decoder release gate remain
incomplete.

## Checked result

The actual bounded serialized-tree executor now carries a finite replay prefix
through every continuing iteration. Its returned `Complete` and `NeedInput`
results have checked traces from the initial serialized decoder and builder
snapshot, including field actions, the transient auxiliary start, acknowledged
spans and actual consumption/status. An additional checked theorem establishes
that results with traces from the same serialized start agree.

The existing canonical-install branch is isolated in an input-private helper
under the human-approved E2 rule. Its read/storage calls and their order remain
unchanged. A private queue-write wrapper invokes the existing writer once and
exposes its existing preservation guarantees without expanding the entire byte
frame in the executor loop. Explicit initial-snapshot and arithmetic facts
supply the proof handoffs. Original root requirements and guarantees remain.

The final candidate preserves the complete planner, existing final-state and
parser/storage-unit trace theorem, K6 formula and prefix source, W1 interfaces,
B3c budget ownership, workspace, K4 encoding, F2 policy, 5,696-action caps,
798/8,192 proof bounds and the 425-unit reset charge. The existing trace-unit
fold still excludes installation; this checkpoint does not establish the
complete source-operation ledger.

## Evidence

- Final whole-crate verification: **1,295 verified, zero errors**, pinned tools,
  eight threads and `--no-cheating`, with unchanged source and tests.
- Runtime validation: **107 passed**, comprising 96 library tests, nine
  primitive tests, the trust-bypass scan and upstream comparison.
- Deliberate defects: **26 semantic rejections** after that exact positive:
  four new executor result defects, four existing cap/drain defects, six
  planning/frame defects and twelve K6 accounting defects. No tool/resource
  failure is counted as a rejection.
- The first combined whole run retained two failing proof obligations: a bit
  multiplication identity and the existing loader's index-square bounds. A
  preliminary corrected source passed 1,294 checks. The final source makes both
  arithmetic bounds explicit and passed the fresh 1,295-check run. Earlier
  failures and source images are retained separately.

Receipt: `evidence/brotli-b3c-m1-executor-normal.json`.

Reviewable patch: `evidence/m1-executor-normal-candidate.patch`. Its base is the
exact staged/working K6 source identified in the receipt. The patch passes
`git apply --check` on that source. Frozen source archives, complete checker
outputs, runtime logs, raw controls and drivers are retained with the receipt.
New control transcripts are isolated in their own checkpoint directory so the
staged K6 evidence is preserved.

## Remaining boundary

Full failure-result traces and unconditional planner/executor agreement remain
open. K7 and the two supporting K8 result contracts were subsequently approved,
implemented in the working source and verified. Their evidence is recorded in
`evidence/brotli-b3c-m1-k7-k8.json`. The independent broader parser-failure
control experiments retain resource-exhaustion failures; those are not counted
as semantic rejections or full M1 control closure.

Remaining source-operation/outcome-specific frame ledgers and full M1 control
closure, B3c/B3d/B4 and independent human specification review are also open.
Trusted components include the mathematical specifications and interpretation,
pinned Verus/Z3/vstd, Rust/LLVM and Apple build tools, and the machine/operating
environment. No complete decoder, complete mathematical safety or
source-to-binary correctness claim is made.
