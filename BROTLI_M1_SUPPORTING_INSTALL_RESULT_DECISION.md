# M1 supporting installation-result contracts

Status: Candidate K8 approved for implementation by the human on 2026-11-15.
The direct instruction was "please progress and implement the contracts",
referring to the two concrete K8 contracts below. The approved contracts are implemented and verified.

## Evidence and gap

The human approved K7 on 2026-11-12. Its canonical-metadata result contract
checks with the unchanged executable body. The simple installer checks its
other branches but fails K7's new success obligation exactly at
`return TreeMetadata::single(...)`, because that constructor's existing
contract describes only successful results. The actual retained output is
`evidence/m1-k7-simple-installer-preflight-01.log` (five verified obligations,
one unresolved). This is a missing supporting contract, not a demonstrated
runtime failure. The K7 review missed that dependency; K7 approval does not
authorize changing this third contract.

The canonical path has a second source-derived contract gap. K1 proves
canonical length classification for a valid tree destination. For an invalid
tree index it guarantees unchanged workspace, but does not state the exact
existing `InvalidTree` error. Full M1 error-path agreement needs that result
without modifying or skipping the existing call. This second gap is a source
review finding, not a completed failing proof or runtime regression.

## Candidate K8: two supporting result guarantees only

1. Strengthen only the existing crate-private
   `TreeMetadata::single(region, symbols, symbol)` result contract. For every
   admitted input, guarantee its exact existing result:
   - `Err(WorkspaceError::InvalidSymbol)` when `symbols == 0`,
     `symbols > tree_region_symbols(region)`, or `symbol >= symbols`;
   - otherwise `Ok(TreeMetadata { symbols, storage:
     TreeStorageState::Single { symbol } })`.
   Retain every existing guarantee and requirement.
2. Strengthen only the existing crate-private
   `install_builder_canonical_tree` contract outside K1's valid-tree domain.
   Under its existing `old(meta).valid_for(region)` requirement, when
   `window_bytes <= 16_777_216`, the workspace has at least
   `window_bytes + FIXED_SCRATCH_BYTES` bytes, and
   `tree >= tree_region_count(region)`, guarantee the existing exact
   `Err(WorkspaceError::InvalidTree)` result, unchanged workspace and unchanged
   metadata. The existing tree-index guard precedes metadata-storage and
   code-length validation; preserve that order. Retain K1's full valid-tree
   success/error classification and every previous frame/record guarantee.
3. Add only checked ghost assertions/lemmas/invariants and input-private M1
   proofs/controls needed to use these guarantees and finish K7's obligation.
   No assumption, admitted proof, narrowed admitted domain or executable
   change is permitted.

These are two additional proof-contract changes across the existing
input/prefix boundary. No other cross-module contract or visibility change is
approved by this candidate. Preserve all executable bodies, signatures,
requirements, algorithms, guard/error order, admitted inputs, dependencies,
tools, W1 interfaces/results, B3c ownership, workspace, K4 encoding, F2 policy,
K6 formulas, 5,696-action caps, 798/8,192 proof bounds and the 425-unit reset
charge. No new executable helper is introduced.

## Validation and limits

Check both guarantees with the pinned tools and `--no-cheating`, retain the
failed K7 output, and complete K7 without excluding the singleton case. Rerun
whole-crate checks before unchanged-specification deliberate defects and run
affected runtime and exact/short-budget comparisons. Tool/resource failures
are not semantic rejections. This decision does not complete M1, authorize
another architectural decision or replace independent human release review.

## Human decision

The human directed implementation of these proposed contracts on 2026-11-15.
K8 is approved within exactly the two named contracts and their dependent
proofs/controls. This supplies no authority for another architectural change.

## Implementation evidence

Both K8 guarantees and both dependent K7 guarantees are implemented in
`src/brotli_prefix.rs`. The four affected signatures, requirements, executable
and ghost body bytes are unchanged; only their result contracts are stronger.
The simple installer now discharges all six selected obligations, including its
previously unresolved singleton case. Metadata checks passed four obligations
and the canonical installer passed ten.

The final working source passed 1,300 whole-crate proof checks with zero errors,
108 runtime tests and 29 semantic defect rejections after the exact unchanged
whole positive. All six new result-contract defects were rejected. The controls
ran on a byte-verified snapshot to preserve earlier K6 evidence. Exact sources,
transcripts, tools, audits and retained historical failures are bound in
`evidence/brotli-b3c-m1-k7-k8.json`.

The configured signing key was unlocked through the existing macOS Keychain
setup. The verified K6 checkpoint is signed in commit `fde0c8ba4b972b6198bd116ee039e3980352f9f0`; the verified
K7/K8 implementation and its evidence are being published in the following
signed commit. M1 and the later decoder/release obligations remain incomplete.
