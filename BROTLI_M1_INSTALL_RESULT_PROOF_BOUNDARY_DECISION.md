# M1 installation-result proof boundary

Status: Candidate K7 approved as written by the human on 2026-11-12.
The K7 contracts are implemented and verified, including the singleton case,
using the separately approved K8 supporting contracts.

## Concrete gap

The approved K6 installation accounting and the normal executor trace can be
checked with the current prefix contracts. Full planner/executor agreement also
needs to exclude an unexplained installation error when the destination and
parsed description are valid.

`TreeMetadata::canonical` currently guarantees only properties of an `Ok`
result. Its existing body returns `InvalidSymbol` exactly when `symbols == 0`
or `symbols > tree_region_symbols(region)`, and otherwise returns the canonical
metadata with zero initialized records. Its contract does not yet state that
success/error classification.

`install_simple_tree` likewise describes successful metadata/records and keeps
storage unchanged on an error. Its contract does not yet guarantee success for
a valid decoded simple description at a valid destination. K6 deliberately
preserved that contract. Its existing guard order rejects an invalid alphabet
or tree destination as `InvalidSymbol` before examining symbol-table entries.

Without the corresponding guarantees, a caller proof must allow those helpers
to fail even when the actual existing implementation succeeds. Normal-result
trace binding therefore does not establish a complete no-mismatch theorem.
These are missing proof contracts, not evidence of a new runtime defect.

## Candidate K7: strengthen only the two existing result contracts

1. For the existing crate-private `TreeMetadata::canonical(region, symbols)`,
   guarantee its exact existing result for every admitted input:
   - `Err(WorkspaceError::InvalidSymbol)` when `symbols == 0` or
     `symbols > tree_region_symbols(region)`;
   - otherwise `Ok(TreeMetadata { symbols, storage:
     TreeStorageState::Canonical { initialized: 0 } })`.
   Retain every existing guarantee and requirement.
2. For the existing crate-private `install_simple_tree`, add only this
   conditional success/error classification. The premise is an existing valid
   window/workspace (`window_bytes <= 16_777_216` and at least
   `window_bytes + FIXED_SCRATCH_BYTES` bytes), an alphabet in `1..=704`,
   selector in `0..=4`, the existing selector-derived symbol count, and exactly
   those active symbols being distinct and below the alphabet limit. Under
   that premise:
   - success holds exactly when `alphabet_limit <= tree_region_symbols(region)`
     and `tree < tree_region_count(region)`;
   - an invalid destination returns exactly
     `Err(WorkspaceError::InvalidSymbol)`.
   No condition is added on unused symbol-array entries. Retain every existing
   metadata, record, unchanged-on-error and frame guarantee.
3. Add checked ghost assertions/lemmas/invariants needed for those guarantees
   and input-private M1 failure-trace/plan-action proofs and controls. They must
   establish facts from existing requirements; no assumption, admitted proof,
   narrowed root domain or executable change is permitted.

This changes the proof contract across the existing input/prefix component
boundary. It introduces no new executable helper, mathematical-definition visibility or
runtime interface. It changes no executable body, signature, requirement,
algorithm, guard/error order, accepted input, dependency, toolchain, state or
workspace layout. Preserve W1's interface/results, B3c budget ownership, all
K6 read/write formulas, 5,696-action caps, 798/8,192 proof bounds, K4 encoding,
F2 fixture policy and the 425-unit construction/reset charge.

## Validation after approval

Check the strengthened contracts with the pinned tools and `--no-cheating`;
retain all earlier guarantees and admitted inputs. Rerun whole-crate proofs
before unchanged-specification deliberate defects, plus affected runtime
comparisons and exact/short-work checks. Report tool/resource failures
separately from semantic rejections. This decision neither completes M1 nor
authorizes another proof-boundary or architectural change.

## Human decision

The human replied "Approved" to the K7 request on 2026-11-12. This approves
Candidate K7 exactly as written above. It does not approve another contract or
architectural change.

## Current verification

K7 and the separately approved K8 contracts are implemented in the working
source. All four affected prefix functions retain their exact signatures,
requirements, executable bodies and existing guarantees. The earlier failed
singleton proof remains preserved in `evidence/m1-k7-progress/`.

Final validation passed 1,300 whole-crate proof checks with zero errors and
`--no-cheating`, all 108 runtime tests, and 29 semantic defect rejections after
that exact positive. Six new defects target the K7/K8 result guarantees; 23
retain affected K1/K3, K6 and tree-plan/frame checks. See
`evidence/brotli-b3c-m1-k7-k8.json`.

This completes these result-contract changes, not M1 or the supported-decoder
release gate. The remaining complete tree/failure/source-ledger and control
obligations and B3c/B3d/B4 and independent human review remain open.
