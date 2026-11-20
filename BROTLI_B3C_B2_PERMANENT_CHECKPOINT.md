# B3c actual B2 caller: permanent-failure outcome

Status: the named exhausted-single-type outcome and budget-validation checkpoint
is complete on the source in
[`evidence/brotli-b3c-b2-permanent.json`](evidence/brotli-b3c-b2-permanent.json).
This follows the byte-effect checkpoint in signed commit
`ce87a2555a1c11813b8d5b57c9ccd830c16583b4`. It closes the accepted retry-bypass
fault recorded there for the condition below, using C1's already-approved
behavior and existing crate-private state observations. It adds no function,
type, visibility opening, compiled interface or resource-policy change.

The actual `advance_serialized_body_block_switch` contract now guarantees zero
consumption and `BodySwitchStatus::Failed(_)` when:

- the original valid-budget/workspace requirements hold;
- the requested kind is 0, 1 or 2;
- the stored switch-phase tag is Ready (zero);
- the requested stored type count is at most one; and
- that kind's stored remaining count is zero.

The original admitted input set is retained. Malformed other saved fields may
fail during loading; they still cannot become `NeedInput` or `Complete` under
this condition. The guarantee is a permanent failure family, not an exact error
detail for every malformed state. It does not establish the complete multi-type
switch grammar, saved-ring/store round trip, exact call/snapshot trace or
whole public-stream propagation.

The existing private loader now binds its successfully returned type counts,
remaining counts and Ready phase to the existing scalar observations. Added
loop invariants carry these facts through its original validation. No parsing,
validation, guard or executable statement changed. Existing B2 component
contracts remain checked premises. The proof uses the existing state views;
there is no new shared decoder model or proof-observation API.

`RequestBudget::new` also now guarantees success exactly when the supplied
window limit is 10 through 24. All other supplied limits, including zero input,
output, work, call and initialization quotas, remain accepted. Its original
success effects and sole `InvalidLimits` error remain. This proves C1's
existing window-only validation rule; it does not introduce a minimum quota.

The actual entire-crate `--no-cheating` run passed **1,397 checks, zero errors**.
After that unchanged positive, **six distinct faults were rejected semantically**:
actual-caller retry, false completion and false consumption on permanent
rejection; spurious valid-window budget failure, accepting an invalid window,
and rejecting zero work. Every mutation preserves its function header/contract
and changes only its body. No syntax, type, resource or tool failure counts.

The verified source was checked at the recorded private candidate path and then
promoted without edits. Every core source file's SHA-256 matches the whole
positive and the unchanged baseline used to generate all six control copies;
`promotion-qualification.json` records that
content qualification. The promoted workspace then passed **116 runtime tests**
under the same pinned toolchain. There are no explicit non-test source-path/environment lookups or includes;
fixture includes occur only in the existing unit-test modules. This is
source-content qualification, not a source-to-binary correctness theorem.

The preceding byte-effect gate's 44 rejections remain bound to that earlier
snapshot. They were not rerun or added to this six-case count. All prior root
contracts and mathematical definitions remain in the new full-crate positive.
The executable bodies, arguments, requirements, algorithms, workspace, quota
debits, 425-unit reset charge, W1 interfaces and F2 fixtures remain. The static
preservation audit reconstructs the exact parent by removing only these new
contracts/invariants and three existing-tool solver-isolation annotations.

Earlier private candidate attempts remain in `earlier-candidates.tar.gz`:
`01` was interrupted without a complete whole result; `02` verified 1,396 checks
and had one resource failure in the unchanged M1 initial-block-length helper.
The final source isolates that helper and the two new proof roots, preserving
all original allowances. The isolated helper passed at the same 300 allowance.
Those earlier failed/interrupted attempts are not promoted to positive results.

The write-billing mismatch remains open: the prior static audit finds 24
source-level byte writes against the existing eight-unit emission debit.
Candidate E3 remains pending direct human approval and is unimplemented.
`e3-scope-qualification.json` verifies all five proposed producers and all 33
direct caller sites remain byte-identical to the approved-boundary proposal's
production graph, despite these unrelated proof-only improvements. E3 approval
must not be inferred from this checkpoint, the source audit, a signature or a
test result.

Full B3c body/stream and source-ledger composition, dictionary/LZ77 refinement,
B3d/B4, the F2 monkey/native disagreement, independent human specification
review and supported-decoder/release gates remain open. The trusted base
continues to include specifications/interpretations, pinned Verus/Z3/vstd and
Rust/LLVM, Apple build tools and the operating environment.
