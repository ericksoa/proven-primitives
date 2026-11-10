# M1 block-length success guarantee: Candidate K3

Status: **explicitly approved as written by the human on 2026-11-09:**
“Approve K3 as written.” K1 was separately approved in the same human reply.
Implementation and scoped validation are recorded below; full M1 remains incomplete.

M1's initial block-length suffix planner and W1 executor both call the existing
crate-private `decode_block_length(symbol, suffix)` in `src/brotli_prefix.rs`.
Its current contract describes a successful result, but does not guarantee
success when its inputs are valid. That leaves a cross-module gap in the normal
suffix plan/action proof. The existing `block_length_value` mathematical
definition and the two source tables are already crate-visible.

## Exact proposed change

Add only this conditional success guarantee to `decode_block_length`'s existing
postconditions, retaining its current signature, requirements and guarantees:

```rust
symbol < 26
    && suffix < (1u32 << BLOCK_LENGTH_EXTRA_BITS@[symbol as int])
    ==> r.is_ok(),
```

The executable body, table values, error behavior and error priority remain
unchanged. Add only private proof lemmas or ghost assertions needed to verify
this guarantee in the prefix module and use it in input-private suffix proofs.
No other crate-visible item or helper-contract change is authorized by K3.

## Source review and effect

The existing table helper already guarantees an offset in 1..16,625 and an
extra-bit width in 2..24 for a valid symbol. The maximum permitted suffix is
16,777,215, so even the maximum offset plus that suffix is 16,793,840, below
`u32::MAX`. The existing checked addition should therefore succeed in the
proposed domain. This source argument must be checked by Verus; it is not a
substitute for the new proof. References at baseline
`d48e8feb44cd2fc47363809832de295d18270776`:
`src/brotli_prefix.rs:34`, `:38`, `:47`, `:56`.

K3 strengthens what an existing component promises to other crate proofs.
It couples the suffix proof to the existing block-length definition without
introducing a new executable adapter, algorithm, dependency, representation,
workspace assignment, budget owner or work policy. It preserves W1's `step`
and result representation and the approved 425-unit construction/reset charge.

## Verification and limits

Check the strengthened helper and normal suffix relation, preserving every
existing admitted input and failure guarantee. Run a whole-crate positive on
unchanged source before deliberate-defect controls. Include false rejection of
valid inputs, wrong decoded length, suffix consumption/status, source-table
reads, byte frames and exact/short reservation cases. Retain actual failures;
resource exhaustion and compiler errors are not semantic rejections.

K3 alone does not complete M1's full source-operation ledger, tree replay,
remaining malformed-state paths or their controls. B3c/B3d/B4 closure and
independent human specification review remain separate release obligations.

## Implementation evidence

The approved conditional success guarantee is implemented and checked, with
only ghost arithmetic added to the existing body. Normal suffix relations now
bind the original symbol/width and serialized queue to exact read outcome,
consumption, decoded length, next state and outcome-specific byte frame. The
planner charges its existing table and bit-read units, and the owner proves
exact combined planning/execution debit, limited-input mapping and reservation
failure identity under the stated normal-read domain. Existing admitted inputs
and runtime signatures are unchanged; malformed-state and complete-source-ledger
obligations remain separate.

The final library passed **1,207 whole-crate checks, zero errors**, using the
pinned checker with `--no-cheating`; see
`evidence/brotli-b3c-m1-k1-k3-attempt03-verification.json`. The runtime suffix
matrix passes all 26 symbols and three kinds. All **33 deliberate defects across five affected suites** were rejected after
their recorded whole-crate positives on identical library bytes. Eight are new
K1/K3 controls and 25 cover the existing builder, table-read/canonical-planning
and suffix-formula behavior. Exact transcripts and ordering are recorded in
`evidence/brotli-b3c-m1-k1-k3-controls.json`. The complete runtime suite remains **102 passed,
one failed** because of the separately reproduced repeat-history loss. No K4
encoding change, F2 fixture-policy change or M1 completion is authorized or
claimed by this checkpoint.
