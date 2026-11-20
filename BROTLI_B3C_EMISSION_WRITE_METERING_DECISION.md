# B3c emission write metering: E3 decision

Status: **pending direct human approval; not implemented**.

The broader B3c source audit found a concrete accounting mismatch. A successful
`emit_byte` performs 24 source-level byte writes while its existing successful work
debit is eight. C1's approved resource policy charges each workspace, window
and caller-output byte write. This is a source-derived success-path inventory,
not yet a checked invocation-specific source receipt or a complete body ledger.

| Reached success action | Calls | Stores per call | Stores |
| --- | ---: | ---: | ---: |
| Caller-output assignment | 1 | 1 | 1 |
| Window assignment | 1 | 1 | 1 |
| `write_b3c_state_byte` | 2 | 1 | 2 |
| `write_b3c_state_u32` | 3 | 4 | 12 |
| `write_b3c_state_u64` | 1 | 8 | 8 |
| Total | | | **24** |

All six typed-write calls must have returned success before `emit_byte` can
return success. The raw helpers' successful paths contain the fixed stores
listed above. Counting each typed-write call once plus the two direct stores
gives eight; expanding the three four-byte writes and one eight-byte write
adds the missing 16 source-level writes. This is not a hardware-store or cycle
claim. The eight-unit counter-effect proof is valid for its existing
contract; it does not establish that these stores are fully paid. The byte-image
checkpoint likewise must not be reported as a complete resource proof.

The exact source hashes, primitive store sites and 33 direct caller sites are
recorded in `evidence/b3c-emission-write-audit/source-audit.json`. The frozen
inputs for this decision are:

- `src/brotli.rs`: `6472034d30705cd1627fb846de1370e5e1d65da01682d78ca858e2a1bd51e4a9`.
- `src/brotli_input.rs`: `3e2f1bb6f4535920666f2cf1c838f5db4d23f8ed2dbd4545f49194bfd940789e`.
- `tests/proof_rejection.rs`: `986bfed687b75841673093146ea71a2c1b23a140a457ab6cc675e186e1d0390a`.

## Candidate E3

Extend the already-used Approach R technique to exactly five existing producers:

1. `brotli_input::write_b3c_state_byte`;
2. `brotli_input::write_b3c_state_u32`;
3. `brotli_input::write_b3c_state_u64`;
4. `BrotliDecoder::emit_byte`;
5. `BrotliDecoder::emit_uncompressed_byte`.

For each existing ordinary result type `T`, change its internal return type to
`(T, Ghost<nat>)`, retaining the ordinary result as component zero. **This changes
internal compiled return types**, including the three crate-private scalar
writers. It does not change public Brotli/W1 interfaces or arguments.

Initialize a local ghost store counter to zero. Increment it at each reached
primitive byte assignment; merge child receipts as the calls return, including
all errors. Construct receipts from these reached counters, never from a charge
formula, final image, changed-cell count or budget difference. Prove one/four/
eight successful stores in the raw writers and zero stores on their address
errors. Prove 24 stores on successful shared/uncompressed emission and zero on
its errors in the original admitted domain. Retain the complete functional,
image/frame and error guarantees on component zero.

Only the direct caller sites in the frozen audit may change to propagate these
receipts or discard them while preserving their ordinary results and algorithms.
They belong to:

- `src/brotli.rs`: `write_phase`, `fail`, `set_state_byte`, `set_state_u32`,
  `consume_metadata_byte`, `commit_eof_if_complete`, `emit_byte`,
  `emit_uncompressed_byte`, `step_body_emit_literal`, `step_body_phase_copy_setup`,
  `step_body_phase_copy_emit`, and `step_stream_transition`.
- `src/brotli_input.rs`: `store_meta_phase`,
  `advance_serialized_window_header`, and `build_serialized_dictionary_word`.

Add one module-private constant in `brotli.rs`:

```rust
const B3C_EMISSION_WRITE_WORK: u64 = 24;
```

Correct the shared emission's write-only reservation/debit from eight to 24,
checked against its reached store receipt. Update only the corresponding
success work-delta guarantees and `output_block_reason`'s minimum-work check,
body and contract. Use the private constant for these terms. Keep
`emit_uncompressed_byte`'s existing eight-unit entry requirement unchanged;
8–23 work units can now return `ResourceLimit` without writes, so its admitted
input set is not narrowed. An empty output with fewer than 24 work units must
be a resource failure rather than `NeedOutput`. Limits below 24 continue to be
valid RequestLimits; no constructor/default limit changes are proposed.

Update only numerical emission-work expectations and the two existing
undercharge/priority mutation anchors that encode the old eight-unit value.
Preserve their assertions and tested defect meanings. Add source-receipt
omission, 24/23 work-boundary, no-write resource failure and unchanged-specification
controls. Preserve format bytes, decoded-byte expectations, strict tree coverage
and F2's quickfox/monkey/compression policy. Do not reinterpret old mixed
resource results as semantic rejections.

## Scope and effects

E3 changes the write-cost component of work-limited request behavior and the
five named internal compiled return types. It preserves all existing arguments,
requirements, functional guarantees, layout, algorithms, ordinary guard/error
order, output atomicity, dependencies and proof trust, except for the explicitly
corrected eight-to-24 work effects and minimum emission-work thresholds.
Preserve the 425-unit construction/reset charge, four-unit terminal escrow,
M1's completed frozen helper scope, W1 interfaces, 5,696-action caps and all
other work formulas. No other producer, mathematical visibility opening,
private/public API or policy change is approved by selecting E3.

This is the exact write-only component. Input/window/dictionary source-read
prepayment, additional caller state writes/transitions, complete body ledgers,
actual B2 handoff and stream/call-sequence composition remain separate. E3 does
not classify an unpaid source read as free, complete B3c, or authorize a new
caller-planning/reservation architecture. Any additional boundary or policy
needed for those later obligations returns to the human.

Run fresh unchanged whole-crate verification before controls, preserve source/
tool/log identities and actual earlier failures, and publish the scoped result.
No test, assistant or automated reviewer can substitute for human specification
review or approve another architectural decision.

## Why direct approval is required

`AGENTS.md` requires direct human approval for private/cross-module APIs and
resource-policy changes. The original Approach R approval expressly limits its
return-type changes to the frozen M1 graph and says that any helper/module
outside it returns to the human. These five producers are outside that graph.
Continuing broader B3c verification does not select E3. No E3 return-type or
billing change will be implemented without the human's exact approval.


## Preimplementation harness qualification

The two production source hashes and the five-producer/33-caller graph above
remain exact. The legacy B3c control harness subsequently required a stale
M1-refactor mutation selector repair and a matched selected-emission checker
allowance of 300, already used by whole-crate checking. The terminal-retry
control also uses an identical allowance of 300 in each temporary source copy,
then restores its original file; production `step` retains 60. The original assertions,
classifiers, contracts, production allowances and runtime inputs remain.
`evidence/b3c-emission-write-audit/harness-qualification.json` records the exact
old/current test hashes and verifies reconstruction by reversing only those
host-harness repairs. This is not an E3 implementation or an additional
architectural approval.
