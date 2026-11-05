# Canonical-builder proof boundary

Status: **held for review by the human on 2026-11-04:**
“Hold this proof-boundary change for review.” K1 remains unapproved and no
change below has been implemented.

The M1 planner in `brotli_input` has an exact mathematical classification of
canonical length validation, including the inspected failing prefix. The
installer in `brotli_prefix` proves that successful installation has valid
lengths and correct canonical records. It currently exposes neither a total
success/error classification nor the definitions of the three length sums
needed to equate the two existing models across modules.

`valid_builder_lengths` is crate-visible but closed; `code_weight`,
`used_space` and `nonzero_count` are private mathematical functions. There is
no approved shared proof interface that lets the input module unfold these
definitions. Adding that interface is a decision about the existing component
boundary and requires the human's exact approval.

## Candidate K1

Make only these existing mathematical definitions available to crate proofs:

| Existing item in `src/brotli_prefix.rs` | Exact proposed change |
|---|---|
| `code_weight(length: u8) -> nat` | Private spec to `pub(crate) open spec`; preserve its existing fifteen-bit weight definition. |
| `used_space(lengths: Seq<u8>) -> nat` | Private spec to `pub(crate) open spec`; preserve its existing sum and termination argument. |
| `nonzero_count(lengths: Seq<u8>) -> nat` | Private spec to `pub(crate) open spec`; preserve its existing count and termination argument. |
| `valid_builder_lengths(lengths: Seq<u8>) -> bool` | `pub(crate) closed spec` to `pub(crate) open spec`; preserve its existing definition. |
| `CODE_SPACE: u32 = 1 << 15` | Private constant to `pub(crate)` so the opened definition has a valid crate-level visibility boundary. Preserve the value. |

Strengthen the existing `install_builder_canonical_tree` proof contract,
without changing its Rust signature or its admitted inputs. Under the
following already-valid destination conditions:

- workspace and window satisfy the existing supported shape;
- tree index is valid for the selected region;
- initial metadata is canonical with zero records installed;
- `1 <= symbols <= 704` and the symbol count fits the selected region;
- `lengths_initialized == symbols`;

prove that success occurs **if and only if** the original builder lengths
satisfy the unchanged `valid_builder_lengths`. Otherwise prove the existing
`InvalidCodeLength` result and unchanged workspace and metadata. Keep the
current order and behavior of errors outside those conditions, and keep the
existing canonical-record correctness and installer-frame guarantees.

Use the opened mathematical definitions in input-private proof lemmas to
equate M1's existing weight/count validation model with the installer model.
Private proof-only lemmas and ghost loop invariants inside the existing two
modules are within this candidate; no additional crate-visible item is
authorized. Bind the resulting relations to deliberate source defects under
unchanged specifications, after a fresh whole-crate positive.

## Effect and limits

K1 exposes proof definitions across the existing input/prefix boundary. That
couples the planner proof to these precise mathematical definitions. It adds
no executable adapter, runtime state, dependency, work-result field, resource
policy or new algorithm. W1's `step`, its result representation, caller-owned
workspace, B3c budget ownership and the 425-unit construction/reset charge
remain unchanged.

K1 does not itself complete the canonical source-operation ledger, complete
serialized-tree replay, every header/body outcome, B3d, B4 or the independent
human review. Approval would authorize this proof-boundary change and its
verification, not establish that its new proof obligations already hold.

The human selected retaining the current proof boundary while this proposal
is reviewed. Current F2 validation and publication can finish independently.
