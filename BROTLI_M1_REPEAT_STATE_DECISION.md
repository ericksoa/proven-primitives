# Repeat-state serialization correction: Candidate K4

Status: **approved as written by direct human reply on 2026-11-09**.
Implementation and verification are authorized only within the exact scope below.

M1 tree-replay analysis found actual state loss in the existing W1 codec.
`ComplexRepeat` contains both the previous repeat's code length, used to decide
whether RFC repeat chaining resets, and the current repeat's length. The store
helper writes the previous value to scalar byte 71, then overwrites the same
byte with the current value. The load helper reads byte 71 as both values.

## Reproduced evidence

`m1_repeat_class_switch_survives_serialized_roundtrip` uses a complete valid
auxiliary alphabet with symbols 7, 8, 16 and 17 at length two. Existing field-
decoder calls consume byte `c6`: a direct length eight, a three-entry repeat
of eight, then the zero-repeat symbol. The resulting logical repeat state has
symbol position four, previous repeat count three, previous repeat length
eight, and current repeat length zero. This is reached by actual decoder
calls, starting at that completed auxiliary alphabet.

After store/load, previous repeat length is zero. Feeding the zero suffix
therefore produces **eight zero lengths instead of three**, starting at index
four. This is a runtime regression, not a proof result. It establishes an
admitted-state/field-sequence divergence; it is not yet a complete compressed-
stream/native-comparison witness or evidence of a memory-safety violation.

Exact failed output: `evidence/m1-repeat-class-switch-before-fix.log`.
Source identity and compressed snapshot are recorded alongside that log.
M1's local planner retains the original logical history, so the mismatch also
prevents proving its exact replay/state/work relation.

## Exact proposed K4 change

Keep the existing 256-byte W1 scalar layout and every Rust representation.
Change only the tag-six (`ComplexRepeat`) interpretation as follows:

| Scalar byte | Existing name | Meaning under K4 |
|---|---|---|
| 71 | `B3B_REPEATED_LENGTH` | Preserve `progress.repeat_code_len`, the previous repeat length. |
| 174 | `B3B_PENDING_SPAN_LENGTH` | For tag six only, store the current repeat length, zero or 1..15. For tag seven, retain its existing pending-span-length meaning. |

In `store_complex_code_description_payload`'s `ComplexRepeat` arm, retain the
existing `store_complex_progress` call, and redirect its following one-byte
current-length write from byte 71 to byte 174. Retain the existing earlier
zeroing of byte 174 in `store_code_description_decoder`.

In `load_code_description_decoder`, keep the progress's previous repeat length
from byte 71. For tag six, load current repeat length from byte 174, reject
values above 15 as the existing `InternalState`, and derive the existing extra-
bit width from current length: three for zero and two otherwise. All other
tag interpretations and error encodings remain unchanged.

Update E1's tag-dependent encoding documentation and input-private proof
relations to match this exact correction. Do not introduce a new scalar byte,
field, dependency, runtime, public/crate-visible adapter or result field.

## Effects and tradeoff

This changes a private serialized-state protocol, so it requires explicit
human approval even though it corrects an existing defect. Byte 174 acquires
a second meaning selected by the existing phase tag. The alternative of a
dedicated reserved byte would introduce a separate byte-ownership decision;
it is not selected by this proposal. Teaching the planner to reproduce the
lost history would preserve the format defect and would not prove the
approved B3a repeat transition.

The number of writes is unchanged: the current-length write still writes one
byte after storing the progress. The extra scalar-state load is ordinary
bookkeeping under the existing policy. Preserve every work formula, caller-
owned workspace size, B3c budget ownership, W1 `step` and result representation,
the 5,696-action bounds and the 425-unit construction/reset charge. The repeat
algorithm and its checked chaining definitions remain unchanged.

## Validation and limits

Prove store/load agreement for this state and retain all original admitted
inputs and root contracts. Test nonzero-to-zero, zero-to-nonzero, same-class
chaining and suffix exhaustion/resumption. Run a fresh whole-crate positive
before unchanged-specification defect controls. Preserve all failed output;
resource exhaustion, compiler failures and interrupted runs are not semantic
defect rejections.

Rerun the existing native fixtures and retain their actual results. K4 does
not authorize changing the separately approved F2 fixture policy. If this
correction changes an F2 expectation, present the actual evidence for a
separate human decision before changing that expectation.

K4 alone does not complete M1's full source-operation ledger, remaining phase
relations or their controls. B3c/B3d/B4 and independent human specification
review remain separate release obligations.

## Implemented and checked K4 checkpoint

The exact approved byte-71/174 correction is implemented. Private checked
relations bind every saved code/progress field, prove a valid repeat image
reloads successfully as the expected decoder, preserve the serialized queue,
and prove the next field agrees with the original state despite unused queue
padding. The actual serialized-tree loop carries and checks this repeat image
across iterations. Original requirements, frames, runtime interfaces, write
counts/formulas, workspace, action caps and reset charge remain intact.

The final source passed **1,210 whole-crate checks, zero errors**, with the
pinned `--no-cheating` checker. All **104 runtime tests** pass, including the
original c6 class-switch witness and 2,048 broader history/resumption
configurations, tag-seven behavior, invalid lengths and unchanged F2 fixtures.
All **21 defects across three affected suites** were semantically rejected
following that unchanged whole-crate positive: six new codec controls, six
existing serialization/error controls and nine existing state/refinement
controls. Exact identities and actual transcripts are recorded in
`evidence/brotli-b3c-m1-k4.json` and its control manifest.

The earlier 1,209/one-error whole attempt, the interrupted slow attempt and all
failed/partial outputs remain retained. A ghost block-count witness and local
unfolding control resolved those proof issues without changing runtime behavior
or root guarantees. No tool/resource/harness failure counts as a defect rejection.

This closes the named K4 correction, not M1. K5's loader-validation read charges
and private pre-scan receipt remain proposed and unimplemented pending direct
human approval. Complete ledger/replay, remaining phase/failure/control closure,
B3c/B3d/B4 and independent human release review remain open.
