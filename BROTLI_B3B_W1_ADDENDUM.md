# B3b W1 serialized-state and error-tag addendum

Status: pending direct human approval. Candidate W1 was approved on 2026-10-26,
but its proposal fixed byte positions without enumerating every serialized tag,
error mapping, reset value, result field, work formula or cross-module helper.
This addendum supplies one exact Candidate E1. No implementation may depend on
E1 until the human approves it.

## E1 serialized tag tables

All tags are `u8`. Values not listed for a field are invalid serialized state,
cause terminal `InternalState`, and are proved unreachable from a valid
constructor and valid transitions.

### Outer and category tags

| Field | Values |
|---|---|
| Outer phase | `0 BlockCount`, `1 BlockTypeTree`, `2 BlockLengthTree`, `3 InitialBlockLength`, `4 DistanceParameters`, `5 ContextModes`, `6 LiteralContextMap`, `7 DistanceContextMap`, `8 LiteralTreeGroup`, `9 CommandTreeGroup`, `10 DistanceTreeGroup`, `11 Complete`, `12 Failed` |
| Literal/command/distance kind | `0 Literal`, `1 Command`, `2 Distance`, `255 None` |
| Context-map kind | `0 Literal`, `1 Distance`, `255 None` |
| Tree-group kind | `0 Literal`, `1 Command`, `2 Distance`, `255 None` |
| Active tree region | `0 Literal`, `1 Command`, `2 Distance`, `3 BlockType`, `4 BlockLength`, `5 TemporaryContext`, `255 None` |

### Nested phase tags

| Field | Values |
|---|---|
| Variable integer | `0 FirstBit`, `1 ThreeBitWidth`, `2 WidthSuffix` |
| Context map | `0 TreeCount`, `1 RleFlag`, `2 RlePrefixSuffix`, `3 TemporaryTree`, `4 ItemSymbol`, `5 RepeatSuffix`, `6 MtfFlag`, `7 MtfTransform`, `8 Coverage`, `9 Complete` |
| Tree group | `0 StartTree`, `1 CodeDescription`, `2 DrainSpan`, `3 Install`, `4 Complete` |
| Code description | `0 Selector`, `1 SimpleSize`, `2 SimpleSymbols`, `3 SimpleShape`, `4 ComplexAuxiliary`, `5 FinalSymbol`, `6 FinalRepeat`, `7 PendingSpan`, `8 CompleteSimple`, `9 CompleteComplex`, `10 Failed` |
| Code-description auxiliary | `0 None`, `1 StaticPrefix2`, `2 StaticPrefix3`, `3 StaticPrefix4` |
| Block length | `0 Symbol`, `1 Suffix`, `2 Complete` |
| Checked block switch | `0 Ready`, `1 AwaitLength`, `2 Failed` |

The variable-integer width byte is zero outside `WidthSuffix` and `1..=7`
inside it. The code-description auxiliary byte is zero outside
`ComplexAuxiliary`.

## E1 private errors and serialized mapping

The exact private errors are:

```rust
enum CompressedHeaderError {
    InvalidFormat(CompressedFormatError),
    Truncated,
    UnsupportedMode,
    Workspace(WorkspaceError),
    InternalState,
}

enum CompressedFormatError {
    InvalidPrefixCode,
    DuplicateSimpleSymbol,
    CodeLengthSpace,
    InvalidBlockLength,
    ContextMapRepeat,
    ContextMapValue,
    ContextMapCoverage,
    InvalidBlockSwitch,
    InvalidSequence,
    InvalidMetadata,
    InvalidDistanceAlphabet,
    InvalidBlockDeclaration,
}
```

State byte 11 is the terminal tag:

| Tag | Meaning |
|---:|---|
| 0 | no terminal error |
| 1 | `InvalidFormat(detail)` |
| 2 | `Truncated` |
| 3 | `UnsupportedMode` |
| 4 | `Workspace(detail)` |
| 5 | `InternalState` |

The detailed `u16` at bytes 172..174 is zero when the terminal tag is 0, 2, 3
or 5. For `InvalidFormat`, detail values 1 through 12 follow the
`CompressedFormatError` declaration order above. For `Workspace`, detail values
1 through 6 are `InvalidWindowBits`, `WorkspaceTooSmall`, `InvalidTree`,
`InvalidSymbol`, `InvalidCodeLength`, `UninitializedRecord` in existing
`WorkspaceError` declaration order. Other tag/detail combinations are invalid
serialized state.

Lower-level mappings are exact:

- B3a invalid/duplicate/space errors map to format details 1, 2 and 3;
- every incomplete required field at final input maps to terminal tag 2;
- block-length failures map to detail 4;
- context repeat overflow, out-of-range direct values and missing advertised
  trees map to details 5, 6 and 7;
- B2 invalid block switch, invalid sequence, invalid prefix symbol, invalid
  length and invalid declaration map to details 8, 9, 1, 4 and 12;
- malformed/noncanonical metadata maps to detail 10; and
- a normal-window distance alphabet outside `16..=520` maps to detail 11.

`from_meta` wrong-phase or impossible valid-state failures are `InternalState`.
Workspace errors remain private construction/component errors. The later public
core maps every format detail and defensively maps `InternalState` to
`StreamError::InvalidFormat`, maps `Truncated` and `UnsupportedMode` directly,
and maps construction `WorkspaceTooSmall` to `InitError::WorkspaceTooSmall`.
The invariant proves `InternalState` unreachable from valid initialized state.

## E1 exact complete result

```rust
struct CompressedHeader {
    num_block_types: [u16; 3],
    initial_block_lengths: [u32; 3],
    distance_postfix_bits: u8,
    num_direct_distance_codes: u16,
    distance_alphabet_size: u16,
    num_literal_htrees: u16,
    num_distance_htrees: u16,
    literal_context_map_len: u16,
    distance_context_map_len: u16,
    literal_context_modes_len: u16,
    literal_trees_initialized: u16,
    command_trees_initialized: u16,
    distance_trees_initialized: u16,
    active_literal_tree: u16,
    active_command_tree: u16,
    active_distance_tree: u16,
}
```

At completion, map/mode lengths equal `64 * num_block_types[0]`,
`4 * num_block_types[2]` and `num_block_types[0]`. Initialized tree counts equal
`num_literal_htrees`, `num_block_types[1]` and `num_distance_htrees`.
`active_literal_tree` is transformed literal map row 0/context 0,
`active_command_tree` is zero, and `active_distance_tree` is transformed
distance map row 0/context 0. Every returned index has initialized metadata and
is below its corresponding group count.

## E1 step granularity

`step` performs bounded zero-input/internal transitions until one of these is
true:

- a required input field cannot complete from the retained queue and supplied
  bytes;
- the compressed header completes; or
- a permanent error occurs.

It therefore has no public `Progress` result. `NeedInput` implies nonfinal input
and `consumed == input.len()`. Final exhaustion at any required field is
`Truncated`. Span draining, trivial-map fill, atomic MTF, coverage, installation
and tree handoff continue in the same call without manufacturing `NeedInput`.
Every loop has a decreasing bound from the fixed state and capacities.

## E1 canonical initialization image

Construction and reset first write zero to all 256 scalar-state bytes, then set:

- outer phase byte 10 to `BlockCount`;
- current-kind byte 12 to `Literal`;
- variable-integer byte 13 to `FirstBit`;
- context-map phase byte 15 to `TreeCount`;
- pending-run byte 53 to `255`;
- tree-group kind byte 54 to `255` and phase byte 55 to `StartTree`;
- active-tree region byte 114 to `255`;
- block-length phase byte 126 to `Symbol`;
- block-switch phase byte 129 to `Ready`;
- block rings at bytes 134..146 to six little-endian values
  `[1, 0, 1, 0, 1, 0]`;
- block-switch kind byte 158 to `255`; and
- MTF upper-bound byte 159 to `63`.

All other counters, arrays, errors and padding remain zero. `from_meta` then
zeros queue bytes 0..8, copies only the B1 queue's valid pending bytes, and
stores its length/offset in bytes 8 and 9. The serialized queue invariant is
exactly B1's valid LSB-first logical bit sequence; unused queue bytes are zero
and never influence results. No mutable queue/parser shadow state survives a
return from `step`.

Reset uses this same image. Starting a later compressed meta-block uses the same
image followed by the new completed meta-header queue. Public request reset is
charged and additionally performs the already-approved outer decoder reset.

## E1 code-description and temporary-state lifecycle

The current B3a logical state is serialized only in bytes 60..134. Each
transition loads a local value, applies the already-checked transition, and
stores the exact next value before returning or continuing. Persistent Rust
fields do not shadow it.

For simple trees, source symbols receive these exact lengths:

- selector 0: `symbols[0]` is a metadata `Single` and no record is read;
- selector 1: `symbols[0..2]` receive `[1, 1]`;
- selector 2: `symbols[0..3]` receive `[1, 2, 2]`;
- selector 3: `symbols[0..4]` receive `[2, 2, 2, 2]`; and
- selector 4: `symbols[0..4]` receive `[1, 2, 3, 3]`.

Every other admitted symbol receives `(length=0, code=0)`. Complex spans are
drained once in increasing symbol order. No new tree starts until destination
metadata is complete.

Builder initialized counts reset to zero before every description. Temporary
metadata changes from `Unused` to the selected `Single` or a zero-initialized
`Canonical`, then to complete before map-item decoding. Coverage bitmap reuse
starts only after all map items and optional MTF finish. It ends before the next
temporary tree begins. Builder/temp bytes may remain stale afterward but cannot
be read without the corresponding new initialized state.

## E1 MTF bytes and exact work

The first three MTF bytes are unread padding: they may retain old values and are
never read or published. The fourth byte, at `MTF_OFFSET + 3`, is the
addressable scratch cell corresponding to upstream `list[-1]`; it is overwritten
before every read. The list occupies `MTF_OFFSET + 4 .. +260`.

For prior upper bound `U` in `0..=63`, initialization writes exactly
`4 * (U + 1)` list bytes. For each raw rank `r`, the transform performs one map
read, one selected-list read, one scratch write, one map write, and `r + 1`
source-cell reads plus `r + 1` destination-cell writes. The exact MTF cell-work
formula, excluding separately charged state transitions, is:

```text
4 * (U + 1) + sum_over_map(2 * rank + 6)
```

It is at most 8,454,400 for the 16,384-byte literal map. The next bound is
`OR(all raw ranks) >> 2` and is at most 63.

B3c first charges each pre-scan map read while accumulating the exact formula,
then requires and deducts the complete transform charge before the first MTF
write. Resource failure is therefore terminal before any map/list change; the
pre-scan has no workspace effect. Executing the prepaid transform does not
decrement the budget again.

## E1 coverage bitmap and work

Tree index `t` maps to builder byte `t / 8` and mask `1 << (t % 8)`. Coverage
clears all 32 bytes, scans the transformed map, rejects any value at least
`num_htrees`, sets its bit, then requires bits `0..num_htrees-1` all set. Because
all 32 bytes start at zero and only bounded tree indices are set, every unused
high bit remains zero.

Missing coverage is permanent `InvalidFormat(ContextMapCoverage)`. The exact
coverage cell-work formula, excluding state transitions, is:

```text
32 + 3 * map_size + num_htrees
```

This counts bitmap clears; each map read plus bitmap read/write; and each final
required-bit read.

## E1 private helper ownership and signatures

`brotli_prefix.rs` owns only byte-addressed storage/transform helpers:

```rust
fn write_tree_metadata(workspace, window_bytes, region, tree, meta)
    -> Result<(), WorkspaceError>;
fn read_tree_metadata(workspace, window_bytes, region, tree)
    -> Result<TreeMetadata, WorkspaceError>;
fn write_next_context_entry(workspace, window_bytes, kind, active_len,
    initialized, value, num_htrees) -> Result<u16, WorkspaceError>;
fn read_context_entry(workspace, window_bytes, kind, initialized, index,
    num_htrees) -> Result<u8, WorkspaceError>;
fn write_next_context_mode(workspace, window_bytes, initialized, value)
    -> Result<u16, WorkspaceError>;
fn read_context_mode(workspace, window_bytes, initialized, index)
    -> Result<u8, WorkspaceError>;
fn inverse_mtf_context_map(workspace, window_bytes, kind, active_len,
    mtf_upper_bound) -> Result<(u8, u64), WorkspaceError>;
fn check_context_tree_coverage(workspace, window_bytes, kind, active_len,
    num_htrees) -> Result<(bool, u64), WorkspaceError>;
```

Here `kind` is the exact `Literal=0` / `Distance=1` context-map enum. Result
errors are the existing workspace error for address/initialization failures.
The coverage boolean is false exactly when a required tree is absent; the
caller maps it to the approved format detail. Every helper proves exact frames
and old-storage independence.

`brotli_input.rs` owns the scalar-state offsets, typed tag serializers,
constructor/reset image, all parser phases and the outer private API. Scalar
helpers remain module-private and are not callable across the prefix/input
boundary. `brotli_block.rs` retains B2 logic; B3b serializes/reconstructs its
exact logical state through module-private adapters and propagates its results.
No new Rust module or public API is introduced.

## E1 approval requested

Approval of **Candidate E1 as written** authorizes only these exact tag/error
tables, complete-result representation, step granularity, initialization image,
B1/B3a serialization relation, simple-tree mapping, temporary-state lifecycle,
MTF/coverage work formulas and helper ownership/signatures as an addendum to
approved W1. It does not alter W1's public API, workspace size, dependencies,
tools, trust boundary, B3c/B4 scope or support status.
