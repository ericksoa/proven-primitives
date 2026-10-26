# B3b W1 serialized-state and error-tag addendum

Status: the human approved Candidate E1 exactly as written on 2026-10-26.
Candidate W1 was approved on the same date, but its proposal fixed byte
positions without enumerating every serialized tag, error mapping, reset value,
result field, work formula or cross-module helper. This addendum supplies those
exact decisions. Alternatives remain unapproved.

Implementation then reached the existing B2 module boundary: E1 authorized
module-private B2 adapters but did not freeze their callable shape. Candidate
E2 below supplies that one remaining cross-module API and a bounded rule for
input-local implementation helpers. E2 remains pending direct human approval.

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

State byte 85 is the intermediate B3a code-description error tag:

| Tag | Meaning |
|---:|---|
| 0 | none |
| 1 | `MetaBlockNotCompressed` |
| 2 | `InvalidAlphabet` |
| 3 | `DuplicateSimpleSymbol` |
| 4 | `CodeLengthSpace` |
| 5 | `Truncated` |

`MetaBlockNotCompressed` in the serialized B3b path maps to `InternalState`;
tags 2, 3 and 4 map to format details 1, 2 and 3; tag 5 maps to terminal
`Truncated`. Other values are invalid state.

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

Context-map repeat arithmetic is evaluated before casting in `u32`/natural
numbers: `repeat = (1u32 << symbol) + suffix as u32`. Symbol 16 may therefore
denote up to 131,071 repeats without machine overflow. The decoder first checks
`context_index as u32 + repeat <= active_map_size as u32`; only a bounded result
is cast and written. Exact fill is valid and any excess is a permanent
`ContextMapRepeat` error.

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
copies exactly the B1 queue's valid pending bytes into the already-zero queue
area and stores its length/offset in bytes 8 and 9. The serialized queue invariant is
exactly B1's valid LSB-first logical bit sequence; unused queue bytes are zero
and never influence results. No mutable queue/parser shadow state survives a
return from `step`.

The image performs exactly 256 zero writes, then eight nonzero override writes:
bytes 53, 54, 114, the low bytes of ring entries 0/2/4, byte 158 and byte 159.
It then writes all six block metadata records and the temporary metadata record
to canonical `Unused`, for 28 more byte writes. `from_meta` writes exactly the
valid pending-byte count plus bytes 8 and 9. Thus scalar/metadata initialization
costs exactly `294 + pending_len` byte writes. Zero-valued phase/kind/counter
fields and ring high bytes are not rewritten after the initial 256 zero writes.

Reset uses this same image. Starting a later compressed meta-block uses the same
image followed by the new completed meta-header queue. Public request reset is
charged and additionally performs the already-approved outer decoder reset.

## E1 code-description and temporary-state lifecycle

The current B3a logical state is serialized in bytes 60..126 plus pending-span
length byte 174. Each
transition loads a local value, applies the already-checked transition, and
stores the exact next value before returning or continuing. Persistent Rust
fields do not shadow it.

Byte 174 is `pending_span_length`: it is `0..=15` only during `PendingSpan` and
zero otherwise. During a pending span, `span_start` is the builder initialized
count, `span_count` is `final_symbol_index - builder_initialized`, and byte 174
is the exact emitted length. This includes generated trailing-zero spans and
allows direct zero-length spans to resume without shadow state. Checked padding
therefore begins at byte 175.

For simple trees, source symbols receive these exact lengths:

- selector 0: `symbols[0]` is a metadata `Single`; every tree-record byte for
  that tree remains stale/uninitialized and no record is read;
- selector 1: `symbols[0..2]` receive `[1, 1]`;
- selector 2: `symbols[0..3]` receive `[1, 2, 2]`;
- selector 3: `symbols[0..4]` receive `[2, 2, 2, 2]`; and
- selector 4: `symbols[0..4]` receive `[1, 2, 3, 3]`.

For selectors 1 through 4, every other admitted symbol receives
`(length=0, code=0)`. Complex spans are
drained once in increasing symbol order. No new tree starts until destination
metadata is complete.

Builder initialized counts reset to zero before every description. Construction
and every compressed-meta-block reset write all three block-type, all three
block-length and the temporary metadata records to `Unused`; these seven records
therefore have initialized authority immediately. Group metadata remains stale
with initialized-prefix counts zero and is overwritten sequentially before
those counts advance. Temporary metadata changes from initialized `Unused` to
the selected `Single` or a zero-initialized `Canonical`, then to complete before
map-item decoding. Coverage bitmap reuse starts only after all map items and
optional MTF finish. It ends before the next temporary tree begins. Builder/temp
bytes may remain stale afterward but cannot be read without the corresponding
new initialized state.

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

The reusable-list invariant requires the 256-byte list to be a permutation of
`0..255` and every position at or above `4 * (U + 1)` to contain its identity
value. First use has `U=63`, so full initialization establishes the invariant
independently of old list storage. The transform preserves the permutation and
establishes the suffix-identity condition for its returned next bound. With
input ranks below `num_htrees`, every transformed map value is also below
`num_htrees`.

`inverse_mtf_context_map` receives `num_htrees`; its returned `u64` is exactly
the transform formula above and excludes the separately charged pre-scan map
reads.

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

The coverage helper requires the checked precondition that every transformed
map value is below `num_htrees`. It returns `false` exactly for missing required
tree indices. Out-of-range parsed direct values are rejected by the caller as
`InvalidFormat(ContextMapValue)` before any context write; they never reach the
storage or coverage helper.

## E1 private helper ownership and signatures

`brotli_prefix.rs` owns only byte-addressed storage/transform helpers:

```rust
enum MetadataReadError {
    Workspace(WorkspaceError),
    InvalidEncoding,
}

fn write_tree_metadata(workspace, window_bytes, region, tree, meta)
    -> Result<(), WorkspaceError>;
fn read_tree_metadata(workspace, window_bytes, region, initialized_prefix, tree)
    -> Result<TreeMetadata, MetadataReadError>;
fn write_next_context_entry(workspace, window_bytes, kind, active_len,
    initialized, value, num_htrees) -> Result<u16, WorkspaceError>;
fn read_context_entry(workspace, window_bytes, kind, initialized, index,
    num_htrees) -> Result<u8, WorkspaceError>;
fn write_next_context_mode(workspace, window_bytes, initialized, value)
    -> Result<u16, WorkspaceError>;
fn read_context_mode(workspace, window_bytes, initialized, index)
    -> Result<u8, WorkspaceError>;
fn inverse_mtf_context_map(workspace, window_bytes, kind, active_len,
    num_htrees, mtf_upper_bound) -> Result<(u8, u64), WorkspaceError>;
fn check_context_tree_coverage(workspace, window_bytes, kind, active_len,
    num_htrees) -> Result<(bool, u64), WorkspaceError>;
fn install_simple_tree(workspace, window_bytes, region, tree, alphabet_limit,
    selector, count, symbols) -> Result<TreeMetadata, WorkspaceError>;
```

Here `kind` is the exact `Literal=0` / `Distance=1` context-map enum. Result
errors are the existing workspace error for address/initialization failures.
Metadata reads require `tree < initialized_prefix`; the prefix is three for
each block metadata region after reset, one for temporary metadata after reset,
and the exact installed group count for literal/command/distance regions.
`InvalidEncoding` maps to format detail 10. Context write helpers have proved
preconditions `value < num_htrees` and therefore cannot produce a format error.
The coverage boolean is false exactly when a required tree is absent; the
caller maps it to the approved format detail. Every helper proves exact frames
and old-storage independence.

The approved B3a builder/tree-record/canonical-installer helpers remain
crate-private cross-module helpers. `install_simple_tree` implements the exact
selector mapping above, including metadata-only selector 0 and full zero records
for inactive symbols in selectors 1 through 4.

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

## Candidate E2: narrow B2 adapter and local-helper rule

E2 exposes none of the existing private B2 types or fields. `brotli_block.rs`
adds only these crate-private logical adapter types:

```rust
enum B3bSwitchFailure {
    InvalidDeclaration,
    InvalidBlockSwitch,
    InvalidPrefixSymbol,
    InvalidBlockLength,
    InvalidSequence,
}

enum B3bSwitchPhase {
    Ready,
    AwaitLength { kind: u8, block_type: u16 },
    Failed(B3bSwitchFailure),
}

struct B3bSwitchState {
    num_types: [u16; 3],
    ring: [u16; 6],
    remaining: [u32; 3],
    phase: B3bSwitchPhase,
}

enum B3bSwitchOutcome {
    NeedInput,
    Complete { kind: u8, block_type: u16, block_length: u32 },
    Failed(B3bSwitchFailure),
}

struct B3bSwitchResult {
    state: B3bSwitchState,
    consumed_fields: u8,
    outcome: B3bSwitchOutcome,
}

fn advance_b3b_switch(
    state: B3bSwitchState,
    requested_kind: u8,
    type_symbol: Option<u16>,
    block_length: Option<u32>,
) -> B3bSwitchResult;
```

All fields are crate-visible only to permit the exact logical snapshot handoff.
Kind values are E1's `0 Literal`, `1 Command`, `2 Distance`; other values are
excluded by the checked precondition. `B3bSwitchState::valid` is exactly the
existing `BlockSwitchCore::valid` invariant: all three declarations are
`1..=256`; current ring entries are below their declared counts; previous ring
entries obey the existing one-type exception; `AwaitLength` has a valid kind
and block type with zero remaining length for that kind; and `Failed` contains
one listed failure. A `Ready` call additionally requires zero remaining length
for `requested_kind`. `brotli_input.rs` validates the serialized snapshot and
maps any violation to E1 `InternalState` before calling the adapter; corrupt
serialized state never becomes B2 `InvalidDeclaration` or an attacker format
error. Failure variants follow the existing B2
declaration order and map to E1 exactly. The adapter validates/restores the
existing private `BlockSwitchCore`, invokes its unchanged transition, and
exports the exact next snapshot and result. A `Failed` input state is sticky.
No workspace access or tag serialization occurs in `brotli_block.rs`;
`brotli_input.rs` alone maps snapshots to E1 bytes.

Installed-tree symbol decoding remains input-module-private:

```rust
enum InstalledSymbolStatus {
    NeedInput,
    Symbol(u16),
    Truncated,
    InvalidPrefixCode,
    InternalState,
}

struct InstalledSymbolStep {
    consumed: usize,
    status: InstalledSymbolStatus,
}

fn advance_installed_tree_symbol(
    workspace: &[u8],
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    meta: TreeMetadata,
    queue: &mut BitQueue,
    prefix: &mut InstalledPrefixState,
    input: &[u8],
    end_of_input: bool,
) -> InstalledSymbolStep;

struct InstalledPrefixState { width: u8, bits: u16, scan: u16 }
```

The prefix state is exactly E1 bytes 115 and 122..126. Its call-boundary
invariant is `width <= 14`, `bits < 1 << width`, and `scan == 0`; initial state
is `{width:0, bits:0, scan:0}`. Scan is a bounded within-call cursor over the
current width and returns to zero before any result.

Input first requires `meta.valid_for(region)` and either
`Single { symbol }` or fully initialized
`Canonical { initialized == symbols }`. `Unused`, incomplete canonical metadata
or an impossible record read maps to `InternalState` before or within the
helper. `Single` additionally requires the prefix to equal its initial
`{width:0, bits:0, scan:0}` value; input validates this relation and maps a
noninitial Single prefix to `InternalState`. A valid `Single` returns its symbol
with `consumed=0`, queue unchanged, prefix initial, and no bit or record read.

For a canonical tree the helper reads one bit at a time, linearly scans
`0..meta.symbols` at each width, ignores canonical zero-length records, and
compares raw LSB-first bits with the width-reversed stored natural canonical
code. `InstalledSymbolStep.consumed <= input.len()`. `NeedInput` implies
nonfinal input and `consumed == input.len()`; it preserves the exact **advanced**
queue/prefix produced by all consumed input, with no reset or loss. A symbol
resets prefix to its initial value and leaves exact unread queue bits. Final
exhaustion is `Truncated`; no match after width 15 is `InvalidPrefixCode`; both
are terminal and reset the prefix. `InternalState` maps to E1 terminal
`InternalState`. The helper uses the existing crate-private tree-record read
helper and adds no prefix-module API.

E2 also authorizes refactoring names and signatures of other
`brotli_input.rs`-private executable helpers without repeated architectural
approval only when all of these remain true:

- the helper is not callable from another module or public API;
- it introduces no persistent Rust field or shadow state;
- it reads/writes only the exact W1/E1 scalar bytes assigned to its logical
  state, through exact framed accessors;
- it refines the already-approved B1/B2/B3a or W1/E1 transition contract; and
- it does not change statuses, effects, work accounting, dependencies, tools,
  component ownership or trust boundaries.

Any cross-module helper, persistent field, changed byte ownership or changed
contract remains a new architectural decision.

Approval of **Candidate E2 as written** authorizes only this narrow B2 snapshot
adapter, the exact input-local installed-tree decoder, and the bounded
input-local helper-refactoring rule. It does not approve changes to existing B2
semantics, public APIs, workspace layout, dependencies, tools, trust, B3c/B4 or
support claims.
