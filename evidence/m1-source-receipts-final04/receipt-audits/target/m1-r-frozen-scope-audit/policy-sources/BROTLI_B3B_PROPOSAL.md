# B3b compressed-header, tree-group, and context-map decision proposal

Status: the human approved Candidate W1 exactly as written on 2026-10-26. The
approved B3 architecture fixes the outer workspace regions, capacities,
algorithms, public API, dependency set and proof trust boundary. This approval
additionally fixes W1's private orchestration boundary, four-byte metadata
encoding, block-metadata order, scalar-state byte layout, inverse-MTF
representation and RFC context-tree coverage mechanism. Alternative R1 and all
other listed alternatives remain unapproved.

Implementation audit found that W1 did not enumerate every serialized tag,
error mapping, reset value, complete result field, work formula or helper
signature. The human approved exact Candidate E1 in
[BROTLI_B3B_W1_ADDENDUM.md](BROTLI_B3B_W1_ADDENDUM.md) on 2026-10-26.

## Frozen format order and bounds

The pinned normal-window format processes a compressed meta-block header in
this order:

1. Read literal, command and distance block-type counts with the RFC variable
   byte integer, then add one. Each result is in `1..=256`.
2. For each count above one, read a block-type tree with alphabet
   `num_types + 2`, a 26-symbol block-length tree, and the initial block length.
   A one-type category has no block trees and starts with remaining length
   `1 << 24`.
3. Read two distance-postfix bits and four direct-distance bits. The direct
   count is `upper_four << postfix`; the normal-window distance alphabet is
   `16 + direct + (24 << (postfix + 1))`, at most 520.
4. Read one two-bit literal context mode per literal block type.
5. Decode the literal context map of `64 * literal_block_types` bytes and the
   distance context map of `4 * distance_block_types` bytes.
6. Decode literal, command and distance tree groups in that order. Their tree
   counts and alphabets are respectively `(literal_map_trees, 256)`,
   `(command_block_types, 704)` and `(distance_map_trees, distance_alphabet)`.
7. Select the initial literal, command and distance trees and enter command
   processing.

The references are RFC 7932 sections 7 and 9.2 and the pinned google/brotli
v1.2.1 sources `c/dec/decode.c`, `c/dec/state.h` and
`c/common/constants.h` under `target/r1/current`.

## Candidate W1: workspace-serialized B3b state

Candidate W1 keeps every mutable B3b parse value in the approved caller-owned
state region. A crate-private `CompressedMetaBlockDecoder<'w>` holds only the
workspace borrow and immutable workspace-window size. Its exact interface is:

```rust
struct CompressedMetaBlockDecoder<'w> { /* private workspace borrow/config */ }

struct CompressedHeaderStep {
    consumed: usize,
    status: CompressedHeaderStatus,
}

enum CompressedHeaderStatus {
    NeedInput,
    Complete(CompressedHeader),
    Failed(CompressedHeaderError),
}

impl<'w> CompressedMetaBlockDecoder<'w> {
    fn from_meta(
        workspace: &'w mut [u8],
        window_bytes: u32,
        meta: MetaBlockDecoder,
    ) -> Result<Self, CompressedHeaderError>;

    fn step(&mut self, input: &[u8], end_of_input: bool)
        -> CompressedHeaderStep;
}
```

`CompressedHeader` contains the three block counts, initial block lengths,
distance postfix/direct counts, distance alphabet size, literal/distance map
tree counts and active initialized lengths. It contains no pointer or view into
uninitialized workspace. `NeedInput`, `Complete` and `Failed` are sticky under
the same retained-bit rules already checked in B1/B3a. The final public B3 core
will own this private component; no public API changes.

### W1 metadata encoding and record order

Every four-byte metadata record is:

```text
bytes 0..2: symbols, little-endian u16
bytes 2..4: descriptor, little-endian u16
```

The only canonical encodings are:

- `(symbols=0, descriptor=0)` for `Unused`;
- `symbols>0` and `descriptor=0x8000 | symbol`, with `symbol < symbols`, for
  `Single`; and
- `symbols>0`, descriptor bit 15 clear, and
  `descriptor=initialized <= symbols` for `Canonical`.

All other bit patterns are rejected and never interpreted. W1 orders the six
block records as three block-type records followed by three block-length
records, each internally ordered literal, command, distance. The exact state
subregions, relative to fixed scratch, are:

| Offset | Bytes | Records |
|---:|---:|---|
| 1,160,176 | 1,024 | 256 literal tree metadata |
| 1,161,200 | 1,024 | 256 command tree metadata |
| 1,162,224 | 1,024 | 256 distance tree metadata |
| 1,163,248 | 12 | literal/command/distance block-type metadata |
| 1,163,260 | 12 | literal/command/distance block-length metadata |
| 1,163,272 | 4 | temporary context-tree metadata |

Accessors accept only canonical encodings, require initialized records before
reads, and prove exact byte frames.

### W1 scalar state block

W1 allocates the next 256 bytes, beginning at scratch offset 1,163,276, as the
B3b scalar block. Construction and reset initialize all 256 bytes and charge
all writes. Multi-byte values are little-endian. Tag values follow the listed
phase order; unlisted tag values are permanent internal-state errors.

| Relative bytes | Field |
|---:|---|
| 0..8 | retained bit-queue bytes |
| 8 | retained byte count |
| 9 | retained leading-bit offset |
| 10 | outer phase |
| 11 | terminal error tag |
| 12 | current literal/command/distance kind |
| 13 | variable-integer phase |
| 14 | variable-integer width |
| 15 | context-map phase |
| 16..22 | three `u16` block counts |
| 22..34 | three `u32` initial block lengths |
| 34 | distance postfix bits |
| 35 | current context-map kind |
| 36..38 | direct-distance count |
| 38..40 | literal-map tree count |
| 40..42 | distance-map tree count |
| 42..44 | current map tree count |
| 44..46 | current map size |
| 46..48 | context-map index |
| 48..50 | initialized context-map prefix |
| 50..52 | initialized context-mode prefix |
| 52 | maximum zero-run prefix |
| 53 | pending zero-run symbol; `0xff` means none |
| 54 | current tree-group kind |
| 55 | tree-group phase |
| 56..58 | tree index within group |
| 58..60 | tree count within group |
| 60 | code-description phase |
| 61 | code-description auxiliary phase |
| 62 | simple selector |
| 63 | simple symbol count |
| 64 | code-description index |
| 65 | code-description width |
| 66 | auxiliary skip |
| 67 | auxiliary index |
| 68 | auxiliary 32-unit space |
| 69 | auxiliary nonzero count |
| 70 | final previous code length |
| 71 | final repeated code length |
| 72..74 | final symbol index |
| 74..78 | chained-repeat value |
| 78..82 | final 32,768-unit space |
| 82 | final prefix bits |
| 83 | final prefix width |
| 84 | auxiliary singleton or 18 |
| 85 | code-description error tag |
| 86..94 | four simple `u16` symbols |
| 94..112 | eighteen auxiliary code lengths |
| 112..114 | initialized builder lengths |
| 114 | active tree region |
| 115 | installed-tree prefix width |
| 116..118 | active tree index |
| 118..120 | alphabet maximum |
| 120..122 | alphabet limit |
| 122..124 | installed-tree prefix bits |
| 124..126 | installed-tree scan index |
| 126 | block-length phase |
| 127 | block-length symbol |
| 128 | block-length suffix width |
| 129 | checked block-switch phase |
| 130..134 | block-length suffix value |
| 134..146 | six `u16` block-type ring entries |
| 146..158 | three `u32` remaining block lengths |
| 158 | checked block-switch kind |
| 159 | MTF upper bound in four-byte groups |
| 160..162 | pending resolved block type |
| 162..164 | RFC coverage-scan index |
| 164..166 | RFC expected tree count |
| 166..168 | active literal tree |
| 168..170 | active command tree |
| 170..172 | active distance tree |
| 172..174 | detailed permanent-error code |
| 174..256 | checked padding, initialized but never read |

The remaining 13,028 state bytes are reserved and unread until an approved B3c
layout assigns them.

### W1 context storage and initialized ranges

Literal map byte `(block, context)` is at
`LITERAL_CONTEXT_MAP_OFFSET + 64 * block + context`. Distance map byte
`(block, context)` is at `DISTANCE_CONTEXT_MAP_OFFSET + 4 * block + context`.
Literal context mode `block` is at `LITERAL_CONTEXT_MODES_OFFSET + block`.

Nontrivial maps write sequentially and use the state block's initialized prefix
as the only read authority. A one-tree map writes zero to every active byte and
consumes no RLE, temporary-tree or MTF field. Inactive capacity is left intact
and never read. Mode/map accessors prove value bounds, initialized reads and
exact frames.

### W1 context-map algorithm

Tree count uses the existing RFC variable byte integer plus one. For more than
one tree, RLE prefix zero consumes one bit; a one consumes four additional bits
and yields `1..=16`. The temporary tree alphabet is
`num_htrees + max_rle_prefix`, at most 272, and uses the approved B3a builder
and temporary tree records.

The map decoder writes exactly the active map size:

- symbol zero writes one zero;
- symbol `1..=max_rle_prefix` reads exactly that many suffix bits and writes
  `(1 << symbol) + suffix` zeroes, rejecting only expansion beyond the map; and
- a larger symbol writes `symbol - max_rle_prefix`, which must be below
  `num_htrees`.

Final exhaustion at any required field is `Truncated`; nonfinal exhaustion
preserves the exact partial phase and is `NeedInput`; malformed trees, repeat
overflow and invalid values are permanent. Terminal states read and write
nothing further.

### W1 inverse MTF and resource granularity

W1 uses the source-linked 260-byte representation: four scratch bytes followed
by the 256-byte list. `mtf_upper_bound` is state byte 159. It starts at 63,
reinitializes the list in four-byte groups through that bound, then applies the
RFC inverse transform and stores the new `OR(ranks) >> 2` bound.

The transform is one bounded internal phase after the complete map and MTF bit.
It has no input suspension. B3b proves its source-work formula. B3c must charge
the complete formula before the first MTF write; insufficient budget therefore
returns terminal `ResourceLimit` before changing the map or list. This avoids a
new partially shifted MTF state while preserving the approved per-action work
ledger.

### W1 RFC tree-coverage check

RFC 7932 requires the transformed map to contain every value in
`0..num_htrees`. The pinned native decoder checks bounds but does not check this
coverage. W1 enforces the RFC requirement.

After the temporary tree is installed, W1 reuses the first 32 code-length
builder bytes as a 256-bit seen bitmap. It clears those bytes, scans the complete
transformed map, marks every tree index, and rejects unless exactly the first
`num_htrees` bits are present. The scan is bounded, framed and independent of
old builder storage. Native comparisons classify native acceptance of a
missing-tree map as an intentional strict RFC rejection, not equivalence.

### W1 B3a/B2 handoff

One owner drains every B3a pending span into sequential builder bytes before it
advances the parser. It installs simple trees with the RFC length shapes and
fills every other admitted symbol with a zero-length record. It installs complex
trees only after all spans and exact code space complete. No next tree starts
until the previous destination metadata is fully initialized.

The checked B2 block-switch state uses the serialized block counts, six ring
entries and three remaining lengths. Its permanent failure propagates to the
outer terminal state unchanged. Initial tree selections are derived only after
both context maps and all three tree groups are complete.

## Alternative R1: Rust-struct scalar state

Alternative R1 keeps the same metadata encoding, algorithms and map regions but
stores the bit queue, phases, counters and partial fields as ordinary private
Rust struct fields. The 13,284-byte state tail remains unassigned beyond
metadata. This is simpler and avoids serialization accessors, but it changes the
approved caller-memory accounting and source-observation boundary: the public
decoder object gains persistent storage outside the caller workspace. It would
need a revised memory contract and separate old-object-state confidentiality
proofs.

## Other decision alternatives

- Interleaving type/length block metadata by category changes the six record
  addresses but not capacity.
- A direct `[256-byte list][four progress bytes]` MTF layout is easier to read
  but differs from the pinned representation and needs incremental-transform
  state or full reinitialization.
- An incremental MTF transform can fail a resource budget between cell moves,
  but requires persisted map/rank/value/shift cursors and a documented partial
  internal map effect.
- RFC coverage can use a repeated bounded scan without bitmap storage, trading
  no builder reuse for up to `256 * map_size` comparisons.

None of these alternatives is selected by this proposal.

## Evidence and deliberate defects after approval

The positive control remains whole-crate `--no-cheating` verification. Focused
defects must be rejected for: block-count `+1`; category order; one-type tree
elision; initial block length; distance mask/shift; metadata tag/order; inactive
metadata reads; literal/distance map stride; tree-count `+1`; RLE prefix width;
direct-value adjustment; exact-fill versus overflow; chunk suspension after an
RLE symbol; temporary-tree initialization; raw/canonical bit reversal; span
duplication; tree-group order/count; inverse-MTF flag/list/shift; missing RFC
coverage; stale map/MTF storage; truncation versus `NeedInput`; sticky failure;
and propagation of the integrated B2 block-switch failure.

Runtime comparisons cover trivial and nontrivial maps, every RLE prefix,
zero/direct/repeat entries, exact-fill and overflow, MTF and no-MTF, missing
coverage, whole input, every split and one-byte chunks. Finite comparison does
not replace the checked transition contracts.

## Exact approval requested

The human may approve **Candidate W1 as written**, select **Alternative R1**, or
specify changes to any named decision. Approval of W1 would authorize only the
private component/API, metadata encoding/order, 256-byte B3b state block,
initialized-range policy, upstream-layout atomic MTF, builder-bitmap RFC
coverage, B3a/B2 handoff and listed proof/comparison work. It would not approve
B3c, change dependencies/tools/trust, adopt a security profile, or advertise a
complete/supported Brotli decoder.
