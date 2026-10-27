# Checked Brotli B3b compressed-header orchestration

This report records the checked private B3b component implemented under the
approved W1, E1 and E2 decisions. It is not a complete Brotli decoder and does
not add a supported public Brotli API.

## Checked serialized state and storage

B3b stores every persistent compressed-header value in the approved
caller-owned workspace. The checked layout covers the exact 256-byte scalar
block, four-byte metadata records, literal and distance context maps, literal
context modes, the move-to-front list and scratch cell, the coverage bitmap,
and the existing builder and tree regions. The remaining 13,028 state bytes are
reserved and unread.

Construction writes the canonical scalar image and seven `Unused` metadata
records with the exact approved write count. It preserves every byte outside
those owned regions and is atomic on error. Typed byte, `u16`, `u32`, tag,
metadata, context and tree accessors prove exact little-endian values, exact
frames and initialized-read authority. Canonical metadata cannot use the
zero-symbol encoding reserved for `Unused`; malformed initialized metadata is
distinguished from an uninitialized record.

## Checked compressed-header transitions

The checked outer state machine implements the approved RFC field order:

1. literal, command and distance block-type counts;
2. optional block-type and block-length trees plus initial block lengths;
3. distance postfix and direct-distance parameters;
4. literal context modes;
5. literal and distance context maps;
6. literal, command and distance tree groups; and
7. the initial active-tree and B2 Ready handoff.

Exact transition contracts connect serialized queue state and the consumed
input prefix to variable-integer values, stored `raw + 1` counts, one-type tree
elision and the implicit `1 << 24` length. Literal and distance map extents are
exactly `64 * literal_block_types` and `4 * distance_block_types`.

Context-map contracts cover the tree-count `+1`, one-bit RLE flag, four-bit RLE
prefix, every one-to-sixteen-bit repeat suffix, zero and direct entries,
`symbol - max_rle_prefix`, exact-fill acceptance, overflow rejection and
retained pending-run state across calls. Final exhaustion is terminal
`Truncated`; nonfinal exhaustion is `NeedInput` only after consuming the entire
supplied input, with exact serialized queue and phase retention.

Installed-tree decoding proves the earliest matching width and symbol against
the width-reversed natural canonical code. Its contract covers old-prefix bit
accumulation, exact accepted bytes and queue tail, suspended prefixes,
single-symbol zero-read behavior, invalid-prefix rejection and terminal reset.

The source-linked inverse move-to-front transform proves its exact output, list
reuse invariant and cell-work formula. The first use with bound 63 is
independent of prior list bytes. Coverage clears the exact 32-byte bitmap,
preserves the decoded map and proves the RFC requirement that every advertised
tree appears. Missing coverage is a permanent format error. This is an
intentional strict difference from the pinned native decoder, which accepts
some missing-tree maps.

Tree-group contracts bind groups zero, one and two to literal, command and
distance order; exact count and alphabet sources; sequential tree indices; and
complete destination metadata before any next tree or group begins. Pending
builder spans are written and acknowledged exactly once. Completion returns
the exact approved header fields, complete map and metadata counts, active
literal and distance selections from context zero, active command tree zero,
and the serialized B2 Ready snapshot.

Terminal errors are sticky: later calls return the same stored error, consume
zero input and leave state unchanged. The B2 adapter separately proves exact
Ready, suspended and failed transitions and exact failure mapping. B3b creates
the checked initial Ready snapshot; an exhaustion-triggered call from the body
decoder is B3c work and is not claimed here.

## Runtime and proof evidence

The current whole crate passes **738 verification checks with zero errors**
under the pinned `--no-cheating` command. Twelve B3b control suites reject
**58 unique semantic defects** with no accepted mutation or tool failure.
Controls cover layout and serialization, count and category order, field
widths, map strides, RLE and direct values, chunk suspension, temporary-tree
initialization, installed-code reversal, pending-span drain, move-to-front
state, RFC coverage, tree-group order and counts, sticky failure, stale state,
truncation classification and the E2 adapter boundary.

Five new runtime tests execute 64 scenarios:

- 16 literal/distance map and chunking cases;
- 32 RLE cases covering prefixes 1 through 16, exact fills and overflow;
- three no-MTF, MTF and missing-coverage cases;
- three exhaustion and sticky-error cases; and
- ten tree-group cases covering whole input, one-byte chunks and every byte
  split of the fixture.

These cases supplement the checked transition contracts. The pinned native
reference exposes stream acceptance and status but not its internal map, MTF or
tree-selection fields. Native internal-field comparison is therefore
unavailable. Native acceptance of a missing-tree map is recorded as the
intentional RFC-strict difference above.

See [the machine-readable evidence](evidence/brotli-b3b.json),
[the W1 decision](BROTLI_B3B_PROPOSAL.md), and
[the E1/E2 addendum](BROTLI_B3B_W1_ADDENDUM.md).

## Remaining decoder and release work

B3c must implement command, literal and distance execution; call the checked B2
adapter when a block category is exhausted; charge all approved budgets before
atomic work; maintain the LZ77 window; and implement dictionary and output
behavior. B4 must add the quarantining caller, complete-stream policy and
release security profile. Independent specification review and the
source-to-binary trust boundary also remain release requirements.

No complete-decoder, output-correctness, practical denial-of-service,
side-channel, arbitrary-composition or supported-Brotli claim follows from
B3b.
