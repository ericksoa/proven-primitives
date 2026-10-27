# B3 complete-decoder implementation proposal

Status: the human approved B3 exactly as written on 2026-10-24. B1, B2/R1, C1
and P1 are complete. This document freezes the B3 choices that were explicitly
deferred by the earlier approvals. It does not approve B4 profile adoption,
independent review, a service, CI, crate publication, new dependencies, or a
changed proof trust boundary.

Implementation status: the B3a components are checked: the fixed
workspace/tree-record layout, source-linked meta-block-header state machine,
all simple code descriptions, the complex auxiliary code-length alphabet, RFC
repeat-coded final symbol lengths, and canonical installation from the fixed
builder region. Their internal handoff is specified; tree-group orchestration
begins in B3b. The human approved exact B3b Candidate W1 on 2026-10-26; its
metadata, state, MTF, coverage and handoff decisions are fixed in
[BROTLI_B3B_PROPOSAL.md](BROTLI_B3B_PROPOSAL.md). See
[BROTLI_B3A.md](BROTLI_B3A.md). B3b is now checked through compressed-header
orchestration, context maps, tree groups and the initial B2 `Ready` handoff; see
[BROTLI_B3B.md](BROTLI_B3B.md). The concrete body/resource/layout decisions for
B3c are pending in [BROTLI_B3C_PROPOSAL.md](BROTLI_B3C_PROPOSAL.md).

## Supported format and public API

Implement the already-approved `RequestLimits`, `RequestBudget`,
`BrotliDecoder`, `Step`, `Status`, `StreamError` and `InitError` API in
[BROTLI_STREAMING_PROPOSAL.md](BROTLI_STREAMING_PROPOSAL.md). The supported
format is RFC 7932 normal-window Brotli with window bits 10 through 24,
compressed, uncompressed and metadata meta-blocks, standard context maps,
canonical prefix codes, overlapping LZ77 copies and the standard static
dictionary/transforms.

Large-window extensions and external/shared dictionaries return
`UnsupportedMode`. Arbitrary malformed bytes remain admitted and return a
specified permanent result; the implementation must not narrow its contract to
well-formed streams. B3 exposes incremental provisional prefixes exactly as
already approved. Complete-message publication remains the B4 quarantining
caller obligation.

## Exact immutable dictionary decision

Embed the RFC dictionary bytes and transforms from google/brotli v1.2.1 commit
`db24a98aed38a16de78cc05ca15cdd8dc2a0d92d`, already approved as R1's current
reference. No build-time generator or new package is used.

| Item | Exact identity |
|---|---|
| Decoded dictionary | 122,784 bytes; SHA-256 `20e42eb1b511c21806d4d227d07e5dd06877d8ce7b3a817f378f313653f35c70` |
| Upstream byte source | `c/common/dictionary_inc.h`; 470,432 bytes; SHA-256 `55b98973df9dcb353bd78b2b573fb7338ab55d98fb5571ad93939095978768e8` |
| Dictionary metadata | `c/common/dictionary.c`; SHA-256 `0890056e4ae595efab6bbf3bf1fd244332e2cfad3adcb9f5793ee29a8f3a18c5` |
| Transform source | `c/common/transform.c`; SHA-256 `47f229a79c3542ea57ec07145d7eaf77300a02816d95695332f9911ea19d6ab3` |
| License | google/brotli `LICENSE`; SHA-256 `3d180008e36922a4e8daec11c34c7af264fed5962d07924aea928c38e8663c94` |

Commit the decoded byte array, dictionary length/offset metadata and transform
tables as immutable Rust constants with source/hash comments and MIT attribution
in `THIRD_PARTY_NOTICES.md`. A generation script may be retained as review
evidence but is not part of the build. Tests compare every committed data byte
and transform result against the pinned native reference; checked index and
transform contracts remain the universal evidence.

## Exact caller-workspace layout

Construction requires at least

```text
(1 << limits.max_window_bits) + 1,176,560 bytes
```

of caller-owned workspace. The first power-of-two region is the circular LZ77
window. The actual stream history limit is `(1 << stream_window_bits) - 16` and
must not exceed the approved request maximum. The remaining fixed scratch is a
byte-addressed layout so safe Rust does not reinterpret a byte slice as typed
memory:

| Offset | Bytes | Region |
|---:|---:|---|
| 0 | 196,608 | 256 literal trees × 256 symbols × 3-byte record |
| 196,608 | 540,672 | 256 command trees × 704 symbols × 3-byte record |
| 737,280 | 399,360 | 256 normal-window distance trees × 520 symbols × 3-byte record |
| 1,136,640 | 16,384 | literal context map: 256 block types × 64 contexts |
| 1,153,024 | 1,024 | distance context map: 256 block types × 4 contexts |
| 1,154,048 | 256 | literal context modes |
| 1,154,304 | 2,322 | three block-type trees × 258 symbols × 3 bytes |
| 1,156,626 | 234 | three block-length trees × 26 symbols × 3 bytes |
| 1,156,860 | 3,056 | bounded code-length builder and temporary context-map tree |
| 1,159,916 | 260 | inverse move-to-front state |
| 1,160,176 | 16,384 | per-tree metadata plus explicit resumable parse/command state slots |
| **Total** | **1,176,560** | fixed scratch below the approved 2,097,152-byte ceiling |

The maxima come from the pinned normal-window format: 256 block/tree types,
256 literal symbols, 704 command symbols, and at most
`16 + 120 + (24 << 4) = 520` distance symbols. Literal and distance context
maps have at most `256 × 64` and `256 × 4` entries. These limits are normative
B3 constants; encountering an extended alphabet is `UnsupportedMode`, not an
unchecked enlargement.

Each tree record is `length: u8` followed by canonical `code: u16` in little
endian. The builder region contains 704 code-length bytes, 16 two-byte counts,
16 four-byte next-code entries, 720 two-byte symbol-chain entries, and one
272-symbol temporary context-map tree. The state region begins with 768
four-byte literal/command/distance tree metadata records, six four-byte block
tree metadata records and one four-byte temporary-tree record; the remaining
13,284 bytes hold explicitly enumerated resumable scalar/partial states and
checked padding. Tree metadata distinguishes unused zero-length entries from a
valid single-symbol zero-bit tree. Every accessor checks region, tree, symbol
and byte offsets before
reading or writing. The decoder tracks initialized ranges; construction does
not read or publish old workspace bytes and need not clear the complete
allocation. Layout constants and non-overlap/total-size theorems are checked.
If this layout proves insufficient, implementation stops for another human
decision rather than enlarging it or omitting an RFC case.

## Exact decoding algorithms

1. **Bits and suspension:** extend B1's eight-byte queue. Every partial field,
   code-length repeat, context map, command and copy has an explicit phase.
   Input exhaustion is returned only for a viable unfinished prefix. EOF makes
   an incomplete required field terminal `Truncated`.
2. **Prefix codes:** extend B2 to parse RFC simple and complex code descriptions.
   Store the three-byte canonical records above. Decode bit-by-bit through width
   1..15 and linearly scan the selected bounded tree at each width. No speculative
   table or unchecked fast path is introduced in B3.
3. **Context maps:** implement RFC run-length decoding and inverse move-to-front
   using the fixed regions. Counts, indices and every repeated span are checked.
4. **Commands and lengths:** use explicit RFC insert/copy/distance tables frozen
   from the same reference. Literal, command and distance exhaustion calls the
   checked B2 switch transition; its permanent result propagates unchanged.
5. **LZ77 window:** use a power-of-two circular byte window, with `history_len`
   bounded by the selected `(2^WBITS - 16)` limit. Reject zero, beyond-history
   and beyond-window distances. Copy one byte at a time from previously produced
   history, then write it to both the provisional output and window; this gives
   the RFC overlapping-copy behavior without unsafe code.
6. **Dictionary:** calculate word length/index/transform with checked arithmetic,
   prove every immutable-data access in range, and emit transformed bytes through
   the same bounded output/window path.
7. **Uncompressed/metadata/final padding:** copy or skip incrementally with
   explicit remaining counts. Validate required padding and reject unexpected
   trailing bytes under the one-message policy at the verified B4 caller.

The implementation remains safe Rust, bounded loops, no executable recursion,
no heap allocation and no I/O. It uses the existing Rust/Verus stack and adds no
Cargo dependency or proof assumption.

## Exact resource charging

`RequestBudget` charges before each atomic source action:

- one input credit per byte accepted into parser state;
- one output credit per provisional byte produced;
- one work credit per bit inspected, prefix record visited, context/MTF cell
  visited, immutable dictionary byte read, state transition, input byte read,
  window byte read/write and caller-output byte write;
- one call credit on entry to every `step`, including immediately rejected
  calls; and one initialization credit for construction or reset.

Multi-action byte emission therefore charges its separate read/write actions.
No chunk boundary, retry, empty call, error or reset mints credits. Insufficient
credit returns terminal `ResourceLimit` before the unpaid atomic action; earlier
provisional output and window state remain documented prior effects. All counter
arithmetic is checked. Per-call termination and cumulative request bounds are
proved; wall-clock availability still needs B4 deployment assumptions.

## Implementation and evidence order

1. B3a: meta-block headers, simple/complex code descriptions, checked layout and
   deliberate malformed-code controls. The layout, meta-header, all simple
   descriptions, complex auxiliary alphabet, repeat-coded final lengths and
   canonical builder installation are checked.
2. B3b: tree groups, context maps and all literal/command/distance transitions,
   including integrated CVE-status corruption controls.
3. B3c: literals, commands, LZ77, dictionary/transforms, metadata,
   uncompressed blocks, output backpressure and cumulative resource charging.
4. B3d: arbitrary permitted call-sequence induction, complete supported-format
   refinement, source-observation independence from old workspace, complete
   runtime corpus comparisons and repeated benchmarks.

Each stage first passes an unchanged whole-crate positive control, then actual
proof rejection of its frozen-contract defects. R1 comparisons cover valid
RFC/dictionary/overlap streams; malformed/truncated streams; zero/small output;
empty, one-byte and every fixture split; retries, EOF, reset and limits. The
Node witness must reach the Rust integrated path and remain permanently failed
without exposing a complete message. Finite comparisons do not replace proofs.

## Allowed claim and remaining gate

Even a completed B3 is a **complete decoder implementation with checked B3
contracts**, not “supported Brotli under PP-Security/1.0.0.” B4 still requires
the exact quarantining caller, approved normative profile/applicability matrix,
independent specification review, source-observation disposition, complete P1
release manifest and explicit support decision. Rust/LLVM, Verus/Z3, modeled
Rust operations, OS and hardware remain trusted as documented.
The concrete B4 caller/profile design is in
[BROTLI_B4_PROFILE_PROPOSAL.md](BROTLI_B4_PROFILE_PROPOSAL.md).

## Approval requested

Approval of B3 authorizes the exact immutable data identities, workspace size
and offsets, three-byte tree representation, bit-by-bit/linear-scan prefix
algorithm, bytewise circular LZ77 algorithm, dictionary/context/meta-block
algorithms, resource charges, staged implementation and R1 comparisons above.
It does not approve B4/profile adoption, new dependencies/tools/services or any
change to the proof trust boundary.
