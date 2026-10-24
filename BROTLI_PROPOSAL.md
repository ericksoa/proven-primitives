# Brotli implementation: first approval decision

Status: the human explicitly approved **B1 as written** on 2026-10-24. Later
milestones remain proposals requiring approval under [AGENTS.md](AGENTS.md). The
implemented B1 result and its exact limits are in [BROTLI_B1.md](BROTLI_B1.md).

## Evidence gathered

- [RFC 7932](https://www.rfc-editor.org/rfc/rfc7932.html) defines the format.
  Section 9.1 encodes window bits from 10 through 24 in one through seven
  bits, reserves one invalid pattern, and defines the window as
  `2^WBITS - 16`. Section 12 calls for bounds checking and resource policies
  based on window, meta-block and total decoded sizes.
- [Node's disclosure](https://nodejs.org/en/blog/vulnerability/october-2026-security-releases#nodejs-brotli-decoder-out-of-bounds-write-permits-remote-code-execution-cve-2026-111497---high)
  identifies permanent-error/input-exhaustion confusion followed by overflow
  of an eight-byte pending buffer across streaming retries.
- [The upstream fix](https://github.com/google/brotli/commit/0ed4268a4401abcb4472096340477cf4af7d1a2b)
  is `0ed4268a4401abcb4472096340477cf4af7d1a2b`, committed
  2026-02-27; its parent is `34f020fa9daba975747b29885314c2545b7aa040`.
  It replaces a boolean block-switch result with explicit success,
  exhaustion and format-error outcomes and propagates them through callers.
  Only the decoder and its public error header change in that commit; it
  does not include a regression fixture. No project exploit replay is claimed.
- In the fixed decoder, [the block-switch check](https://github.com/google/brotli/blob/0ed4268a4401abcb4472096340477cf4af7d1a2b/c/dec/decode.c#L1189)
  rejects a switch when the block-type count is at most one.
  [The retry path](https://github.com/google/brotli/blob/0ed4268a4401abcb4472096340477cf4af7d1a2b/c/dec/decode.c#L2471)
  appends to pending storage after exhaustion. Our future implementation
  must establish capacity at the actual write as well as prove status meaning.
- [Envoy's advisory](https://github.com/envoyproxy/envoy/security/advisories/GHSA-3wvj-j6qm-62mr)
  confirms deployment impact. Upstream's latest release observed during this
  research was [v1.2.1](https://github.com/google/brotli/releases/tag/v1.2.1),
  published 2026-10-21. Reading it does not approve adding a comparison dependency.

## B1: approved first implementation milestone

The approval covers **only** the private input/header core described below. This gives us
real format parsing and checked cross-call state before building the much
larger decoder. It would not be advertised as a Brotli decompressor or as a
proof that the block-switch CVE has been excluded from a complete decoder.

### Integration and unchanged foundations

Add a crate-private `brotli_input` module to the existing Rust library, with
implementation and proof bodies together in `src/brotli_input.rs`. It is
checked as part of the whole crate. There is no exported Brotli API at B1.

Use the existing Rust 1.99.1 / Verus 0.2026.10.18.7d82994 / locked `vstd`
stack, safe Rust, bounded loops, no executable recursion or heap allocation.
Use the existing standard-library test and deliberate-defect approach.
Do not add dependencies, native reference builds, FFI, another verifier,
new assumptions or external proof bodies. Existing five APIs and their
contracts remain unchanged.

### Concrete private representation and operations

The proposed representation uses an initialized `[u8; 8]` pending array,
a valid-byte count `0..=8`, and a leading consumed-bit offset `0..=7`.
An empty queue has offset zero. A mathematical ghost sequence represents
exactly the unread authorized bits; unused array bytes are excluded from it.
Fields are private and valid executable states originate from the constructor
or proved transitions, rather than arbitrary forged representations.

The internal `read_bits(width, input, end_of_input)` operation handles widths
`0..=56`, with its width precondition checked at every call site. It returns
consumed input bytes and either a value, genuine input exhaustion, or terminal
truncation. Its bounded algorithm appends only enough bytes for the requested
field, checks capacity before each append, assembles only valid bytes into
little-endian bits in a `u64`, and compacts only retained valid bytes after
consuming a field.
The shift and mask bounds must be proved. No field bits are consumed on an
incomplete field; accepted pending bytes are retained and counted exactly once.
Changing field width between calls still obeys this bit-queue contract.

The private header driver owns that queue and the following phases:

- `ReadingWindow`: parse the exact RFC window-header grammar, retaining its
  subphase across calls.
- `Complete { window_bits, window_size }`: a terminal header result; any bits
  already read from its final byte but belonging to the payload remain in
  the queue. Whole payload bytes not needed for the header remain unconsumed.
- `Failed { InvalidHeader | Truncated }`: a terminal error.

`advance_header(input, end_of_input)` returns a fresh consumed count and one
of `NeedInput`, `Complete`, or `Failed`. It produces no decompressed bytes.
`end_of_input` means no further bytes follow the supplied final chunk; an
incomplete header after consuming that chunk is `Truncated`, not `NeedInput`.
It does not require consumption of payload bytes after a completed header.
Once complete or failed, further driver calls return the same terminal
outcome with zero consumption and no state change. `reset` constructs a new
logical stream and discards the old retained-bit interpretation.

This is a proposed private interface and state model, not an addition to the
existing public `Error` or byte-buffer APIs.
The header driver enforces terminal-call behavior. The reader is its private
subcomponent; B1 does not establish the lifecycle of a future payload decoder.

### Required B1 proofs and controls

| Obligation | Exact proposed result |
|---|---|
| Representation | Constructor establishes the bit-queue/header invariant; each permitted call and reset preserves it. Pending length never exceeds eight and every read, append, shift and compaction is safe. |
| Bit conservation | Consumed input contributes exactly its authorized bits; returned field values and retained bits refine the little-endian sequence specification. No byte or bit is lost, duplicated or replaced by unused storage. |
| Exhaustion | `NeedInput` means the current header/field is a viable incomplete prefix and all supplied input needed for it has been consumed. It cannot stand for an already detected invalid header or a full pending queue unable to make progress. |
| Error lifetime | Invalid header and end-of-input truncation are distinct terminal results. Repeated calls after failure do not append bytes or turn the result into retryable exhaustion. |
| Chunk boundaries | For any finite partition of the same header bytes, with the final-input flag applied consistently, parsed window values, accepted bits and retained payload bits agree with the concatenated-input specification. Include empty chunks, partial fields and retries. |
| Confidentiality | Header results and valid retained bits are independent of unused pending-array contents; only authorized supplied bits can influence them. This does not establish timing/cache independence. |
| Work | Record byte append/compaction operations and bit extraction iterations in ghost counters; prove bounds in terms of the fixed eight-byte queue and requested width, and a constant header-work bound. Include empty and terminal calls; do not call this a cycle or service DoS bound. |

Runtime cases cover every header encoding, the reserved invalid pattern,
all byte values for the first byte, input prefixes, empty/final chunks,
retained payload bits, terminal retries and reset. These supplement proofs.
The header fits in one byte, so it cannot by itself exercise multi-byte
input fragmentation. Reader cases separately cover widths `0..=56`, reachable
bit offsets, successive fields and splits at every byte boundary. Wider
compressed-block/Huffman fragmentation remains a later milestone.

After a passing unchanged control, deliberate defects must fail actual proof
obligations: an off-by-one append, loss of a retained bit, a wrong window
formula, classification of a known invalid header as `NeedInput`, and appending
after terminal failure. Tool/type failures do not count as proof rejection.

The completed evidence in [BROTLI_B1.md](BROTLI_B1.md) publishes exact
source/checker identities, verification results, controls and limitations.
The existing 90-check security record remains immutable historical evidence;
the current component record reports the later 122-check source.

## Later decisions, outside B1 approval

| Next scope | Decision required before implementation |
|---|---|
| Full compressed blocks | Approve exact prefix-code/Huffman, context-map and block-switch representations/algorithms, then prove their grammar and cross-call transitions. The actual invalid-block-switch rule must reach a terminal driver result before any exhaustion retry. |
| LZ77/window and dictionary | Approve caller workspace versus owned storage, supported window limits, static dictionary/transforms and licensing/source identities, and any excluded extensions or external dictionaries. RFC coverage must be labeled accurately. |
| Public streaming API | Approve consumed/produced/status semantics, backpressure, final-input/reset rules and resource-limit behavior. These are new contracts. |
| Output before a later error | Choose incremental provisional prefixes versus withholding all output until complete validation. Incremental output needs a caller acceptance policy; withholding needs storage or replay assumptions. Existing one-shot whole-buffer preservation on error does not automatically apply to streaming. |
| Practical resource protection | Approve input, output, window and work budgets, whether exhaustion yields or terminates, and whether budgets persist across calls/resets. Empty chunks and retries must not replenish a request's budget. |
| References and CVE replay | Approve exact reference versions/revisions, features, transitive packages, native build/runtime tools and replay scope. The fix/parent above are research identities, not approved executable references. |

The eventual full decoder needs a real multi-call regression, including tiny
chunks and output backpressure, plus a defect that reintroduces fatal-to-retry
confusion. A passing B1 header proof cannot substitute for that result.

Independent specification review and the source-to-binary trust boundary remain
as described in [SECURITY_CONTRACTS.md](SECURITY_CONTRACTS.md). Further security
proofs are feasible; their proposed scopes are in
[SECURITY_PROOF_EXTENSION_PROPOSAL.md](SECURITY_PROOF_EXTENSION_PROPOSAL.md).
