# Checked Brotli B1 input/header component

B1 is a private foundation for later streaming Brotli work. It is **not a
complete decoder and is not advertised as supported Brotli**. Its exact scope
was approved in [BROTLI_PROPOSAL.md](BROTLI_PROPOSAL.md).

The component uses initialized `[u8; 8]` pending storage, a valid-byte count
and leading bit offset. The same annotated source is checked and compiled.
It adds no public API, normal dependency, unsafe code, heap allocation, I/O or
new trusted proof component. The five existing public routines and their
specifications remain source-identical to the measured G revision.

## Checked guarantees

- Constructor/reset and every reader transition preserve pending length at
  most eight, offset and initialized-access invariants. Every append checks
  actual remaining capacity.
- Reads of every width from 0 through 56 consume the minimal number of supplied
  bytes required for that field. Incomplete fields consume no field bits;
  accepted pending bytes are retained exactly once.
- Returned little-endian values and remaining bits equal the mathematical bit
  sequence. Extraction, byte compaction and changing field widths do not lose,
  duplicate or replace bits.
- For every possible first byte, the header driver returns RFC 7932's normal
  window bits and `2^WBITS - 16`, rejects the reserved pattern, consumes exactly
  one byte and retains any payload bits in that byte. Additional whole bytes
  are left with the caller.
- Empty nonfinal input returns genuine `NeedInput` without changing the
  abstract initial state. Empty final input returns terminal `Truncated`.
  Complete and failed states are sticky across every later call until explicit
  reset, consuming zero bytes and appending nothing.
- Header results and valid retained bits are independent of unused bytes in
  the pending array. This is a prior-storage confidentiality property, not a
  timing/cache theorem.
- Checked ghost accounting bounds each field by seven byte appends, 56 bit
  extraction steps and eight compacted bytes. The header makes at most three
  straight-line field reads. These are source operations, not CPU cycles.

The current whole crate passes **122 verification checks with zero errors**
under `--no-cheating`. [Raw checker JSON](evidence/brotli-b1-verification.json)
retains per-function results and tool metadata. Four runtime groups cover every
first byte, empty/final calls, terminal retries/reset, every width/split,
changing widths and distinct old storage. All pre-existing release tests and
the pinned upstream comparison/replay test pass.

## Deliberate-defect controls

After a 122-check unchanged positive control, the current suite requires proof
rejection of all eleven earlier defects plus five B1 defects:

1. Write the appended byte one position too far.
2. Consume one extra retained bit.
3. Use the wrong Brotli window gap.
4. Turn the reserved invalid header into retryable input exhaustion.
5. Read/append input after a terminal failure.

[The normalized control record](evidence/brotli-b1-controls.json) retains each
actual proof diagnostic. Compilation/tool/type failures do not count as proof
rejection.

## Boundaries

B1 has no meta-block, prefix-code, context-map, block-switch, LZ77, dictionary,
output or complete-stream implementation. It therefore does not reach the
actual CVE-2026-111497 invalid-block-switch path and supplies no historical
exploit replay. A one-byte header result cannot stand in for arbitrary decoder
chunking. The exact next decisions are in
[BROTLI_STREAMING_PROPOSAL.md](BROTLI_STREAMING_PROPOSAL.md).

There is no B1 throughput claim: this private component is not on any existing
public routine's path. Historical G benchmarks remain tied to their measured
revision. Exact existing executable functions and public specifications are
source-identical, which bridges their behavior contracts but is not a verified
compiler theorem.

RFC interpretation has not received independent specification review. Verus,
Z3, modeled Rust/vstd operations, Rust/LLVM, OS and hardware remain in the
documented trusted boundary. Independent specification review of this
component's threat model remains pending.
