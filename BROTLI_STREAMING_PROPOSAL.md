# Brotli as the first evolving-profile case

Status: the human approved this document's public API, state, resource and
output model, B2, and R1 on 2026-10-24. [B1](BROTLI_PROPOSAL.md) is complete. B3
and B4 were subsequently approved in their concrete proposal documents. This
accompanies [the pipeline architecture](PIPELINE_PROPOSAL.md).

## Case and generalized obligations

Case: CVE-2026-111497. [Node's advisory](https://nodejs.org/en/blog/vulnerability/october-2026-security-releases#nodejs-brotli-decoder-out-of-bounds-write-permits-remote-code-execution-cve-2026-111497---high),
[Envoy's advisory](https://github.com/envoyproxy/envoy/security/advisories/GHSA-3wvj-j6qm-62mr)
and [the upstream fix](https://github.com/google/brotli/commit/0ed4268a4401abcb4472096340477cf4af7d1a2b)
support the mechanism: a permanent invalid block switch was represented as
input exhaustion, causing streaming retries to keep appending to bounded
pending storage. The fix propagates explicit status through block-switch callers.

Proposed reusable clause IDs, not one contract per CVE:

- `PENDING-CAPACITY`: every pending append/read/compaction fits actual storage
  in every reachable state and across all permitted calls.
- `EXHAUSTION-MEANING`: a retryable input result denotes a genuinely incomplete
  viable parse, never an established permanent format error.
- `TERMINAL-PRESERVATION`: permanent format errors remain terminal until an
  explicit permitted reset; retries cannot append or change them into exhaustion.
- `STREAM-CONSERVATION`: consumed bytes, retained bits, produced prefixes and
  caller-held remainders are neither lost, duplicated nor read from stale storage.

These refine the pending/state families in the proposed profile. New CVEs
with the same mechanism add case evidence. A stronger/new mechanism requires
human-approved normative changes and a new profile identity.

Required proof/control coverage follows literal, command and distance block
switches through actual decoder transitions. An isolated guard theorem,
one-shot output theorem or B1 header proof does not establish this integration.

## Proposed full-decoder scope, requiring approval

Implement RFC 7932 decoding with normal windows, compressed/uncompressed and
metadata meta-blocks, context maps, canonical prefix codes, LZ77 overlapping
copies and the standard static dictionary/transforms. Exclude large-window
extensions and external/shared dictionaries in this proposed first mode;
those byte streams still receive explicit unsupported/invalid-mode results,
not a promise of full extended-format compatibility. Scope differences are
part of the approved advertised format domain.

Use the existing Rust/Verus stack and the same annotated implementation for
checking and Cargo compilation. Preserve the existing public functions and
their error/buffer contracts. New streaming semantics are separate.

### Proposed API shape

The following is an interface proposal, not compiled library code:

```rust
pub struct RequestLimits {
    pub max_input: u64,
    pub max_output: u64,
    pub max_work: u64,
    pub max_calls: u64,
    pub max_initializations: u32,
    pub max_window_bits: u8,
}
pub struct RequestBudget { /* private remaining credits/counters */ }
pub struct BrotliDecoder<'w, 'b> { /* exclusive workspace and budget borrows */ }
pub struct Step { pub consumed: usize, pub produced: usize, pub status: Status }
pub enum Status {
    NeedInput, NeedOutput, Finished,
    Failed(StreamError),
}
pub enum StreamError {
    InvalidFormat, Truncated, UnsupportedMode, ResourceLimit,
}
pub enum InitError { InvalidLimits, WorkspaceTooSmall, ResourceLimit }

impl RequestBudget {
    pub fn new(limits: RequestLimits) -> Result<Self, InitError>;
}
impl<'w, 'b> BrotliDecoder<'w, 'b> {
    pub fn new(workspace: &'w mut [u8], budget: &'b mut RequestBudget)
        -> Result<Self, InitError>;
    pub fn step(&mut self, input: &[u8], output: &mut [u8], end_of_input: bool)
        -> Step;
    pub fn reset(&mut self) -> Result<(), InitError>;
}
```

No I/O occurs in this core. Caller buffers contain arbitrary initialized bytes.
The decoder uses no heap allocation. Window and parsing tables are carved from
the caller's workspace, with a proposed hard scratch ceiling of 2,097,152
bytes in addition to the selected normal window. This ceiling is a design
constraint still requiring a checked storage-layout bound; failure to fit it
requires a new human decision, not silent enlargement or omitted format cases.
`max_window_bits` must be 10 through 24. No default numeric request limits are
silently chosen; caller-supplied limits are validated, source-bound and recorded.

The proposed initial algorithm uses canonical prefix-code counts/code lengths
with bounded bit-by-bit decoding and explicit resume states, not speculative
fast lookup tables. Prefix-code arrays are bounded by their RFC alphabets;
table creation, zero-bit/single-symbol cases and malformed code lengths need
separate proofs. Static dictionary bytes/transforms must be frozen with their
source/license identities and independently reviewed before embedding them.
Their final data identities remain a B3 approval item, not an unspecified
dependency approved by accepting this API sketch.

### State and results

Proposed logical phases: header; meta-block header; prefix-code/context-map
construction; command; literal emission; distance/copy; metadata skip;
uncompressed emission; final padding; finished; failed. Each suspended phase
retains exactly its partial field/code and pending bits. Stored lengths,
table indices, window history and initialized workspace spans have checked
invariants. Bit-reader capacity remains eight bytes as in B1.

`NeedInput` requires a viable unfinished parse, exhaustion of the offered bytes
needed at that point, and no already established format error. If final input
has been fully consumed and a required field is incomplete, return terminal
`Truncated`. The end flag commits EOF only when its supplied final chunk has
actually been consumed; on output backpressure unconsumed bytes remain with
the caller and must be supplied again for the intended stream.

`NeedOutput` means output space is required to make the next justified emission;
it must not hide a known format failure. Zero-capacity outputs, empty inputs and
arbitrary chunk boundaries preserve all invariants. Progress may be input
consumption, output, or a bounded state/table transition charged to work.
Every call terminates; lack of new external input/output space may legitimately
return without stream progress. No fairness assumption is needed for safety.

`Finished` and `Failed` are sticky: further core calls consume/produce zero,
preserve their status and do not append pending bytes. Reset is explicit,
reinitializes the logical stream, consumes initialization/work credit and
never replenishes the request's budgets. Failure to pay reset costs leaves
the existing terminal state unchanged. The same borrowed budget can cover
multiple explicitly reset logical streams; constructing a new budget is a
new caller/admission decision, not an attacker-controlled refill operation.

### Output policy: a decision with compatibility consequences

The proposed core returns **incremental provisional prefixes**. On any step,
only `output[..produced]` was emitted by that step; the suffix is preserved.
The core may emit a prefix before detecting a later error, including within
the same call. It does not inherit the one-shot APIs' whole-buffer-on-error
preservation guarantee. Provisional bytes do not establish validity or
authorization of the complete message.

The proposed first verified caller holds decoded bytes in caller-owned
quarantine storage, exposes no message view until `Finished` with the intended
input exhausted, and invalidates remembered lengths on every error/limit.
It rejects unexpected trailing data for a one-message policy. It never exposes
the whole allocation, a prior request's length, or buffered bytes following a
failure. Correct use of the raw provisional API by arbitrary clients is not
proved by verifying this particular caller.

The human must explicitly approve this provisional-core/quarantined-caller
choice. The alternative is atomic withholding in the core, which requires
whole-message storage or an approved replay contract. Neither is implemented
or silently selected here.

## Resource policy and DoS target

The proposed budget persists over the request, including initialization,
all chunks, retries, errors and resets. Input/output credits charge accepted
and produced bytes; work credits charge byte reads/writes, table-cell visits,
prefix-code bit steps and decoder-state transitions. No table build, empty
metadata loop or zero-bit symbol transition is free. Memory includes window,
pending bytes, parsing tables and fixed local storage; actual stack-byte and
process-wide claims require their own bridge.

Resource exhaustion is a terminal policy result, distinct from a format error
or `NeedInput`. It never silently narrows the proved input domain: arbitrary
bytes and sizes still have a specified bounded outcome under supplied limits.
Use checked arithmetic for all credit/counter operations.

A raw API's rejection still costs entry/check overhead. Its cumulative bound
therefore has the form `charged_work + K * API_calls + K_init * init_attempts`,
with constants established in the approved accounting model. Infinite retries
cannot have a finite total CPU bound. The verified caller must enforce finite
invocation/initialization credits and stop invoking when exhausted, yielding
the finite request-wide bound. The accounting proof may not treat exhausted calls as free. No new budgets are minted by chunking, retries or reset.

Practical availability additionally assumes an approved admission/concurrency
policy, adequate host capacity and a justified mapping from charged work to
the target's execution cost. Rate limits or OS scheduling are not provided by
this library and are not proved merely by this budget theorem.

## Implementation milestones and support labels

| Milestone | Authorized now? | Required result / allowed claim |
|---|---|---|
| B1 input/header | Yes; completed | Real bit conservation, pending bounds and terminal header behavior; private verified component only |
| B2 prefix/block-switch core | Yes; implemented and checked | Canonical prefix/block-length and literal/command/distance switch component; complete byte-stream integration remains explicit and unproved |
| B3 complete decoder | Yes; in progress | Dictionary data, workspace layout and LZ77/context algorithms are approved; implement and prove the whole supported grammar and arbitrary streaming transitions. Preserve B1/B2 evidence |
| B4 caller/resources/profile | Yes; implementation pending | Checked quarantine caller, cumulative resource/call policy, source-observation obligations and independent specification review; every applicable profile clause discharged |
| Supported Brotli under V | No | Full decoder plus B4 and exact release gate pass. No helper/one-shot/component result may generate this support claim |

Approval of the API/state/resource design is distinct from approval to
implement B2; B3 data and any changed algorithms still need their exact
decisions. No full-decoder milestone receives implied approval from B1.
The approved concrete dictionary, workspace, algorithm and resource decision is
in [BROTLI_B3_PROPOSAL.md](BROTLI_B3_PROPOSAL.md).

## R1: exact proposed comparison/replay references and tools

| Role | Proposed immutable source |
|---|---|
| Current native reference | google/brotli v1.2.1, commit `db24a98aed38a16de78cc05ca15cdd8dc2a0d92d` |
| Vulnerable mechanism reference | Immediate pre-fix parent `34f020fa9daba975747b29885314c2545b7aa040` |
| Fix comparison | Commit `0ed4268a4401abcb4472096340477cf4af7d1a2b` |
| Published integration regression | nodejs/node commit `7ba22c28127e88d7ce5a207af15fff2fbca71d46`, `test/parallel/test-zlib-invalid-input.js`, blob `40958b074445ae59731b66733bf6e89e77a5e6ee` |

These identities were read from upstream, not installed or compiled. Proposed
execution is a small **test/benchmark-only C subprocess harness**, using the
native `BrotliDecoderDecompressStream` API. No Rust FFI, Rust dependency or
native implementation enters the verified library or its proof assumptions.
The human approved that exact C comparison code and build approach on
2026-10-24.

Use installed Apple Command Line Tools 27.0 / Apple Clang 21.0.0 on
`aarch64-apple-darwin`, per-command `DEVELOPER_DIR`, with upstream common/decoder
C sources and includes at each exact revision. Proposed normal flags are
`-std=c99 -O3 -DNDEBUG`; historical replay uses separate `-O1 -g
-fsanitize=address -fno-omit-frame-pointer` binaries and the installed Clang
21 ASan runtime. No CMake or other package/tool installation is proposed.
Freeze each revision's complete enumerated source/include hashes before
building; missing/unexpected inputs require review rather than fallback.

At the current reference the enumerated C inputs are `c/common/{constants,
context,dictionary,platform,shared_dictionary,transform}.c` and
`c/dec/{bit_reader,decode,huffman,prefix,state,static_init}.c`. The pre-fix
revision's own complete enumeration must be frozen separately; it may differ.
The harness receives bytes, chunk/output schedules and caps, and reports
per-step consumed/produced/status, final prefix and buffer guards. It operates
only on local fixtures. Sanitized replay measurements are never benchmark
baselines or proof results.

The fixing commit itself supplied no replay fixture. Node later published an
integration regression in [commit `7ba22c2`](https://github.com/nodejs/node/commit/7ba22c28127e88d7ce5a207af15fff2fbca71d46),
which identifies CVE-2026-111497. Its 22-byte vector is
`200010414141fcffff07002228f00b60f7f41f000000`; Node requires the one-shot
and one-byte-at-a-time streaming paths to return
`BROTLI_DECODER_ERROR_FORMAT_BLOCK_SWITCH` (`-17`) and forbids a streaming
`end` event. At that commit the complete test file is 3,660 bytes with SHA-256
`c5dfa0ac92870e26e5062bfd5e5e4c4555f1eaff75859034f19abad96e02d0ba`.
The file carries the Node-contributors permissive license header; the repository
`LICENSE` blob at that commit is `ec72f56e16fb19944a55acdbff67727d2bfadb8a`
(SHA-256 `3ebb7123f4d2b9b916338e11748380972d4339d66f54cb3258270f99bb62faf5`).
This gives R1 an independently published integration witness with exact
provenance. It has been inspected only; it has not been copied into the
repository or executed against either native revision as of the proposal
revision. R1 is now approved. The replay must confirm that the pinned
pre-fix build reaches the historical failure and that the fixed/current builds
return the permanent format error across the specified chunk schedules; a
matching byte string alone is not mechanism evidence.

Comparison coverage must include valid RFC streams, dictionary and overlap
cases, malformed/truncated fields, small/zero output buffers, one-byte and
empty chunks, every fixture split, repeated errors, EOF and reset. Normalize
documented policy differences; every unexpected difference is investigated.
Benchmarks use at least three fresh processes and repeated batches, with
construction/allocation separated from step timings, and report throughput,
step/end-to-end latency, workspace and malformed/resource-limit paths.
Comparisons remain finite evidence, not universal native equivalence.

## Defect controls and acceptance

First pass the exact unchanged positive control. Then require real proof
rejection for pending off-by-one writes; stale-byte reads; lost retained bits;
fatal block-switch results changed to exhaustion; an append after terminal
error; premature `NeedInput` on an impossible prefix; budget reset/refill;
unaccounted table/zero-input work; and stale caller publication length.
Scope each control to implemented source; never report a proposed control as run.

For the CVE case, validate the full multi-call witness on the pinned references
and the actual decoder once integrated, and corrupt the actual status/append
path while freezing contracts. Any missing applicable proof, replay/control,
required review or source/model bridge is a visible coverage gap that blocks
advertising supported Brotli under the updated security profile.

The source-to-binary trusted base and independent-review limitations remain
explicit. A checker result cannot authorize a profile or implementation change.
