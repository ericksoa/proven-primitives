# Security contracts and evidence

This assessment supports a scoped claim: **proven secure against the specified
per-call bounds, output-integrity and prior-destination-disclosure threats for
every admitted input and modeled execution**. The meaning of “specified” and
“modeled” below is part of the claim. It is not a claim of complete application,
streaming, side-channel or deployment security.

The source of truth is the [public contracts](CONTRACTS.md), the actual
`ensures` clauses and named lemmas, and the [checked security record](evidence/security.json).
The current source passes 177 checks with `--no-cheating`; the
[current checker output](evidence/b2-c1-verification.json) retains individual
results. The earlier [122-check B1 output](evidence/brotli-b1-verification.json)
and [90-check output](evidence/security-verification.json)
remains the measured G/security-corollary snapshot.
The
[proof guide](PROOFS.md) and [current proof record](evidence/claims.json)
identify the toolchain, source identities and trusted components.

| Primitive | Executable contracts | Security corollaries | Checked evidence |
|---|---|---|---|
| Base64 | [Encode](src/base64.rs#L367), [decode](src/base64.rs#L525) | [Prefix independence](src/base64.rs#L696), [decoded length](src/base64.rs#L713), [encoded size](src/base64.rs#L92) | [90-check security record](evidence/security.json) |
| Percent codec | [Encode](src/percent.rs#L172), [decode](src/percent.rs#L276) | [Prefix independence](src/percent.rs#L369), [expansion bounds](src/percent.rs#L386) | [90-check security record](evidence/security.json) |
| LZ4 raw block | [Decode](src/lz4.rs#L277) | [Prefix independence](src/lz4.rs#L412); work counters in the decoder and validator | [90-check security record](evidence/security.json) |
| Brotli B1 private component | No public decoder; private bit queue and window-header driver only | Pending capacity, exact retained bits, header status/window, sticky terminal state, reset, bounded work and unused-storage independence | [122-check B1 record](evidence/brotli-b1.json) |
| Brotli B2 private component | No complete decoder; canonical prefix/block-length and three-category switch core only | Bounded successful tables, exact code/width matches, state preservation and permanent zero-field invalid switch | [B2 report](BROTLI_B2.md) |
| C1 private composition | No public API; exact Base64-to-percent caller only | Current-prefix handoff, exact staged errors/effects, stale-length invalidation, final-prefix confidentiality and combined bounds | [C1 report](COMPOSITION_C1.md) |

All successful-buffer statements use the same [\`written\` definition](src/lib.rs#L18).

## Status vocabulary

- **Proved:** an actual checked contract, invariant or named theorem establishes
  the stated property in its stated domain. A corollary's premises are identified.
- **Partially proved:** checked components exist, but the stronger property
  also needs assumptions, caller obligations or additional proof work.
- **Proposed:** an obligation or follow-up proof is specified, without an
  implementation or checked result. New architectural choices require approval.
- **Unproved:** no checked result is claimed. Tests, inspection and benchmarks
  are identified separately and do not promote this status to proved.

## Common attacker and execution domain

For each of the five public routines, consider arbitrary input byte values,
input length `I`, destination capacity `C`, and initial destination contents
`B`. Empty, malformed and truncated inputs and insufficient capacities are
included; there is no public well-formed-input or sufficient-buffer precondition.
The attacker may choose those quantities or cause a caller to supply them.
Initial contents may also contain unrelated secrets unknown to the attacker;
the confidentiality comparison varies those contents while holding the input
fixed. If the caller supplies a secret as the current input, its specified
encoding or decoding is not covered by an unrelated-memory secrecy claim.

Admitted values are initialized, valid Rust slices/references with the modeled
lifetimes, bounds and exclusive mutable access. Unsafe/FFI callers that violate
those conditions, hardware faults and changes to input memory outside the Rust
model are outside that domain. The proof concerns source executions under the
documented Rust/Verus semantics. It is not a checked model of OS scheduling,
interleavings, machine timing or an arbitrary compromised execution environment.

For a mathematical result `D(input)`, the decoder contracts establish:

- Invalid input returns `InvalidInput` and preserves all of `B`, even if `C`
  is too small.
- Valid input whose result exceeds `C` returns `OutputTooSmall` and preserves
  all of `B`.
- Otherwise `Ok(n)` has `n = |D(input)| <= C`; the first `n` bytes equal `D`,
  and the suffix beyond `n` preserves its original contents.

Encoding accepts arbitrary bytes, returns the specified encoding when it fits,
and otherwise returns `OutputTooSmall` without changes. These are checked
functional and buffer-effect properties, not probabilistic test coverage.

**Caller requirement: expose only `output[..n]` from the current `Ok(n)`.**
Never serialize the whole allocation, use a previous call's length after an
error, or treat preserved bytes as newly produced data. On error, no output
prefix is authorized. Successful suffix preservation deliberately does not
sanitize old secrets. The library does not serialize the buffer for callers.

Callers can order independent calls, retry with different capacities, supply
truncated or replacement inputs, and reuse initialized destinations after
success or error. Each invocation is covered from its own admitted initial
state. Passing separate chunks does not resume a prior parse. The current
proofs do not model the caller's retained length, retry policy or session trace.

## Base64: encoding and canonical decoding

**Attacker control and domain.** Arbitrary bytes and lengths, capacities and
initial contents for `encode_into` and `decode_into`. Decoding uses only the
standard alphabet with strict final padding and zero unused trailing bits.
Whitespace recovery, Base64url, unpadded modes and streaming state are outside
this contract. Every input in the slice domain still has a specified result.

| Dimension | Checked guarantee and boundary | Status and evidence |
|---|---|---|
| Confidentiality | A successful returned prefix depends only on the input specification, regardless of earlier destination contents. The result tag/length follows input and capacity. This does not hide input length, validity, timing or cache behavior. | **Proved** by `encode_into`/`decode_into`, `written`, and the private `encoded_prefix_is_independent_of_previous_output` / `decoded_prefix_is_independent_of_previous_output` corollaries in [the source](src/base64.rs). The corollaries require the already-checked successful `written` postconditions; they are not axioms. Side channels are **unproved**. |
| State across calls | Error and success frame guarantees hold for each call from every admitted initial destination. There is no retained decoder session. A later independent call can reuse any still-valid buffer. | Per-call guarantees are **proved**. A caller/session trace theorem is **unproved**. `encoded_concat` proves mathematical encoding concatenation only at input boundaries divisible by three; arbitrary split decoding or retry-as-streaming is not established. |
| Resources | Encoded length is exactly `4 * ceil(I/3)` in mathematical integers. Valid decoded text has `I % 4 == 0` and output length at most `3 * (I/4)`. Successful writes are at most `C`; size arithmetic is checked before writing. | **Proved** by `encoded_size_is_four_per_group`, `decoded_length_bound` and executable contracts. Loop termination is **proved**. A whole-API numerical work ledger and practical DoS resistance are **unproved**; source inspection supports linear traversal, not a time budget. Extra storage is constant by source structure, with no heap allocation; a concrete stack/process-memory bound is **unproved**. |
| Composition/deployment | Callers must inspect each result and expose only its current prefix; protocol-specific canonicalization/authentication is outside this byte codec. | **Partially proved:** byte refinement and mathematical round trips are checked. Caller wrappers, cross-call policies and universal shipped-binary equivalence are **unproved**. See the common trust boundary below. |

The O(1) encoding size calculation avoids computing machine `I+2`; the
mathematical length formula does not authorize wrapping that expression in
executable code. The checked table and bit-vector lemmas introduce no
cryptographic constant-time guarantee.

## URI-component percent encoding and decoding

**Attacker control and domain.** Arbitrary byte sequences, lengths, capacities
and initial contents. Encoding preserves the RFC 3986 unreserved set and emits
uppercase `%HH` for other bytes. Decoding accepts either hex case and rejects
incomplete/invalid escapes. Other bytes, including literal `+`, pass through.
This is a byte codec; UTF-8 validity, full URL parsing and authorization are not
admitted as established properties of its result.

| Dimension | Checked guarantee and boundary | Status and evidence |
|---|---|---|
| Confidentiality | A successful returned prefix is the input-only encoding/decoding, independent of previous destination contents. Preserved suffix/error storage is excluded from that observation. | **Proved** by the public routines and the two private prefix-independence corollaries in [the source](src/percent.rs). Timing and other side channels are **unproved**. |
| State across calls | Per-call frame/error contracts cover arbitrary initial buffers and independent reuse. No partial-escape state survives between calls. | Per-call behavior is **proved**. `encoded_concat` proves the mathematical encoding concatenation law at any byte boundary. Decoder chunk boundaries can split `%HH`, so a streaming or caller-trace invariant is **unproved**. |
| Resources | Encoded output length lies between `I` and `3I`; valid decoded output length is at most `I`. Writes fit `C` or the whole buffer remains unchanged. | **Proved** by `encoded_length_bounds`, `decoded_length_bound` and the executable contracts. Termination is **proved**. Full numerical CPU-work, concrete stack/process-memory and practical DoS bounds are **unproved**; fixed local storage/no heap are source-audit facts. |
| Composition/deployment | Decoded bytes may include slashes, NULs or other application-significant values. A caller must separately establish the meaning and authorization of the interpreted value. | Codec round trip/refinement is **proved**. URL canonicalization, path traversal policy, XSS prevention, double-decoding safety and deployment guarantees are **unproved**. |

## LZ4 independent raw-block decoding

**Attacker control and domain.** Arbitrary complete input slices, output caps
and initial destination contents for `decompress_block_into`. The specified
format is an independent raw block with checked offsets and end rules; it has
no external dictionary, frame or retained streaming state. Empty input is
invalid; the zero-token block represents empty decoded output. The stricter
end-rule differences from the pinned reference are documented in
[COMPARISON.md](COMPARISON.md).

| Dimension | Checked guarantee and boundary | Status and evidence |
|---|---|---|
| Confidentiality | Every successful prefix equals the input-only raw-block result. Matches read bytes produced in the current call, including overlapping matches; zero and before-prefix offsets are rejected. | **Proved** by the API contract, match invariants and `decoded_prefix_is_independent_of_previous_output` in [the source](src/lz4.rs). Its premises are the checked successful-buffer postconditions. Timing and general process-wide information flow are **unproved**. |
| State across calls | Invalid input/small output preserve the entire destination; success preserves its suffix. Reused buffer contents cannot enter a successful result. | Per-call guarantees are **proved**. No raw-block call resumes an earlier partial block. A streaming, frame/dictionary or arbitrary caller trace model is **unproved** and outside the API. |
| Resources | Successful output is at most `C`. The checked internal production counter obeys `produced <= 512 * consumed_input`; wide arithmetic uses that invariant. Validation charges at most `I` forward-span work, including errors. For success with `O` returned bytes, combined abstract accounting is at most `2I + 2O`. | Bounds on writes, counters, termination and the stated ghost accounting are **proved**. The accounting counts selected input spans and byte copies, not every instruction, header operation or cycle. A standalone mathematical maximum-expansion theorem, concrete stack/process-memory bound, wall-clock budget and practical DoS resistance are **unproved**. |
| Composition/deployment | The caller's cap limits emitted bytes, but the library does not impose a service-wide input, concurrency, rate or time budget. Expose only the returned prefix. | **Partially proved:** the byte core and abstract accounting are checked; wrapper policies, concurrency/deployment and universal source-to-machine equivalence are **unproved**. |

For all three primitives, fixed local arrays/counters and no executable
recursion or heap allocation are source-audit facts. Verus ghost sequences are
erased, not input-sized runtime allocations. These observations do not establish
an exact stack-byte budget or bound memory allocated by callers, runtimes or OS.
Termination and a source-level work bound do not by themselves prevent service
exhaustion from large inputs, many calls or adversarial scheduling.
An output cap is not an input-work cap: the decoders continue validating later
input after output is known too small, preserving malformed-input priority.
Service-wide input sizes, call counts and concurrency therefore need caller
policies and evidence beyond the current output-cap guarantees.

## Historical CVEs, regressions and proof controls

| Case | Generalized property and checked status | Finite regression/control evidence |
|---|---|---|
| CVE-2026-32829, LZ4 stale-buffer disclosure | Input-only successful output, valid current-call backreferences, full error-buffer preservation: **proved**. | The pinned historical safe decoder returned 18 old destination bytes in a 25-byte result. Current reference and this decoder reject the zero offset. Deliberate stale-byte reads in general and offset-one paths are rejected by proof. |
| CVE-2017-1000430, Base64 sizing overflow | Exact mathematical encoded length, guarded executable arithmetic and bounded writes: **proved** for admitted slices/capacities. | The old arithmetic is reproduced with wrapping 32-/64-bit integers; this is not a giant allocation or execution of the old encoder. Exact/small real buffers are tested. A guard that accepts an extra four-byte group is rejected by proof. |
| CVE-2026-111497, Brotli format-error/input-exhaustion confusion | B1 input/header invariants and B2's corrected shared block-switch transition are **proved for those private components**. Complete-stream Rust integration is **unproved**. | The native R1 replay gives fixed `-17` versus pre-fix `-9` across chunks 1..22, with intact guards and no ASan report. Component mutations must be rejected. No complete decoder exists. |

[SECURITY_CASES.md](SECURITY_CASES.md) gives source advisories, fixture details
and limits. [The rejection suite](tests/proof_rejection.rs) first verifies an
unchanged positive control and then requires real proof rejection. A failing
tool launch or type error is not accepted as proof rejection. The current-source
[current control transcripts](evidence/b2-c1-controls.json) retain the current
results; the sixteen-control B1 and earlier eleven-control records remain
historical.
The
[comparison record](evidence/validation-upstream-comparison.json) is finite
compiled-behavior evidence; neither tests nor corruption controls replace the
universal contracts or validate the threat model's completeness.

## Brotli streaming obligations: B1/B2 checked, full decoder unproved

Brotli remains a candidate. [B1](BROTLI_B1.md) checks the private input/header
foundation and [B2](BROTLI_B2.md) checks canonical prefix/block lengths plus the
shared literal/command/distance switch core. The approved public design is not
yet implemented as a complete decoder; deferred B3/B4 choices and review remain.

Proposed obligations for every permitted chunk/call sequence:

1. B1's checked constructor establishes its bit-reader/header invariant. Future
   decoder transitions, including error and suspension, must preserve pending,
   window and output bounds; every append must establish capacity first.
2. B1 distinguishes its reserved header error from genuine input exhaustion.
   B2 proves that a one-type block switch is a permanent zero-field error before
   prefix parsing and remains terminal until explicit reset.
3. B1 covers its one-byte header, empty calls and terminal retries. Arbitrary
   full-decoder chunk boundaries, partial fields, retries and output backpressure
   remain proposed integration obligations.
4. B1 retained bits/header results depend only on valid supplied bits. Future
   produced prefixes must depend only on authorized compressed input and any
   explicitly approved dictionary, excluding unrelated old decoder memory.
5. B1 pending storage and abstract reader/header work have checked bounds.
   Future expansion, window/table storage and complete-decoder work need explicit
   cumulative bounds and deployment assumptions.

A one-shot output-correctness proof does not establish these temporal
properties. An empty-input call may legitimately make no stream progress;
its own work/termination and the environment's eventual provision of input
must be distinguished. An infinite sequence of caller retries does not imply
an internal decoder loop or a proved service-wide time bound.
The component negative controls include fatal-switch-to-retry corruption. A
future complete-decoder control must
still reintroduce fatal block-switch-to-retry confusion in the actual integrated
path and fail a checked invariant over a multi-call regression.

## Composition, independent review and shipped-program trust

The project verifies the same annotated routine source compiled by Cargo;
ghost erasure does not select a separate maintained executable implementation.
Records bind exact source hashes, locked dependencies, checker options and
measured executable identities. Current work also compares executable routines
and compiled artifacts after proof-only additions. Those checks strengthen
provenance; they do not verify the compiler or prove universal machine-code
equivalence.

The retained native build and timing evidence uses Rust 1.99.1 on
`aarch64-apple-darwin`, with Verus 0.2026.10.18.7d82994 and the locked proof
dependencies. A different target, compiler or build requires its own checked
model/build binding; the observed binary identity does not cover it.

The trusted base includes the mathematical specifications and their standards
interpretation, Verus and bundled Z3, Verus macros/erasure and modeled Rust/vstd
operations, the pinned Rust/LLVM compiler, valid-reference assumptions, OS and
hardware. Independent specification review is still pending; the RFC mapping
is explicitly [author self-review](BASE64_SPEC_REVIEW.md). A proof of the wrong
specification would not establish the intended security property.

Universal upstream equivalence, arbitrary caller wrappers, concurrent or
complete-stream trace models, concrete machine resource limits and side channels
remain unproved. C1 proves only its exact caller. The approved follow-up scopes
are in [SECURITY_PROOF_EXTENSION_PROPOSAL.md](SECURITY_PROOF_EXTENSION_PROPOSAL.md).
