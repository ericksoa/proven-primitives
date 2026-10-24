# Proven Primitives: contracts

Public contracts for three useful byte-processing primitives.

The [security-contract assessment](SECURITY_CONTRACTS.md) interprets these
unchanged functional contracts against explicit attacker controls and
observations. It distinguishes proved per-call properties from unproved caller,
streaming, side-channel and deployment obligations. It adds no public API or
new implementation precondition.

Status: the human explicitly approved the complete proposal in this chat on
2026-10-23. The contracts below are approved implementation requirements. Proof
status must be established by actual checker results, not by this approval.

## Approved foundations

- Standalone project covering Base64 encoding/decoding, URL percent
  encoding/decoding, and LZ4 block decompression.
- Rust/Cargo with the pinned Verus toolchain and proof libraries from the pilot:
  Rust 1.99.1 and Verus 0.2026.10.18.7d82994 (commit
  `7d829946231d6413a398f6e4160cdfe951261dad`).
- Byte-slice inputs, caller-provided output buffers, explicit errors.
- Bounded loops, no input-dependent executable recursion, no unsafe code or I/O
  in the primitive library.
- Source, proofs, reproducible verification, tests, benchmarks, and documentation
  describing the guarantees and assumptions.

These approvals do not authorize a new language, verifier, runtime, dependency,
service, build approach, or protocol/API change outside their stated scope.

## package and proof approach

- One Cargo library, package `proven-primitives`, crate `proven_primitives`,
  Rust edition 2021, with public modules `base64`, `percent`, and `lz4`.
- The executable implementation and its proofs live in the same Verus-annotated
  source. Ordinary Cargo compilation erases ghost proof material; verification
  uses the pinned `cargo verus` command. There is no separately maintained
  implementation that is merely compared against a verified model.
- The proof dependency is the matching `vstd` package,
  `=0.0.0-2026-10-18-0147`, and its required pinned Verus builtins/macros. The resolved Cargo dependency list is retained in the lockfile; the human
  separately approved its nine required non-Verus macro/build dependencies
  before compilation. Exact versions are recorded in
  `evidence/dependency-review.json`. The human subsequently approved the three
  exact test/benchmark reference dependencies and features recorded in
  REFERENCE_PROPOSAL.md. They do not change the primitive implementation's
  normal dependency set or proof assumptions.
- Native local builds use the existing Apple Command Line Tools 27.0 through a
  per-command `DEVELOPER_DIR=/Library/Developer/CommandLineTools` setting.
- Specifications describe mathematical byte sequences. Proofs connect each
  executable routine's return value and buffer writes to those specifications.
- For every public routine, invalid bytes and small buffers are normal inputs
  handled by a returned error, rather than excluded by a well-formed-input
  precondition. Safe Rust reference validity is part of the trusted semantics.
- Proof checks reject `assume`, `admit`, unchecked/external implementation
  bodies, and newly introduced axioms. Standard Verus/Rust library specifications
  and the verifier/solver remain explicitly documented trusted components.

## shared API and error semantics

```rust
pub enum Error {
    InvalidInput,
    OutputTooSmall,
}

pub mod base64 {
    pub fn encode_into(input: &[u8], output: &mut [u8]) -> Result<usize, Error>;
    pub fn decode_into(input: &[u8], output: &mut [u8]) -> Result<usize, Error>;
}

pub mod percent {
    pub fn encode_into(input: &[u8], output: &mut [u8]) -> Result<usize, Error>;
    pub fn decode_into(input: &[u8], output: &mut [u8]) -> Result<usize, Error>;
}

pub mod lz4 {
    pub fn decompress_block_into(input: &[u8], output: &mut [u8]) -> Result<usize, Error>;
}
```

On `Ok(n)`, `n <= output.len()`, the first `n` output bytes equal the
specification result, and output bytes after `n` retain their original values.
On either error, the entire output buffer retains its original values.

Malformed input takes precedence over insufficient output capacity. For valid
input whose mathematical output length cannot fit the provided destination
(including a length exceeding the machine's addressable range), the result is
`OutputTooSmall`. This avoids a separate public arithmetic-overflow error.

To establish unchanged output on error without a temporary allocation, the
implementation validates format and required output length before bounded
writes. Where a validation pass is needed, writing is proved safe under its
postcondition. Base64 encoding accepts arbitrary bytes, and its separately
approved optimization computes the required length using checked
quotient/remainder arithmetic. Decoder validation remains complete before
writes. The public routines perform no heap allocation.

This is a new verified core with a deliberately small API, rather than a claim
that an existing upstream crate or its complete API has been verified.

The separately approved [Brotli B1 component](BROTLI_B1.md) is crate-private
and adds no public routine to this contract. Its checked pending-bit/window-
header guarantees are component evidence, not a supported Brotli decoder API.
The [B2 prefix/block-switch core](BROTLI_B2.md) and
[C1 composition caller](COMPOSITION_C1.md) are also crate-private. Their checked
contracts add component and exact-caller evidence without changing the five
public function signatures or creating supported public Brotli.

## Base64 behavior

- RFC 4648 section 4 standard alphabet (`A-Z`, `a-z`, `0-9`, `+`, `/`).
- Encoder emits canonical padding and zero unused trailing bits, with no line
  wrapping.
- Decoder requires canonical padding when needed and rejects incorrect length,
  misplaced/excess padding, whitespace, non-alphabet bytes, and nonzero unused
  trailing bits. Empty input encodes and decodes to empty output.
- This first contract does not include Base64url, MIME whitespace recovery,
  unpadded variants, streaming, or constant-time side-channel guarantees.
- Proof requirements: output refinement to the RFC-derived byte specification,
  `decode(encode(bytes)) == bytes`, re-encoding any accepted canonical input
  returns that input, buffer preservation, checked size arithmetic and loop
  termination.

Source: https://www.rfc-editor.org/rfc/rfc4648

## percent-encoding behavior

- A URI-component byte codec following RFC 3986's unreserved character set.
- Encoding leaves only ASCII letters, digits, `-`, `.`, `_`, and `~` unchanged;
  every other byte becomes uppercase `%HH`.
- Decoding accepts uppercase and lowercase hexadecimal escapes and rejects
  incomplete or non-hexadecimal escapes. Other bytes pass through unchanged.
- `+` remains a literal plus byte. This is not HTML form encoding.
- Outputs are bytes. The codec makes no claim of UTF-8 validity, complete URL
  parsing, Unicode normalization, path authorization, or XSS prevention.
- Proof requirements: exact byte transformation, `decode(encode(bytes)) == bytes`,
  error/buffer preservation, output-length bounds and loop termination.

Source: https://www.rfc-editor.org/rfc/rfc3986#section-2.1

## LZ4 behavior

- Decode independent raw LZ4 blocks according to the upstream block-format
  specification. The whole input slice is one block; the destination length is
  the caller's output cap.
- Support literal sequences, length extensions, nonzero backward offsets and
  overlapping match copies. No external dictionary is available.
- Reject truncated fields, zero offsets, references before produced output,
  invalid length arithmetic, and violations of the block format's end rules.
- The zero-token block represents empty decoded output; an empty input slice is
  invalid.
- Scope excludes frame headers, checksums, streaming, external dictionaries and
  compression. It therefore does not claim the complete API of `lz4_flex` or
  the complete LZ4 frame format.
- Proof requirements: successful output equals the block specification, invalid
  references cannot be read, output writes stay inside the caller's buffer,
  errors preserve the buffer, length arithmetic is safe, and processing
  terminates with work bounded by input plus produced output.

Source: https://github.com/lz4/lz4/blob/dev/doc/lz4_Block_format.md

## Validation and public claims

- The original standard-library-only Rust tests use standards vectors, malformed/truncated
  inputs, destination capacities around exact size boundaries, preserved-buffer
  checks and deterministic generated inputs. A separately approved comparison
  test adds pinned upstream references and adapted fixture assertions. Tests
  supplement formal proofs and do not prove universal upstream equivalence.
- Benchmarks use the same executable routines with a Rust standard-library
  harness and include large inputs. Its approved comparison mode measures the
  current upstream references with the same compiler/profile and records raw
  samples. No additional benchmark framework is used.
- The repository records exactly which functions and properties pass formal
  checking. An unproved property remains labeled unproved even if tests pass.
- Source-level proofs establish properties under the Rust/Verus model; the
  compiler, operating system, hardware and concrete stack-byte capacity are not
  verified by this project. No executable recursion or input-sized local stack
  allocation is introduced.
- The human separately selected Apache-2.0. No GitHub repository, CI service or
  crate publication is created by this implementation; local code and
  documentation are prepared for review before a separate publication decision.

## Approval

The human approved all three targets, then explicitly approved these contracts
as written. Further architectural decisions remain reserved to the human.
