# Proven Primitives

**Mathematically proven byte-processing primitives.**

Base64, URI-component percent encoding, and LZ4 block decoding with
machine-checked functional correctness, buffer-preservation, size-arithmetic,
and termination contracts.

**Proven secure against specified per-call threats under the published
contracts and trusted model.** Checked guarantees exclude bounds/arithmetic
failures, incorrect specified outputs and disclosure of prior destination
contents through a successful returned prefix, for every admitted input and
modeled execution, including malformed bytes and insufficient buffers.
The [security-contract assessment](SECURITY_CONTRACTS.md) states attacker control,
exact domains, assumptions, evidence and remaining gaps across confidentiality,
state across calls, resources and deployment. Callers must expose only the
current `Ok(n)` prefix. Streaming, side channels, practical DoS resistance and
whole-application security are not established by these per-call proofs.

## What is proved

| Primitive | Checked guarantees |
|---|---|
| Base64 | Exact standard-alphabet encoding and strict canonical decoding; byte round trip; canonical-text round trip; correct size and padding handling |
| Percent encoding | Exact URI-component byte escaping and strict decoding; byte round trip; uppercase emitted escapes and acceptance of either hex case |
| LZ4 raw block decoding | Output equals the block specification, including overlapping matches; valid backreferences and end conditions; checked linear byte-work accounting |
| Private Brotli B1 input/header | Eight-byte pending bounds; exact retained bits; RFC normal-window result; truthful exhaustion/truncation/invalid status; sticky terminal states and reset; bounded source work |
| Private Brotli B2 prefix/block-switch core | Bounded canonical code construction and exact matching; RFC block lengths; literal/command/distance switch invariants; permanent zero-field invalid switch for one declared type |
| Private Brotli B3a front end | Exact fixed workspace and tree records; initialized-range and single-symbol confidentiality; exact meta-block headers; simple and complex code descriptions; RFC repeat-coded final lengths with exact space accounting; canonical installation from the fixed builder region |
| Private C1 caller | Base64 decode into scratch followed by percent decode of only the current prefix; exact errors/effects, stale-length invalidation, confidentiality and combined bounds |
| Every public routine | No out-of-bounds access or arithmetic overflow under the model; loop termination; correct error results; unchanged destination on error; unchanged destination suffix on success |

All five public functions are implemented with bounded loops, caller-owned
buffers, no heap allocation, no executable recursion, and no unsafe code in the
implementation. The same annotated source is verified and compiled. There is
no separately maintained unverified implementation behind the API.

The current implementation passes **350 project verification checks** with
`--no-cheating`. See [the proof record](evidence/claims.json),
[the contracts](CONTRACTS.md), and [the proof guide](PROOFS.md).
The [current B3a record](evidence/brotli-b3a.json) binds the exact current
source, checked private slice and controls. The earlier
[B1 record](evidence/brotli-b1.json) and
[security proof record](evidence/security.json) remain historical snapshots;
the latter binds the checked corollaries and measured G executable.

The [candidate roadmap](ROADMAP.md) includes Brotli decompression and the recent
CVE-2026-111497 state-transition/buffer-overflow case. It is a research target;
the current library does not implement a complete Brotli decoder.
The [checked B1 component](BROTLI_B1.md) proves the private streaming bit queue
and RFC window header, without claiming a complete decoder or the CVE's actual
block-switch integration.
The [checked B2 component](BROTLI_B2.md) proves canonical prefix/block-length
and block-switch foundations, including the corrected zero-field permanent
failure. It still does not decode a complete stream.
The [checked B3a slice](BROTLI_B3A.md) adds the exact caller-workspace layout,
safe initialized tree records, source-linked meta-block headers, simple and
complex code descriptions, RFC repeat-coded final lengths, and canonical
installation from the fixed builder region. Tree groups, context maps,
literal/command/distance execution, and the rest of B3 remain incomplete.
The exact B3b metadata/state/MTF choices await human selection in the
[B3b decision proposal](BROTLI_B3B_PROPOSAL.md).
[P1](PIPELINE.md) implements fail-closed local evidence bookkeeping without
adopting the draft security profile. The approved later proof scopes remain in
[SECURITY_PROOF_EXTENSION_PROPOSAL.md](SECURITY_PROOF_EXTENSION_PROPOSAL.md).

[C1 compositional verification](COMPOSITION_C1.md) checks one exact caller of
the Base64 and percent decoders, including compatibility, stale lengths,
intermediate effects and combined resources. It is not evidence for arbitrary
applications.

[Security case studies](SECURITY_CASES.md) connect the checked guarantees to
LZ4 stale-buffer disclosure (CVE-2026-32829) and Base64 sizing overflow
(CVE-2017-1000430). They distinguish generalized proofs from regression tests
and from comparisons with upstream implementations.

[Upstream comparisons](COMPARISON.md) include adapted regression assertions,
deterministic differential tests, a historical LZ4 disclosure replay, and
repeated latency/throughput measurements against the approved references.
These are compatibility and performance evidence, not a proof of universal
equivalence to upstream. The current implementation has substantial performance
gaps on some workloads; the report includes the measured tradeoffs.

[Proof-preserving optimizations](OPTIMIZATION.md) record the approved O(1)
Base64 encoding size calculation and LZ4 offset-one fill, with fresh baseline
and candidate measurements. Public contracts and dependencies are unchanged.

[Two further Base64 iterations](TABLE_ITERATIONS.md) replace executable character
classification with proved immutable tables. Each iteration has separate proof
and timing records, with the same mathematical specifications and public API.

[Base64 batching results](BATCHING.md) cover two more approved iterations using
48-bit integer packing. The decoder still validates the entire input before
writing. See the [RFC specification self-review](BASE64_SPEC_REVIEW.md).

[Batched validation results](VALIDATION.md) cover the approved G iteration:
eight-character validation with the same contracts and complete validation
before writes, including a malformed suffix after a known-small destination.

## Example

```rust
use proven_primitives::{base64, percent, Error};

fn main() -> Result<(), Error> {
    let mut encoded = [0u8; 8];
    let n = base64::encode_into(b"proof", &mut encoded)?;
    assert_eq!(&encoded[..n], b"cHJvb2Y=");

    let mut decoded = [0u8; 8];
    let decoded_n = base64::decode_into(&encoded[..n], &mut decoded)?;
    assert_eq!(&decoded[..decoded_n], b"proof");

    let mut escaped = [0u8; 16];
    let n = percent::encode_into(b"a+b c", &mut escaped)?;
    assert_eq!(&escaped[..n], b"a%2Bb%20c");

    // A failed call cannot leave a partially modified destination.
    let mut destination = [0xa5u8; 8];
    assert_eq!(base64::decode_into(b"Zh==", &mut destination), Err(Error::InvalidInput));
    assert_eq!(destination, [0xa5; 8]);
    Ok(())
}
```

## The API

```text
base64::encode_into(input, output)        -> Result<usize, Error>
base64::decode_into(input, output)        -> Result<usize, Error>
percent::encode_into(input, output)       -> Result<usize, Error>
percent::decode_into(input, output)       -> Result<usize, Error>
lz4::decompress_block_into(input, output) -> Result<usize, Error>
```

Inputs are `&[u8]`; destinations are `&mut [u8]`. `Ok(n)` identifies the produced
prefix. The rest of the destination is preserved. Both `InvalidInput` and
`OutputTooSmall` preserve the entire destination. Malformed input takes
precedence over a small destination.

Base64 uses RFC 4648's standard alphabet and canonical padding. Percent decoding
keeps `+` literal and produces bytes, not validated UTF-8. LZ4 accepts independent
raw blocks, including overlapping copies, and enforces the specified end rules.
Frame headers, checksums, dictionaries, and streaming are outside its API.

## Reproduce the proof

Pinned versions:

- Rust **1.99.1**, with `rustc-dev`, `llvm-tools`, and `rustfmt`.
- Verus **0.2026.10.18.7d82994**.
- `vstd` **0.0.0-2026-10-18-0147**, with exact dependencies in `Cargo.lock`.

Obtain the matching binary distribution from the
[Verus release](https://github.com/verus-lang/verus/releases/tag/release/0.2026.10.18.7d82994).
Set `VERUS_ROOT` to its extracted directory. Install the pinned tools before
running the commands below; the project includes no tool installer.

```sh
export VERUS_ROOT=/path/to/extracted/verus
export PATH="$VERUS_ROOT:$PATH"

cargo +1.99.1 verus build --fwd-verus-args-to roots --locked --release -- \
  --no-cheating --num-threads 1 --triggers-mode silent --rlimit 60

cargo +1.99.1 test --locked --release
```

On this project's macOS validation host, native builds use the installed Apple
Command Line Tools without changing the global developer selection:

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools cargo +1.99.1 test --locked --release
```

Apply that prefix to native proof builds, examples, and benchmarks on this
macOS setup as well.

`cargo build` and `cargo test` compile and test the code; they **do not replace
the Verus proof command**. Ghost proof material is erased by the approved Verus
macros during ordinary Cargo compilation.

## Watch the prover reject defects

```sh
VERUS_ROOT=/path/to/extracted/verus cargo +1.99.1 test --locked --release \
  --test proof_rejection -- --ignored --nocapture
```

This first verifies an unchanged positive control. It then changes only
executable implementation code in private temporary copies and requires proof
rejection for:

1. A wrong Base64 alphabet.
2. Treating `+` as a space during percent decoding.
3. Copying the wrong preceding byte in an LZ4 match.
4. Reading a stale destination byte instead of a previously produced LZ4 byte.
5. Accepting an undersized Base64 destination with an incorrect size guard.
6. Capturing a stale destination byte in the optimized LZ4 fill path.
7. Incorrectly accepting a NUL byte through a corrupted decoding table.
8. Extracting an encoding batch digit from the wrong bit position.
9. Extracting a decoding batch byte from the wrong bit position.
10. Accepting invalid alphabet bytes through a broken validation predicate.
11. Returning a small-output error before validating a malformed suffix.
12. Appending past the B1 pending buffer.
13. Consuming one extra retained Brotli bit.
14. Computing the wrong Brotli window size.
15. Reporting a reserved invalid header as retryable.
16. Appending input after a terminal Brotli failure.
17. Passing the complete scratch allocation to a downstream decoder.
18. Retaining publication state after a Base64-stage error.
19. Retaining publication state after a downstream error.
20. Publishing the whole output allocation rather than its current prefix.
21. Collapsing a Base64 format error into a capacity error.
22. Omitting the percent stage from the checked work ledger.
23. Falsely rolling scratch back after a downstream error.
24. Turning a permanent Brotli block-switch error into retryable input.
25. Computing the wrong canonical prefix-code recurrence.
26. Shifting every B3a workspace tree-record address by one byte.
27. Reading an uninitialized canonical tree record.
28. Reducing the fixed B3a scratch total by one byte.
29. Accepting the reserved meta-block-header bit.
30. Accepting a nonminimal normal meta-block length.
31. Accepting a nonminimal metadata length.
32. Reporting final meta-block-header truncation as retryable input.
33. Swapping the stored low and high bytes of a workspace tree code.
34. Reconstructing a workspace tree code from its length byte.
35. Misclassifying the simple/complex code selector.
36. Accepting a symbol equal to the alphabet limit.
37. Accepting a duplicate simple symbol.
38. Mapping a static-prefix value to the wrong code length.
39. Misclassifying complex code-space overflow.
40. Changing the RFC code-length permutation.
41. Shifting the builder code-length write region.
42. Reading an uninitialized builder code-length entry.
43. Storing the wrong byte in a builder count.
44. Storing the wrong byte in a builder next-code value.
45. Rejecting a required zero-length canonical record.
46. Installing the wrong canonical code in a destination record.
47. Initializing the repeated previous length to a value other than eight.
48. Failing to reset a repeat when the repeated length changes.
49. Subtracting one instead of two in chained-repeat expansion.
50. Adding four instead of three to a repeat suffix.
51. Rejecting a repeat that exactly fills the selected alphabet.
52. Undercharging repeated nonzero lengths against the 32,768-unit code space.
53. Comparing raw auxiliary stream bits with an unreversed canonical code.

The mathematical specifications stay unchanged. The percent-decoding and LZ4
read mutations are semantic defects in otherwise memory-safe Rust. A successful
negative-control test means the prover rejected the mutation, not that the
mutation was correct.

## Tests and benchmarks

The tests cover standards vectors, every single-byte value for the codecs,
generated binary data, padding and escape errors, LZ4 overlap and length
extensions, exact/insufficient capacities, buffer preservation, and large
inputs. The original test groups use the Rust standard library and include an
independent streaming-bit Base64 oracle. An additional comparison test uses
the separately approved, pinned development references. Adapted upstream test
material is attributed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
Tests supplement the universal proof claims.

```sh
cargo +1.99.1 bench --locked --bench primitives
```

The benchmark reports CSV for all five APIs and both literal-only and
overlapping-match LZ4 blocks. Throughput is measured in original/decoded bytes,
with allocations and input generation outside the timed loop. Results are
measurements on the executing host, not a performance guarantee.

Run the comparison test and the existing benchmark's comparison mode with:

```sh
cargo +1.99.1 test --locked --release --test upstream_comparison -- --nocapture
cargo +1.99.1 bench --locked --bench primitives -- --compare
```

The comparison mode includes scalar and runtime-selected SIMD Base64 references
on supported targets, and safe LZ4 block decoding. It validates the measured
results outside timing and records repeated batch-average latency. See
[COMPARISON.md](COMPARISON.md) for methodology, raw samples, and scope.

## What “proven” means

Verus and its bundled Z3 solver discharge verification conditions for the
published byte-sequence specifications and the executable source. The trusted
base includes those specifications, Verus, Z3, the proof macros, the modeled
Rust/library semantics, and the Rust compiler. The operating system, hardware,
and concrete stack-byte capacity are not verified by this repository.

For LZ4, the abstract byte-work accounting is bounded by `2I + 2O` for input
length `I` and produced output length `O`: validation inspects at most one
forward input span, execution inspects another, and each copied output byte
costs at most a read and a write. These are checked source-level counters and
progress invariants, not a bound on machine cycles.

This project does not prove cryptographic constant time, the security of a
complete URL-processing system, or every behavior of an upstream crate. It
implements a small, explicitly specified core with the guarantees listed above.

## License

Licensed under [Apache-2.0](LICENSE). See [NOTICE](NOTICE).
