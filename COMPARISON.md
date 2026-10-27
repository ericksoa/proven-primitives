# Upstream compatibility, security replay, and performance

Measured on Apple M2 Pro, macOS 26.7.1, Rust 1.99.1.

The baseline snapshot identified in [evidence/comparison.json](evidence/comparison.json)
passed 69 project checks. The first optimized results are in
[OPTIMIZATION.md](OPTIMIZATION.md), with the latest Base64 iterations in
[TABLE_ITERATIONS.md](TABLE_ITERATIONS.md) and subsequent batching in
[BATCHING.md](BATCHING.md), followed by [VALIDATION.md](VALIDATION.md). The results below
are finite compatibility evidence and host measurements, not a proof of
universal equivalence to either upstream implementation.

## References and scope

| Reference | Exact version / source | Mode |
|---|---|---|
| base64 | 0.23.1; 069bf7067b949f5c0a92b6ceb82492920502f2c2 | STANDARD scalar; runtime-selected SIMD for performance |
| lz4_flex current | 0.14.0; 1bffdcbbf906a234b913937cb2f57c0245915038 | Safe, checked independent block decoding; no frames |
| lz4_flex historical | 0.12.0; 975bfa7ac9583da879b5d7578b423232d84f69fe | Initialized-buffer security replay only |

The exact approved features, checksums, and dependency scope are recorded in
[REFERENCE_PROPOSAL.md](REFERENCE_PROPOSAL.md) and
[the dependency review](evidence/dependency-review.json). The historical vulnerable
package is intentionally present as a development-only regression control.
It is not a normal dependency of the primitive implementation.

## Compatibility and historical security result

| API | Comparison calls | Both succeed with equal bytes and lengths | Both reject | Extra strict rejections |
|---|---:|---:|---:|---:|
| Base64 encode | 6,723 | 3,219 | 3,504 | 0 |
| Base64 decode | 72,081 | 3,121 | 68,960 | 0 |
| LZ4 decode | 72,032 | 7,233 | 64,797 | 2 |

There were **150,836 comparison calls and zero unexpected differences**. Counts
include multiple buffer capacities and data patterns; they are not counts of
unique inputs or a percentage of the full input space. Every 0-, 1-, and 2-byte
input was exhausted for decoding at a sufficient destination capacity. Other
cases use generated valid inputs, selected malformed fixtures, and applicable
upstream test assertions. The complete upstream suites were not run.

Observed contract differences:

- Two blocks accepted by current LZ4 violate our specified end rules: fewer
  than five final literals, and a last match too close to the decoded end.
- Nine malformed-Base64/small-buffer cases return our `InvalidInput` while
  upstream reports insufficient output. Our contract prioritizes malformed input.
- Upstream changed destination contents on error in 1,557 Base64 and 993 LZ4
  comparisons. Our implementation preserved the entire destination on every error.
- Upstream changed the suffix beyond its returned LZ4 prefix in seven comparisons.
  Our implementation preserved every successful suffix. These observations do not
  by themselves establish a defect in the upstream API; its guarantees differ.

Fixture bytes, outcomes, and counters are retained in
[the executable comparison report](evidence/upstream-comparison.json). Adapted
assertions and license notices are listed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

**The historical CVE-2026-32829 replay succeeded:** the safe 0.12.0 decoder
returned 25 bytes including 18 bytes from the initialized destination's old
contents. Current 0.14.0 rejected the zero offset. Our decoder rejected it and
preserved the complete buffer. [SECURITY_CASES.md](SECURITY_CASES.md) connects
this concrete replay to the checked input-only output property.

## Brotli native comparison boundary

The approved R1 harness replays CVE-2026-111497's 22-byte witness against the
pinned native fix, its pre-fix parent and v1.2.1 for input chunks 1 through 22.
The fixed versions return permanent error `-17`; the parent later returns `-9`.
All guard bytes remain intact and AddressSanitizer reports no overwrite, so this
is status-path evidence rather than a memory-corruption reproduction. See
[the structured R1 record](evidence/brotli-r1.json).

B3b runtime comparisons use the native decoder only where stream acceptance and
status are observable. The native API does not expose its internal context-map,
inverse-MTF or active-tree fields, so those values cannot be compared directly.
The pinned native decoder accepts some context maps missing an advertised tree;
the checked B3b component rejects them to enforce the RFC coverage requirement.
That deliberate strict difference and the full 64-scenario runtime matrix are
recorded in [the B3b report](BROTLI_B3B.md). Finite agreement does not establish
universal equivalence, and no complete Rust Brotli decoder is claimed.

## Valid-input performance at 256 KiB

Times are medians of 27 batch-average latency samples per configuration, across
three separate processes. A larger ratio means Proven Primitives took longer.

| Workload | Proven (microseconds/call) | Reference | Reference (microseconds/call) | Proven / reference |
|---|---:|---|---:|---:|
| Base64 encode | 632.120 | base64_scalar | 92.026 | 6.87x |
| Base64 encode | 632.120 | base64_simd | 31.932 | 19.80x |
| Base64 decode | 1363.775 | base64_scalar | 99.825 | 13.66x |
| Base64 decode | 1363.775 | base64_simd | 46.650 | 29.23x |
| LZ4 literal-only | 7.964 | lz4_flex_safe | 5.292 | 1.51x |
| LZ4 upstream-compressed periodic input | 8.599 | lz4_flex_safe | 8.042 | 1.07x |
| LZ4 repeated-byte overlap | 461.260 | lz4_flex_safe | 3.740 | 123.34x |

These results expose substantial optimization work. On this host, scalar
Base64 and especially repeated-byte LZ4 matches are expensive in the current
implementation. Near parity on one periodic LZ4 workload does not imply parity
on general compressed data. Additional validation passes can have a cost, but
the table does not isolate their contribution from other implementation choices.

## Small-input latency: 8 decoded/original bytes

| Workload | Proven (ns/call) | Reference | Reference (ns/call) |
|---|---:|---|---:|
| Base64 encode | 19.35 | base64_scalar | 9.69 |
| Base64 decode | 47.32 | base64_scalar | 20.81 |
| LZ4 literal-only | 12.60 | lz4_flex_safe | 4.83 |

## Measurement method and retained evidence

- Same benchmark executable, compiler, optimization profile, inputs, and
  destination capacities for each pair. Both reference Base64 engines require
  standard-alphabet canonical padding; LZ4 uses the approved safe/checked features.
- Engine construction, input generation, output allocation, validation, warmup,
  output reset, corpus writes, and formatting occur outside timed loops.
- Each timed call consumes black-boxed inputs/results. Each batch rotates which
  implementation executes first. Batches use a bounded, input-size-dependent
  iteration count; three processes each take nine batches per configuration.
- Workloads include 8, 64, 4,096, and 262,144 logical bytes, literal-only and
  overlapping LZ4, upstream compression, late-invalid Base64, small outputs, and
  invalid zero offsets. Historical vulnerable code is never a performance reference.
- The report contains 78 configurations and 2,106 raw batch samples. These are
  warm steady-state batch averages, not single-request p95/p99 or cold-cache
  measurements. No performance guarantee or cross-machine claim is made.

The [machine-readable report](evidence/comparison.json) includes every summary,
minimum and maximum batch averages, throughput for valid workloads, compiler
details, benchmark source/binary hashes, exact reference identities, and SHA-256
digests for the generated input corpus. The corpus is regenerated by the harness;
its binary files remain local. Raw samples are published as
[run 1](evidence/comparison-run-1.csv), [run 2](evidence/comparison-run-2.csv), and
[run 3](evidence/comparison-run-3.csv).

## Reproduce

Use the pinned tool versions and macOS settings documented in README.md:

```sh
cargo +1.99.1 test --locked --release --test upstream_comparison -- --nocapture
cargo +1.99.1 bench --locked --bench primitives -- --compare > evidence/comparison-run-1.csv
cargo +1.99.1 bench --locked --bench primitives -- --compare > evidence/comparison-run-2.csv
cargo +1.99.1 bench --locked --bench primitives -- --compare > evidence/comparison-run-3.csv
```

The test regenerates its JSON counters and historical replay assertions. The
benchmark regenerates exact corpus files and raw CSV samples. Timing values
will vary. The committed report preserves this measured run and its provenance.
