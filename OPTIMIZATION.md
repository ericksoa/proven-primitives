# Proof-preserving scalar optimization results

This report records the approved A/B snapshot. Later C/D results and current
proof status are in [TABLE_ITERATIONS.md](TABLE_ITERATIONS.md).

The human approved the two algorithms in [OPTIMIZATION_PROPOSAL.md](OPTIMIZATION_PROPOSAL.md).
Both are implemented in the same verified source, with the same public contracts,
approved toolchain, dependencies, safe Rust, constant extra storage, and validation
before writes. The complete crate passes **70 checks with zero errors** using
`--no-cheating`. Six deliberate defects are rejected, including a stale-byte
mutation of the new fill path.

## What the mathematics changed

**Base64 sizing uses Euclidean division.** If `n = 3q + r`, the output has
`q + (r != 0)` four-byte groups. The implementation avoids computing `n + 2`
in a machine integer and checks `groups <= capacity / 4` before multiplying.
The existing encoded-size theorem proves the same result as the previous counting
loop. Sizing is now O(1) in input length; encoding still writes O(n) bytes. This
is an algorithmic-work statement, not a cryptographic constant-time claim.

**LZ4 offset-one matches use periodicity.** In the existing sequence specification,
`i % 1 == 0`, so all match bytes equal the last already produced byte. The writer
captures it once and uses a bounded fill loop. A private step lemma connects this
loop to the same match specification. One read plus k writes is at most 2k for
a nonempty match, preserving the published abstract byte-work bound. The general
overlapping-copy path, format rules, and whole-input validation are retained.

Inspection of the measured writer shows a byte broadcast (`dup.16b`) and vector
stores (`stp q0, q0`) emitted by LLVM. No SIMD intrinsics or unsafe implementation
code were added. The compiler remains trusted; this inspection is not a proof
of the generated machine code.

## Measured changes at 256 KiB

Fresh baseline and optimized runs used the same harness, frozen references,
inputs, compiler/profile, and host. Each side has three process runs and 27
batch-average latency samples per configuration.

| Workload | Baseline (microseconds/call) | Optimized (microseconds/call) | Baseline / optimized |
|---|---:|---:|---:|
| Base64 encode | 627.927 | 432.062 | 1.45x |
| Base64 decode (unchanged algorithm) | 1358.700 | 1370.875 | 0.99x |
| LZ4 repeated-byte overlap | 460.052 | 6.922 | 66.46x |
| LZ4 literal-only | 7.941 | 7.762 | 1.02x |
| LZ4 upstream-compressed periodic input | 8.511 | 8.427 | 1.01x |

**The targeted gains are about 1.45x for large Base64 encoding and 66.46x for
the repeated-byte LZ4 workload.** Results below 1x are slower measurements, not
improvements. The full report retains every workload, size, and sample range;
small changes in unaffected paths should not be interpreted as established gains.

## Remaining gap to current upstream

| Workload at 256 KiB | Current reference | Optimized / reference latency |
|---|---|---:|
| Base64 encode | base64_scalar | 4.78x |
| Base64 encode | base64_simd | 13.94x |
| Base64 decode | base64_simd | 30.02x |
| LZ4 repeated-byte overlap | lz4_flex_safe | 1.67x |
| LZ4 literal-only | lz4_flex_safe | 1.50x |
| LZ4 upstream-compressed periodic input | lz4_flex_safe | 1.06x |

These two changes do not close the Base64 throughput gap. The repeated-byte
LZ4 result is specific to an offset-one workload, not a universal speedup for LZ4.
Reference runtimes also varied between the baseline and optimized processes;
the machine-readable report retains reference-normalized speedups alongside
absolute before/after timings. No fastest-implementation or machine-cycle theorem
is claimed.

## Correctness and security evidence

- The unchanged specifications still establish exact outputs, checked arithmetic
  and bounds, termination, error precedence, unchanged buffers on error, and
  preserved suffixes on success. The LZ4 input-only output corollary is retained.
- All nine primitive runtime test groups, the proof-source audit, and the
  upstream comparison test passed. The 150,836 comparison calls still have zero
  unexpected differences, with the same documented intentional contract differences.
- The initialized-buffer historical LZ4 disclosure still reproduces in the old
  reference and is rejected by the protected implementation.
- The negative-control suite first verifies the unchanged candidate, then rejects
  six separately mutated implementations while keeping specifications intact.
- The Base64 size-guard mutation was adapted to the new arithmetic check. The
  added LZ4 mutation captures the current unproduced destination byte instead
  of the last produced byte. This specifically checks the new security-sensitive path.

Tests and mutation controls supplement the universal source-level contracts.
They do not establish universal equivalence to upstream implementations or
correctness of the compiler, operating system, or hardware.

The old and optimized routines both satisfy the same deterministic published
specifications, so their specified input/output behavior is preserved under the
Rust/Verus model. The report also records an exact-text audit showing that the
public specifications and executable contracts in both changed modules match
the baseline. This claim concerns our two verified versions; the upstream
references remain outside that proof.

## Retained measurements and reproduction

The [machine-readable report](evidence/optimization.json) binds the baseline
and optimized source hashes to 78 configurations per side. It includes all medians and sample ranges,
reference identities, and the measured optimized executable hash.

Each dataset contains 2,106 samples. Raw baseline runs:
[1](evidence/optimization-baseline-run-1.csv), [2](evidence/optimization-baseline-run-2.csv),
[3](evidence/optimization-baseline-run-3.csv). Raw optimized runs:
[1](evidence/optimization-run-1.csv), [2](evidence/optimization-run-2.csv),
[3](evidence/optimization-run-3.csv).

This uses the [existing comparison methodology](COMPARISON.md): warm repeated
batches, rotated implementation order, preallocated outputs, construction and
validation outside timing, and black-boxed calls. It does not measure application
p95/p99, cold-cache behavior, other hosts, or security against timing side channels.

With the pinned tools and macOS settings from README.md:

```sh
cargo +1.99.1 verus build --fwd-verus-args-to roots --locked --release -- \
  --no-cheating --num-threads 1 --triggers-mode silent --rlimit 60
cargo +1.99.1 test --locked --release
VERUS_ROOT=/path/to/pinned/verus cargo +1.99.1 test --locked --release \
  --test proof_rejection -- --ignored --nocapture
cargo +1.99.1 bench --locked --bench primitives -- --compare
```

Repeat the comparison benchmark in three processes. To reproduce the baseline,
use the recorded baseline commit in a separate checkout. Timing values will vary.
The original historical comparison report and its raw runs are preserved.

This snapshot implements only A and B. The subsequent table experiments were
approved separately; other proposed mathematical techniques remain options for
a future human-approved step.
