# Two further Base64 optimization iterations

This report records the approved C/D snapshot. Later E/F results and current
proof status are in [BATCHING.md](BATCHING.md).

The human approved C and D in [NEXT_ITERATIONS_PROPOSAL.md](NEXT_ITERATIONS_PROPOSAL.md).
C replaces executable encoding-character selection with a private immutable
64-byte alphabet table. D replaces executable decoding-character classification
with a private immutable 256-byte table, using 255 as the invalid sentinel.

**The C/D source passes 72 whole-crate verification checks with zero errors.**
The two table-backed helpers prove their original contracts against the same
mathematical `symbol` and `value` definitions. Public specifications, APIs,
padding rules, validation passes, error priority, buffer guarantees, dependencies,
safe Rust, and constant extra storage are retained.

## Separate measurements at 256 KiB

Each stage uses the same harness, compiler/profile, frozen references, and inputs,
with three processes and 27 batch-average latency samples per configuration.

| Workload | Baseline (microseconds/call) | C: encoding table | C+D: both tables | Combined speedup |
|---|---:|---:|---:|---:|
| Base64 encode | 433.542 | 224.359 | 225.609 | 1.92x |
| Base64 decode | 1364.983 | 1365.042 | 787.833 | 1.73x |
| LZ4 repeated-byte control | 6.844 | 6.833 | 6.958 | 0.98x |

C alone improved large-input encoding by about 1.93x and left decoding nearly
unchanged. D then improved decoding by about 1.73x. With both tables, encoding
remains about 1.92x faster than this round's baseline. Changes in the unchanged
LZ4 path are measurements of variability or layout effects, not an LZ4 algorithm
improvement attributed to these iterations.

No measured median latency among the 31 protected workload/size configurations
increased by more than five percent in this experiment. This observation is not
a statistical or cross-machine guarantee; every configuration and sample range
is retained in the machine-readable report.

## Remaining upstream gap

| Workload at 256 KiB | Current reference | Final / reference latency |
|---|---|---:|
| Base64 encode | base64_scalar | 2.47x |
| Base64 encode | base64_simd | 7.27x |
| Base64 decode | base64_scalar | 7.96x |
| Base64 decode | base64_simd | 17.27x |

The improvements reduce the gap but do not establish competitive SIMD throughput.
The results are for the stated synthetic workloads on an Apple M2 Pro, not for
every application or data distribution. No additional SIMD intrinsics, unsafe
implementation, dependency, or trusted table assumption was introduced.

## Why the proof is preserved

- The original piecewise mathematical alphabet and classifier remain unchanged.
  The checker verifies that every executable table lookup returns the specified
  value, including index bounds and the successful decoded-value range.
- Padding remains in the original parser, including canonical trailing-bit checks.
  Both decoding passes remain; validation still completes before output writes.
- The old and new routines satisfy the same deterministic contracts. Their
  specified input/output behavior is preserved under the Rust/Verus model.
  The report records an exact-text audit of public specifications and contracts.
- The unchanged LZ4 safety and byte-work proofs continue to pass.

## Regression and corruption evidence

C passed 71 checks, the existing runtime/comparison suite, and six deliberate
corruption controls. D passed 72 checks, the runtime/comparison suite, and seven
corruption controls. The additional control changes the executable decoding
table to accept NUL, and verification rejects it against the unchanged spec.

The current comparison test makes **151,860 calls with zero unexpected
differences**. It adds 1,024 cases by substituting every byte value in each of
four positions of a four-character group, comparing the actual compiled APIs
with the pinned reference. Counts are calls, not unique inputs or proof coverage.
The existing historical LZ4 disclosure replay and intentional contract differences
remain documented. The current counters are in
[the table-iteration comparison report](evidence/tables-upstream-comparison.json).

The previous 150,836-call report is preserved at its original path so older
measurement records still resolve to their recorded hashes. Tests establish
finite compatibility evidence, not universal equivalence to upstream source.

## Source identities, raw samples, and reproduction

The [machine-readable report](evidence/tables.json) binds the baseline and both
candidate stages to source and measured-executable hashes. Each stage has 78 configurations and 2,106 samples,
for 6,318 retained samples across the three stages.

Raw baseline runs: [1](evidence/tables-baseline-run-1.csv),
[2](evidence/tables-baseline-run-2.csv), [3](evidence/tables-baseline-run-3.csv).
Encoding-only runs: [1](evidence/tables-encoding-run-1.csv),
[2](evidence/tables-encoding-run-2.csv), [3](evidence/tables-encoding-run-3.csv).
Both-table runs: [1](evidence/tables-decoding-run-1.csv),
[2](evidence/tables-decoding-run-2.csv), [3](evidence/tables-decoding-run-3.csv).

The [encoding-only patch](evidence/tables-encoding.patch), applied to the recorded
baseline with `git apply --unidiff-zero evidence/tables-encoding.patch`,
reconstructs C for independent checking. The final repository source contains
C+D. No complete intermediate source copy is maintained behind the API.

Use the pinned versions and platform settings from README.md:

```sh
cargo +1.99.1 verus build --fwd-verus-args-to roots --locked --release -- \
  --no-cheating --num-threads 1 --triggers-mode silent --rlimit 60
cargo +1.99.1 test --locked --release
VERUS_ROOT=/path/to/pinned/verus cargo +1.99.1 test --locked --release \
  --test proof_rejection -- --ignored --nocapture
cargo +1.99.1 bench --locked --bench primitives -- --compare
```

Repeat the benchmark in three processes to reproduce the sampling protocol.
The harness validates outcomes outside timing and rotates implementation order.
Engine construction, allocations, input generation, warmup, output reset, and
reporting remain outside timing. These are warm batch-average latencies, not
application p95/p99, cold-cache measurements, or cryptographic timing guarantees.
Timing values will vary.
