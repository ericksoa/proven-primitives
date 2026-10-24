# Batched Base64 validation results

This report records the approved G snapshot with 83 checks. Later proof-only
security corollaries and current status are in
[SECURITY_CONTRACTS.md](SECURITY_CONTRACTS.md).

The human approved G in [VALIDATION_BATCH_PROPOSAL.md](VALIDATION_BATCH_PROPOSAL.md).
The validator now checks eight nonfinal characters using the existing table
and a proved bitwise-OR predicate. It counts six decoded bytes per valid batch.
It still validates the complete input before writing and leaves the final
one or two groups to the original padding-aware parser.

**The G snapshot passes 83 verification checks with zero errors**, release
regressions, 154,498 comparison calls with zero unexpected differences, and
eleven deliberate-defect rejection controls. Public specifications/contracts,
the E/F writer and encoder, the other primitives and dependencies are unchanged.

## Fresh measurements at 256 KiB

| API path | Baseline us/call | G us/call | Speedup |
|---|---:|---:|---:|
| Successful decode | 541.658 | 305.500 | 1.77x |
| Valid input, small output | 360.958 | 129.392 | 2.79x |
| Late invalid input | 359.358 | 129.075 | 2.78x |

No protected workload/size median regressed by more than five percent in
these runs, so the specified confirmation trigger did not fire. This is an
observation on this host, not statistical confidence or a performance guarantee.

| Direction | Logical size | Final/scalar latency | Final/SIMD latency |
|---|---:|---:|---:|
| Encode | 4,096 bytes | 1.91x | 5.53x |
| Encode | 262,144 bytes | 1.89x | 5.56x |
| Decode | 4,096 bytes | 3.11x | 6.71x |
| Decode | 262,144 bytes | 3.09x | 6.73x |

Encoding continues to meet the goal of at most twice scalar latency at both
4 KiB and 256 KiB. **Decoding still misses that goal**. The small-output and
late-invalid paths do no output writing, but their timings are API-path
comparisons rather than an exact decomposition of successful decoding cost.

## Proof and security evidence

- `validation_table_matches` proves that a table result is below 64 exactly
  when the original classifier accepts the character.
- `validation_or_bits` proves the eight-value OR test is equivalent to all
  eight individual range tests. No assumed table or unchecked bit operation
  is introduced.
- `valid_batch` connects this predicate to two original full-group parses.
  The validator loop then refines the original sequence specification and
  bounded capacity counter, including checking later bytes after output is
  already known too small.
- Existing padding, trailing-bit, suffix and whole-buffer error guarantees
  remain. The encoder and successful decoder writer are exactly unchanged.
- All nine prior corruption controls remain. Two additional controls accept
  an invalid sentinel or return a small-output error before a malformed tail;
  verification rejects both against unchanged contracts after a passing
  unchanged positive control.
- Fourteen explicit small-output/malformed-tail comparisons supplement the
  existing exhaustive batch-position, boundary and historical security cases.
  Finite comparisons remain distinct from universal upstream equivalence.

## Reproduction and provenance

The [machine-readable report](evidence/validation.json) binds the fresh baseline
to the candidate source, executable and raw-sample hashes. It records all 78 configurations, unchanged-function
and contract hashes, exact references and both stages. There are 2,106 samples
per stage and 4,212 total.

Raw baseline runs: [1](evidence/validation-baseline-run-1.csv), [2](evidence/validation-baseline-run-2.csv), [3](evidence/validation-baseline-run-3.csv).
Raw G runs: [1](evidence/validation-run-1.csv), [2](evidence/validation-run-2.csv), [3](evidence/validation-run-3.csv).

Current [comparison counters](evidence/validation-upstream-comparison.json) are
retained separately from earlier reports so their recorded hashes remain valid.
Use the pinned proof, release-test, corruption-control and comparison-benchmark
commands in [README.md](README.md); repeat benchmarks in three processes.
The unchanged harness rotates implementation order and excludes allocation,
generation, construction, warmup and reset from timing.

These are warm batch-average measurements on one Apple M2 Pro. They are not
single-request tail latencies, cold-cache results or cryptographic timing
guarantees. Source-level proof assumptions and the compiler/OS/hardware boundary
remain documented in [PROOFS.md](PROOFS.md). The [Brotli roadmap](ROADMAP.md)
is a candidate research scope; no Brotli implementation or dependency is added.
