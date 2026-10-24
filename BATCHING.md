# Base64 batching: proofs and measured results

This report records the approved E/F snapshot.
Subsequent G validation results and current proof status are in
[VALIDATION.md](VALIDATION.md).

The human approved E and F in [BATCHING_PROPOSAL.md](BATCHING_PROPOSAL.md).
E encodes six bytes into eight characters using explicit 48-bit packing in
a `u64`. F decodes eight characters into six bytes after the unchanged
complete validation pass. Both use safe indexed reads, fixed temporary arrays,
the existing tables and copy helper, and the original remainder/padding path.

**The final crate passes 79 verification checks with zero errors**, a release
build and regressions, 154,484 upstream comparison calls with zero unexpected
differences, and nine deliberate-defect rejection controls. All public
specifications and contracts, dependencies and proof trust assumptions remain
unchanged. Check counts are not a percentage of the input space.

## Initial staged measurements at 256 KiB

| Workload | Baseline us/call | E only | E+F | Combined speedup |
|---|---:|---:|---:|---:|
| Encode | 230.229 | 172.500 | 173.859 | 1.32x |
| Decode | 790.758 | 787.108 | 537.717 | 1.47x |

## Fresh confirmation and remaining performance gap

One initial protected workload, unchanged LZ4 offset-one decoding at 4 KiB,
measured 8.6% slower and triggered the agreed confirmation. The fresh series
rebuilt the exact baseline and final sources and ran each in three processes.
The corresponding LZ4 median was about 1.8% slower in this repeat. No protected
workload/size median regressed by more than five percent in the confirmation.
Both series are retained. This does not establish statistical confidence or
rule out regressions on other machines or data.

| Workload | Logical size | Confirmation speedup | Final/scalar latency | Final/SIMD latency |
|---|---:|---:|---:|---:|
| Encode | 4,096 bytes | 1.29x | 1.91x | 5.53x |
| Encode | 262,144 bytes | 1.31x | 1.88x | 5.51x |
| Decode | 4,096 bytes | 1.48x | 5.32x | 11.53x |
| Decode | 262,144 bytes | 1.47x | 5.34x | 11.50x |

The goal of no more than twice upstream scalar latency at both 4 KiB and
256 KiB was met for encoding in both series. **Decoding did not meet that
goal**. The full validator remains unchanged; these timings do not isolate
its contribution or establish which further change would close the gap.

## Proof and security evidence

- E passes 75 whole-crate checks; E+F passes 79. Both use the existing
  `--no-cheating` checker settings, with no admitted or external proof bodies.
- Checked bit-vector lemmas establish the 48-bit bounds and individual
  extractions. The executable helpers refine two original mathematical groups;
  sequence laws and writer invariants lift them to the unchanged public API.
- Decoder values are proved valid from the complete validation result. The
  final group still uses the original canonical padding and trailing-bit checks.
  Invalid-input priority and complete error-buffer preservation remain proved.
- The original Base64 sizing-overflow and LZ4 stale-buffer security properties
  and historical replay remain intact. See [SECURITY_CASES.md](SECURITY_CASES.md).
- The source audit confirms exact equality of public specifications/contracts
  and of the complete `decoded_length` validator against the recorded baseline.
- E rejects eight implementation corruptions; E+F rejects nine, each after a
  passing unchanged positive control. The two additional controls change an
  encoding or decoding extraction shift without changing any specification.

The comparison corpus retains boundary lengths zero through 512 with exact,
undersized and oversized destinations and three generated patterns. It adds
576 malformed-suffix comparisons and 2,048 substitutions covering all 256
bytes in all eight batch positions of a twelve-character group. The helper
checks complete error buffers and successful suffixes. Counts are API calls;
these tests do not prove universal equivalence to upstream implementations.

The [RFC map](BASE64_SPEC_REVIEW.md) is an author self-review. Independent
specification review and reproduction remain pending.

## Reproducible artifacts

The [machine-readable report](evidence/batching.json) records source, executable
and raw-sample hashes; unchanged-contract and validator identities; all 78
configurations per stage; medians and ranges; exact references; and both
measurement series. There are 2,106 samples per stage and 10,530 total across
the three initial stages and two confirmation stages.

Initial raw runs:

- Baseline: [1](evidence/batching-baseline-run-1.csv), [2](evidence/batching-baseline-run-2.csv), [3](evidence/batching-baseline-run-3.csv).
- E only: [1](evidence/batching-encoding-run-1.csv), [2](evidence/batching-encoding-run-2.csv), [3](evidence/batching-encoding-run-3.csv).
- E+F: [1](evidence/batching-decoding-run-1.csv), [2](evidence/batching-decoding-run-2.csv), [3](evidence/batching-decoding-run-3.csv).

Confirmation raw runs:

- Baseline: [1](evidence/batching-confirm-baseline-run-1.csv), [2](evidence/batching-confirm-baseline-run-2.csv), [3](evidence/batching-confirm-baseline-run-3.csv).
- E+F: [1](evidence/batching-confirm-decoding-run-1.csv), [2](evidence/batching-confirm-decoding-run-2.csv), [3](evidence/batching-confirm-decoding-run-3.csv).

The [E-only patch](evidence/batching-encoding.patch), applied with
`git apply --unidiff-zero` to the baseline identified in the machine-readable
report, reconstructs every recorded E-stage source hash, including the applicable
tests. The final source contains E+F.
Current comparison counters are in [this report](evidence/batching-upstream-comparison.json);
the [E-only counters](evidence/batching-encoding-comparison.json) are retained
separately. Earlier reports and their hashed compatibility files are preserved.

Use the pinned tools and platform settings in [README.md](README.md):

```sh
cargo +1.99.1 verus build --fwd-verus-args-to roots --locked --release -- \
  --no-cheating --num-threads 1 --triggers-mode silent --rlimit 60
cargo +1.99.1 test --locked --release
VERUS_ROOT=/path/to/pinned/verus cargo +1.99.1 test --locked --release \
  --test proof_rejection -- --ignored --nocapture
cargo +1.99.1 bench --locked --bench primitives -- --compare
```

Repeat benchmarks in three processes. The unchanged harness rotates execution
order and uses nine batch samples per configuration per process. Allocations,
input generation, engine construction, warmup and output reset stay outside
timing. Results are warm batch-average latencies on one Apple M2 Pro; they
are not application p95/p99, cold-cache or cryptographic timing guarantees.
Source-level proof assumptions and the compiler/OS/hardware boundary remain
as documented in [PROOFS.md](PROOFS.md).
