# Approved G: batched Base64 validation

Status: the human explicitly approved G as written on 2026-10-24. This separate
approval permits the validator change that the earlier E/F approval excluded.
Completed results and reproducible evidence are in [VALIDATION.md](VALIDATION.md).

## Evidence and hypothesis

The retained confirmation series in [BATCHING.md](BATCHING.md) measures these
256 KiB logical-input API paths:

| Path | Median microseconds per call |
|---|---:|
| Successful decode | 533.542 |
| Valid input, destination one byte too small | 355.633 |
| Invalid byte at the end | 355.333 |

The small-output path validates the complete input and returns without writing.
Its latency is about two thirds of the successful path's latency. This is an
API-path comparison, not a precise phase profile or proof of where every cycle
is spent. Current compiled code retains calls to `read_quantum` in validation;
the successful writer already has the approved eight-character batching path.

Hypothesis: classifying nonfinal groups in batches can reduce validation work
while preserving the complete validation pass and its exact error contract.

## Exact proposed change

In `decoded_length`, process eight characters per iteration while at least
twelve remain. Leave the remaining one or two groups to the existing parser,
including final padding and canonical trailing-bit validation.

For each batch, read eight values from the existing 256-byte decoding table
and combine them using bitwise OR. Values are either 0 through 63 or sentinel
255. The batch is valid exactly when the combined value is below 64. Prove
that this predicate is equivalent to all eight characters being valid,
unpadded alphabet characters and to two successful full decoding groups.
Do not construct decoded output bytes in this validation helper.

For a valid batch, account for six decoded bytes using the existing bounded
counter/small-buffer flag scheme: compare six with `capacity-count` before
incrementing. Once the destination is known too small, continue checking every
remaining input character. Return `OutputTooSmall` only after all input is
valid; a malformed later batch or tail must still return `InvalidInput`.
The validator writes no destination bytes.

Use private checked lemmas to connect the OR predicate, original classifier,
two-group prefix, counter and unchanged `decoded_length` contract. Keep all
public mathematical definitions and contracts byte-for-byte unchanged. The
successful E/F writer, remainder path, alphabet tables, encoder and other
primitives retain their existing implementations.

## Constraints and acceptance

Retain safe Rust, bounded loops, constant extra storage, caller-owned buffers,
the current pinned Rust/Verus versions, approved dependencies, tables, references
and proof trust boundary. Add no SIMD, unsafe code, allocations, merged
validation/writing pass, new API, tool, service, assumption or external body.

Run whole-crate proofs, release tests, the current comparison corpus and all
nine corruption controls. Add controls that incorrectly accept an invalid
sentinel and return early for a small destination before a malformed suffix.
Verify rejection against unchanged contracts after an unchanged positive
control. Retain the existing batch-position and malformed-suffix assertions.

Measure a fresh baseline and candidate using the same 78-configuration harness,
three processes and nine batches. Retain all samples, exact source/executable
identities, successful/small-output/late-invalid paths and upstream gaps.
A protected median regression above five percent triggers a fresh baseline
and candidate confirmation; a confirmed material tradeoff requires human review.
The existing goal remains no more than twice current upstream scalar latency
at 4 KiB and 256 KiB; report a miss without changing the contracts.

Approval covers this specific validation batching approach and its proof,
regression, measurement and publication evidence. Other optimization choices
still require separate human approval.
