# Approved Base64 batching experiment

Status: the human explicitly approved E and F as written on 2026-10-24.
Completed results and reproducible evidence are in [BATCHING.md](BATCHING.md).

The baseline source, 72-check proof record, compatibility counters, and
measured results are identified in [TABLE_ITERATIONS.md](TABLE_ITERATIONS.md).

## Question and fixed requirements

Can processing two complete Base64 groups per iteration reduce execution cost
while the same executable source still proves the existing contracts?

Retain Rust 1.99.1, the pinned Verus stack, Cargo.lock, approved references and
features, safe Rust, bounded loops, caller buffers, constant extra storage,
and the existing public API. Keep all public mathematical specifications and
contracts byte-for-byte unchanged. In particular, preserve canonical padding
and trailing bits, malformed-input priority, unchanged destination on error,
and unchanged suffix on success.

No new dependencies, tools, services, CI, APIs, CPU-specific intrinsics, unsafe
code, proof assumptions, external implementation bodies, or larger lookup tables
are proposed. Changes to LZ4 and percent encoding are outside this experiment.

## E. Encode six input bytes into eight characters

After the existing overflow-safe size check, add a bounded loop for complete
six-byte chunks. Assemble the six individually indexed bytes into the lower
48 bits of a `u64`, with the first input byte at bits 40 through 47. Use
explicit shifts and bitwise OR; no pointer casts or native-endian loads.

Extract eight six-bit values at shifts 42, 36, 30, 24, 18, 12, 6, and 0, mask
each with 63, and convert through the existing proved alphabet helper. Store
the eight characters in a fixed `[u8; 8]` temporary and use the existing
`copy_bytes` helper. Advance the input by six and the output by eight.

When fewer than six input bytes remain, use the existing group loop and padding
helper. This retains the original handling of zero through five remaining
bytes, including a final partial group.

Prove that the packed value stays below 2^48, shifts and indices are valid,
each extracted digit matches the corresponding original group calculation,
and the eight-character result equals the concatenation of two existing
`quantum` results. Lift that result through the existing concatenation laws
to the unchanged `encoded` contract and buffer frame.

## F. Decode eight characters into six output bytes

Keep `decoded_length` and its complete validation pass unchanged. Only after
that pass succeeds, add a writer loop processing eight characters at a time
while at least twelve input characters remain. Leaving the final group for
the existing path ensures that the batch never includes padding.

Read the eight character values through the existing immutable decoding table.
Prove from the validated input that each value is below 64 and equals the
existing mathematical classifier; do not assume table correctness or input
validity. Pack the values into the lower 48 bits of a `u64` using shifts
42 through 0 in steps of six. Extract six bytes at shifts 40, 32, 24, 16, 8,
and 0, masking each with 255. Use individually indexed reads, a fixed
`[u8; 6]` temporary, and the existing `copy_bytes` helper.

Advance input by eight and output by six. The existing decoder writer loop
handles the remaining one or two groups, including canonical padding.
Prove equivalence to two successive original decode steps, all arithmetic and
buffer bounds, and preservation of the unchanged `decoded` contract.

## Staging and acceptance evidence

Attempt E first and record its exact source and measurements. Attempt F next
and retain an independently reconstructable E-only patch. A failed proof or
missing gain is an experimental result, not permission for another approach.

For each stage:

- Run whole-crate verification with the existing `--no-cheating` settings;
  keep the old mathematical definitions and all public contracts unchanged.
- Run the existing release regressions, source audit, historical security
  replay, and pinned upstream comparisons. Keep intentional upstream contract
  differences explicitly classified.
- Add boundary comparisons for input lengths zero through 64 with exact,
  undersized, and oversized buffers. Cover both batch and remainder paths,
  partial final groups, malformed suffixes, and complete buffer preservation.
- For F, substitute all 256 byte values into each of the first eight positions
  of a twelve-character group, comparing both compiled APIs at sufficient
  output capacity. These 2,048 calls exercise batch-position classification;
  they do not establish universal upstream equivalence.
- Keep all seven existing corruption controls. Add a wrong encoding extraction
  shift for E and a wrong decoding extraction shift for F. Each control must
  be rejected against unchanged specifications after an unchanged positive
  control passes.
- Use the existing benchmark harness, sizes, malformed workloads, frozen
  references, compiler/profile, and three-process/nine-batch method. Retain
  fresh baseline, E-only, and E+F samples and source/executable hashes.

The proposed performance goal is at most twice the scalar reference's median
latency for both Base64 directions at 4 KiB and 256 KiB. Continue to report the
SIMD comparison. This is an experimental target, not a promised result or a
proof obligation. Report every protected workload and size. A median regression
above five percent triggers a fresh three-process confirmation; accepting a
confirmed material tradeoff requires human review. Do not weaken correctness
requirements to meet the performance goal.

## Specification review and independent reproduction

Prepare a review map from RFC 4648 sections 3 and 4 to the existing alphabet,
padding, trailing-bit, length, and error contracts. Label review performed by
the implementation author as self-review. An independent review or reproduction
remains pending until a separate person actually performs it.

Publish the approved implementation's source identities, proof results,
corruption controls, finite compatibility results, raw timings, and reproduction
instructions in the existing repository report format. These artifacts support
independent checking; their existence is not an independent review result.
Contacting reviewers is outside this proposal.

## Approval scope

Approval covers E and F as written, including their staged checks,
measurements and supporting evidence above. It does not change the documented
proof trust boundary.
