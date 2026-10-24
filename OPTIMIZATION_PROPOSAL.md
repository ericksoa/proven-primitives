# Approved proof-preserving scalar optimizations

Status: the human explicitly approved both A and B in this chat on 2026-10-24.
Implementation, proof, and measurement results are in
[OPTIMIZATION.md](OPTIMIZATION.md).

The human requested optimization using the existing mathematical abstractions.
AGENTS.md reserves decisions about the implementation approach for the human;
the human approved the two concrete algorithm changes below separately.

## A. O(1) Base64 encoding size calculation

Replace only `base64::encoded_length`'s group-counting loop with the arithmetic:

```text
groups = input_length / 3 + (1 if input_length % 3 != 0 else 0)
if groups > destination_capacity / 4:
    return OutputTooSmall
return groups * 4
```

The existing `encoded_size_is_four_per_group` proof states the mathematical
size `4 * ((input_length + 2) / 3)`. Euclidean division relates this to the
quotient/remainder expression above. The implementation does not evaluate
`input_length + 2` in machine arithmetic. Prove that computing groups cannot
overflow, and that multiplication by four occurs only when its result fits
both the machine integer and the destination.

Effect: remove a linear group-counting preflight from the encoder. Encoding
itself remains linear in produced bytes. Keep the same exact private helper
contract, public errors, and unchanged-destination-on-error guarantee. Leave
Base64 decoding and its complete validation pass unchanged.
The O(1) statement concerns algorithmic work for sizing, not cryptographic
constant-time behavior.

## B. Specialize LZ4 matches with offset one

After the existing complete block validation, use this case in the match writer:

```text
if match_offset == 1:
    repeated_byte = destination[current_output_position - 1]
    write repeated_byte through the match destination using a bounded loop
else:
    use the existing general overlapping-match loop
```

The existing `matched(prefix, offset, count)` specification defines the copied
byte at position `i` using `i % offset`. With offset one this remainder is zero,
so every copied byte equals the last byte of the already produced prefix.
Prove the specialized loop refines that same specification, preserves the
destination frame, and maintains the existing byte-work bound.

Effect: remove the read-after-write chain from the repeated-byte workload.
The compiler may recognize the bounded constant-byte stores as a bulk fill;
performance remains a measured outcome. The general path and all format/end
rules remain unchanged. Offset zero is still invalid, and the repeated byte
must come from the current call's produced prefix.

## Scope and acceptance criteria for either approved choice

- Use the existing Rust 1.99.1 / Verus stack, approved dependencies, safe Rust,
  caller-owned buffers, bounded loops, constant extra storage, and no I/O or
  executable recursion in the primitive implementation.
- Keep every published specification, public API, error precedence, and buffer
  preservation guarantee. Add only private proof material needed to establish
  that the selected implementation satisfies the existing contracts.
- Add no SIMD intrinsics, lookup tables, new library-operation assumptions,
  external proof bodies, axioms, unchecked code, tools, dependencies, or CI.
- Recheck the entire crate with `--no-cheating`. Adapt the sizing mutation
  control to the selected arithmetic guard, and check a stale-byte mutation in
  the new offset-one path if B is approved. Keep specifications unchanged.
- Exercise exact/small capacities, malformed data, canonical Base64 boundaries,
  offset-one match lengths, and the existing upstream comparison corpus.
- Measure fresh baseline and candidate runs using the existing benchmark
  harness, frozen references, inputs, compiler, and three-process methodology.
  Retain original measurements and report changes per workload, including
  regressions and the remaining gap to upstream.

Proofs are erased before normal compilation. They do not automatically tell
LLVM how to optimize code. These changes express cheaper algorithms in safe
Rust and use the checker to establish that their behavior is still correct.
No speedup is claimed before measurement.

## Further mathematical directions for separate consideration

| Technique | Application | Main proof obligation |
|---|---|---|
| Periodicity and geometric expansion | General LZ4 match copying in progressively larger disjoint chunks | Each chunk equals the same periodic sequence, with no reads from old destination contents; total work remains linear |
| Concatenation laws / monoids | Batch Base64 groups and percent-encoding chunks | Base64 concatenation is valid at boundaries divisible by three; handle the final partial group separately |
| Finite-function and bit-vector reasoning | Verified scalar tables or packed-word byte transforms | Every table entry or machine-word transformation equals the existing byte specification; no cross-lane carry or bounds error |
| Abstract interpretation | Proved capacity bounds enabling guarded fast paths | The guard implies all later writes fit; retain complete validation wherever malformed suffixes can cause failure |
| Equality saturation / superoptimization | Search behaviorally equivalent candidate expressions and loops | Check each accepted candidate against the original specification; benchmark actual compiled code rather than trusting an abstract cost estimate |
| Amortized analysis and machine cost models | Bound copy phases and prioritize optimization effort | Distinguish total bytes, dependent operations, and memory traffic from actual measured latency |

These later directions are not implementation approvals. Relevant primary
background includes [the LZ4 block format](https://github.com/lz4/lz4/blob/dev/doc/lz4_Block_format.md),
[equality saturation](https://arxiv.org/abs/2004.03082), and
[bounded translation validation](https://web.tecnico.ulisboa.pt/nuno.lopes/pubs.php?id=alive2-pldi21).
