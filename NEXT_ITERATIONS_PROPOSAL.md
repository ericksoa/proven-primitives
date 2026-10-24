# Approved next two Base64 optimization iterations

Status: the human explicitly approved both C and D in this chat on 2026-10-24.
Completed results and reproducible evidence are in
[TABLE_ITERATIONS.md](TABLE_ITERATIONS.md).

The human requested another couple of measured iterations. The previous
optimization approval explicitly excluded lookup tables, so these two exact
choices received separate approval under AGENTS.md.

## C. Encoding alphabet lookup

Replace only the private executable `base64::to_symbol` conversion with an
indexed lookup in a private immutable compile-time `[u8; 64]` alphabet array:

```text
ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/
```

Keep the existing piecewise mathematical `symbol` specification unchanged.
Prove that every indexed result for `v < 64` equals `symbol(v)`, including the
index bound. Leave encoding group construction, padding, size checking, and
the public API unchanged. This replaces repeated range classification with
one table access; any speedup must be measured.

## D. Decoding byte classification lookup

Replace only the private executable `base64::from_symbol` classification with
an indexed lookup in a private immutable compile-time `[u8; 256]` array:

- `A` through `Z` map to 0 through 25.
- `a` through `z` map to 26 through 51.
- `0` through `9` map to 52 through 61.
- `+` maps to 62 and `/` maps to 63.
- Every other byte maps to the invalid sentinel 255, including `=`.

Return `None` for sentinel 255 and `Some(value)` otherwise. Keep the existing
mathematical `value` specification unchanged, and prove equality and the
0-through-63 bound for all 256 input bytes.

The existing parser continues to handle padding separately. Retain the entire
validation pass, canonical padding/trailing-bit checks, malformed-input error
precedence, unchanged destination on error, and unchanged suffix on success.
Apply this same helper in both existing decoding passes without merging them.

## Execution and acceptance scope

- Attempt C first, prove and measure it separately, then attempt D as the next
  iteration. Keep source identities and measurements for each stage.
- Keep the current Rust/Verus versions, dependencies, safe Rust, caller-owned
  buffers, bounded loops, and constant extra storage. The two immutable arrays
  contain 320 bytes in total. Introduce no heap allocation or executable
  recursion in the primitive library.
- Do not add SIMD intrinsics, packed-word transforms, loop unrolling, services,
  tools, dependencies, public APIs, or new proof assumptions in these iterations.
- Keep all published specifications and public contracts unchanged. Verify
  the actual table-backed executable code with the existing checker; no
  unchecked wrappers, external proof bodies, or assumptions about table contents.
- Re-run whole-crate verification with `--no-cheating`, runtime regressions,
  the upstream comparison corpus, and applicable proof-rejection controls.
  Adapt the alphabet mutation to the new executable table and add a decoding
  table corruption control. Do not mutate specifications to obtain a pass.
- For the decoding table, supplement comparison coverage by substituting
  every byte value into each position of a four-character group and checking
  the actual APIs against the approved reference. This tests compiled behavior
  beyond the mathematical table-entry proof.
- Use the existing benchmark harness, frozen references, unchanged workloads,
  and three-process repeated-batch method. Retain a fresh baseline and per-stage
  raw samples; report all measured changes and remaining upstream gaps.
- Reject a candidate if its proof cannot be completed within the approved
  trust boundary. Record non-improvements rather than claiming a gain. Seek
  human review before accepting a material performance tradeoff or changing
  this implementation scope.

Lookup tables do not imply cryptographic constant-time behavior. No such
guarantee is added to the existing contracts.
