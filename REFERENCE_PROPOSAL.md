# Approved upstream comparison references

Status: the human explicitly approved these exact comparison dependencies and
feature configurations in this chat on 2026-10-23.

The human approved starting the LZ4 and Base64 security case studies and
preparing upstream comparisons, then separately approved the exact reference
dependencies below as required by AGENTS.md.

## Exact approved dependency changes

These three development dependencies are added to the existing Cargo package. They
are for local tests and benchmarks; the library's normal dependency set stays
unchanged. Use the existing Rust 1.99.1 toolchain and standard-library test and
benchmark harnesses.

```toml
[dev-dependencies]
base64_ref = { package = "base64", version = "=0.23.1" }
lz4_ref = { package = "lz4_flex", version = "=0.14.0", default-features = false, features = ["std", "safe-encode", "safe-decode", "checked-decode"] }
lz4_vulnerable = { package = "lz4_flex", git = "https://github.com/PSeitz/lz4_flex", rev = "975bfa7ac9583da879b5d7578b423232d84f69fe", default-features = false, features = ["std", "safe-encode", "safe-decode", "checked-decode"] }
```

| Reference | Source identity | Purpose |
|---|---|---|
| base64 0.23.1 | Tag v0.23.1, commit 069bf7067b949f5c0a92b6ceb82492920502f2c2 | Current strict padded standard-alphabet caller-buffer encoding and decoding |
| lz4_flex 0.14.0 | Tag 0.14.0, commit 1bffdcbbf906a234b913937cb2f57c0245915038 | Current independent raw-block decompression and generation of valid compressed inputs |
| lz4_flex 0.12.0 | Commit 975bfa7ac9583da879b5d7578b423232d84f69fe | Historical CVE-2026-32829 replay using safe decoding and initialized buffers |

Registry checksums:

- base64 0.23.1: ac07cdecf99051d9a5238b80f35af32cdeba5b336e55d957b318b50137e18da5
- lz4_flex 0.14.0: ecbdfe44b1bd960b68170b417450a628c43f7cf56bb3c5317e61cb230ee7f226

The current Base64 package's default features are std and simd-unsafe. This
permits upstream optimized code in the comparison process; it adds no unsafe
code to Proven Primitives and supplies no proof assumptions. The selected
upstream engine must be named in each result rather than implied to use SIMD.

The proposed LZ4 configurations retain checked decoding and safe encode/decode
features. Frame support is disabled because our API covers raw blocks. This
avoids the optional twox-hash dependency. These configurations introduce no
transitive normal or build packages. Upstream development dependencies are not
included: the proposal does not claim to run their entire internal test suites.

Version 0.12.0 is yanked, so the historical replay uses its exact Git commit
rather than bypassing registry resolution or editing a lockfile by hand.

## Comparison scope

- Pin source commits, package checksums, features, compiler flags, and input
  corpus identities in published results.
- Preserve assertions when adapting applicable upstream vectors and regression
  cases. Record their original source and license, and list excluded features.
- Compare current references with our routines on the overlapping documented
  modes. Classify every disagreement in acceptance, errors, returned lengths,
  output bytes, and buffer side effects.
- Our unchanged-output-on-error guarantee and strict LZ4 end rules are part of
  our contract, even when an upstream implementation is more permissive.
- Use the historical LZ4 version only as a local initialized-buffer regression
  control. Compare performance and current compatibility against 0.14.0.
- Do not install historical Base64. Reproduce its original sizing arithmetic
  with bounded integer calculations, explicitly distinguishing that from
  running the old encoder with an impractically large allocation.
- Measure caller-buffer paths, small-input latency, large-input throughput,
  valid and malformed workloads, and repeated-run variation. Keep input
  generation and allocations outside timed regions where both APIs permit it.
- Differential tests establish tested compatibility. They do not prove
  universal equivalence to upstream source. No such theorem is claimed here.

## Primary sources

- https://github.com/marshallpierce/rust-base64/tree/069bf7067b949f5c0a92b6ceb82492920502f2c2
- https://github.com/PSeitz/lz4_flex/tree/1bffdcbbf906a234b913937cb2f57c0245915038
- https://github.com/PSeitz/lz4_flex/security/advisories/GHSA-vvp9-7p8x-rfvv
- https://github.com/marshallpierce/rust-base64/commit/24ead980daf11ba563e4fb2516187a56a71ad319
