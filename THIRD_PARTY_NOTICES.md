# Third-party test material

The primitive implementation remains licensed under Apache-2.0. Selected
upstream test assertions and fixtures are adapted in
`tests/upstream_comparison.rs`; the upstream notices are preserved below.
These adaptations do not import upstream executable implementation into the
verified library.

| Project | Pinned source | Adapted assertions or fixtures | License notice |
|---|---|---|---|
| rust-base64 0.23.1 | 069bf7067b949f5c0a92b6ceb82492920502f2c2 | `tests/tests.rs::encode_engine_slice_error_when_buffer_too_small`; `tests/encode.rs::encode_all_bytes` | [MIT](third_party/licenses/base64-MIT.txt) |
| lz4_flex 0.14.0 | 1bffdcbbf906a234b913937cb2f57c0245915038 | Non-dictionary raw-block assertions from `src/block/decompress_safe.rs::test`, including `all_literal`, `incomplete_input`, `offset_oob`, and `offset_0` | [MIT](third_party/licenses/lz4_flex-MIT.txt) |

Reference packages are development dependencies with their own upstream
licenses. Their complete test suites, development dependencies, frame APIs,
dictionary APIs, and other encoding modes are not included in this adaptation.
