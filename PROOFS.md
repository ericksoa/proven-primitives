# Proof guide

## Reading the claims

The source of truth is each public function's `ensures` clause, not a test result
or a badge. A function with no well-formed-input precondition must handle every
byte input and every destination capacity admitted by its Rust slice types.

`src/lib.rs::written` states that the produced prefix equals the mathematical
result and that the destination suffix keeps its initial bytes. Error branches
require equality of the entire final destination and its original snapshot.

The implementation validates format and output size before writing. The writer
then refines the same specification while maintaining the buffer frame. Private
helper preconditions are checked at every call site; they do not become
unstated public input requirements.

## Percent encoding

`percent::escaped` specifies a single byte's URI-component representation.
`percent::encoded` concatenates those representations. The decoder grammar
recognizes either a literal byte or a complete hexadecimal escape.

`percent::round_trip` proves, by induction over arbitrary mathematical byte
sequences, that decoding an encoding returns the original bytes. The executable
loops separately prove refinement to those specifications and correct errors.

## Base64

`base64::quantum` specifies the RFC 4648 group transformation.
`base64::unquantum` specifies its inverse with canonical padding and trailing-bit
conditions. `base64::first` forbids padding before the final group.

`base64::quantum_round_trip` and `base64::quantum_canonical` establish the group
identities. `base64::round_trip` and `base64::canonical_round_trip` lift them to
arbitrary sequences. The buffer routines prove that their actual writes and
errors implement those specifications.

The private `base64::encoded_size_is_four_per_group` proof states the exact
mathematical padded size. Together with the checked executable size pass and
writer it connects arithmetic safety to the CVE-2017-1000430 failure class.
The executable helper now computes the number of four-byte groups using
quotient and remainder, compares it with `capacity / 4`, and multiplies only
after the comparison establishes safety. Its contract is unchanged, and its
work is independent of input length.

Private immutable encoding and decoding tables replace the executable
`to_symbol` and `from_symbol` range classifiers. Their original contracts still
require equality to the unchanged mathematical `symbol` and `value` functions.
Verification checks the actual array literals and indexed code for every
permitted index, including the invalid decoding sentinel and the 0-through-63
range of every successful lookup. Padding remains in the existing parser, and
both decoding passes are retained. See [TABLE_ITERATIONS.md](TABLE_ITERATIONS.md).

The later batching implementation explicitly packs 48 bits into a `u64`.
Private `encode_batch_bits` and `decode_batch_bits` lemmas use the existing
checker's bit-vector reasoning to prove the packing bounds and each extraction
against the original arithmetic group definitions. These are checked lemmas,
not assumptions. The batch helpers then prove equality to two original groups;
the writer loops lift that equality to the unchanged sequence and buffer
contracts. Decoder table values are proved valid from the successful validation
pass, and the final group stays on the original padding-aware path. The
validator itself was unchanged at that stage. See [BATCHING.md](BATCHING.md).

The later G validator uses `validation_table_matches` and `validation_or_bits`
to prove that a combined eight-value OR test accepts exactly two unpadded
alphabet groups. Its bounded count and small-output flag refine the original
`decoded_length` contract. It continues checking later groups after the buffer
is known too small, preserving malformed-input priority. The original tail
parser, encoder and successful writer are unchanged. See
[VALIDATION.md](VALIDATION.md).

## LZ4

`lz4::extension` and `lz4::length_field` define the length grammar.
`lz4::segment` defines literals, offsets, match lengths and end rules.
`lz4::matched` models an overlapping copy as repetition of the preceding
offset-sized window; `lz4::matched_step` proves its one-byte operational step.
`lz4::block_state` combines the segments into the decoded result.

The validator uses wide counters whose checked bounds cover every input length
admitted by the machine's slice type. It therefore keeps validating malformed
input even after the decoded size exceeds the destination: malformed input
still wins over `OutputTooSmall`.

The writer proves refinement to `block_state`, including its overlapping copy
loop. The original destination snapshot is explicitly maintained across nested
loops. Checked ghost counters account for forward header spans and byte copies;
the source-level cost model and its limits are stated in the README.

The private `lz4::decoded_prefix_is_independent_of_previous_output` proof derives
equal successful returned prefixes from the implementation's input-only output
contract. It makes explicit why old destination bytes cannot enter the result,
addressing the CVE-2026-32829 stale-buffer disclosure class. See
[the security case studies](SECURITY_CASES.md) for scope and regression evidence.

`lz4::matched_one_step` specializes the same periodic sequence at offset one:
every additional byte equals the last byte of the original produced prefix.
The new writer captures that byte once, then fills with a bounded loop. Its
work accounting charges one read plus one write per emitted byte; because a
match is nonempty, this remains at most two operations per emitted byte. The
general match writer and the published `2I + 2O` bound remain intact.

## Private Brotli B1 input/header core

`brotli_input::BitQueue::read_bits` proves minimal input acceptance, pending
capacity, exact little-endian field values, retained-bit conservation and
bounded append/extract/compaction work for widths 0 through 56. Its physical
view includes only valid pending bytes and the leading bit offset. The
`valid_bits_ignore_unused_storage` theorem makes the confidentiality consequence
explicit: unused array contents cannot change authorized retained bits.

`brotli_input::HeaderDecoder::advance_header` accepts only constructor/reset or
sticky terminal states. For an empty initial call it proves genuine nonfinal
exhaustion or final truncation. For every first byte it proves the exact RFC
7932 normal window result or reserved-pattern error, one-byte consumption and
retained payload bits. Complete/failed calls preserve their exact terminal
state and consume nothing; reset re-establishes the initial invariant.

These are root-checked implementation contracts, not isolated helper tests.
They do not implement compressed blocks, block switches or output and therefore
do not establish a complete Brotli decoder or the CVE-2026-111497 integration
obligation. See [BROTLI_B1.md](BROTLI_B1.md).

## Private Brotli B2 prefix/block-switch core

`brotli_prefix` validates bounded code lengths and exact Kraft-space use,
constructs canonical codes for every successful table, performs exact
code/width matching and implements the RFC 26-entry block-length ranges.
`brotli_block` proves bounded block histories/lengths across all three actual
dispatch categories. Its invalid-single-type guard precedes prefix parsing,
returns a permanent error without consuming a field and remains sticky.

The integrated `advance_from_prefixes` root connects successful prefix and
block-length results to that state transition. It does not connect a complete
RFC byte-stream parser or output decoder. See [BROTLI_B2.md](BROTLI_B2.md).

## C1 exact caller composition

`composition_demo::DecodeCaller::decode` proves exact Base64-to-percent stage
compatibility, current-prefix handoff, error ordering, buffer effects and
publication-state invalidation. Its relational corollary proves final-prefix
independence from old storage. Component loop ledgers plus checked expansion
lemmas establish the stated `21I + 56` successful-work upper bound. See
[COMPOSITION_C1.md](COMPOSITION_C1.md).

## Trust and erasure

The [security assessment](SECURITY_CONTRACTS.md) maps checked contracts and
private corollaries to explicit threats and remaining obligations. Base64 and
percent modules now include `encoded_prefix_is_independent_of_previous_output`
and `decoded_prefix_is_independent_of_previous_output`. Their premises are the
already checked `written` success postconditions, as in the existing LZ4
corollary; they introduce no assumption or separate information-flow model.
Private length lemmas establish Base64 decoded length and percent encoded/
decoded expansion bounds. All seven additions are proof-only. They do not
establish streaming/session, side-channel or whole-application guarantees.

The proof command passes `--no-cheating` to the project root. The crate adds no
assumptions, custom axioms, admitted proofs, external implementation bodies or
unchecked implementation shims. The standard library still supplies modeled
Rust operations and trusted specifications; root proof checks do not remove
that trusted base.

The same `verus!` bodies are processed for both verification and ordinary Cargo
compilation. Imports guarded by `cfg(verus_keep_ghost)` refer only to proof
material. They do not select a different executable implementation.

Some ghost branches contain `assert(false)` after a validated input is assumed
to fail a second parse. These are proof obligations establishing unreachability.
They are not assumptions: an unproved assertion makes verification fail.

## Evidence

The local proof record in `evidence/claims.json` identifies the checked source
hashes, tool versions and completed checks. Ordinary raw logs and standalone
benchmark results remain local. Upstream-comparison and optimization CSV runs
and their summaries are committed. The security checker JSON and normalized
defect-control diagnostics are committed too. Re-run the documented commands
after a code change; a previous proof record does not cover changed source.

The source-tree digest hashes the sorted source-manifest entries, each encoded
as the UTF-8 path, a NUL byte, its hexadecimal SHA-256 digest, and a newline.
Individual validation-source hashes identify the tests, benchmark, and example.

Upstream references are approved development dependencies. They supply no proof
assumptions and are not verified by the project's root proof checks. Passing
the comparison test establishes behavior on its exercised corpus; it does not
promote either upstream library into the trusted specifications or prove
universal equivalence to its source or executable artifact.

The security record compares the compiled benchmark artifact after these
proof-only additions with the measured G artifact. Byte identity is provenance
evidence, not a proof that Rust/LLVM accurately implements the source model.
