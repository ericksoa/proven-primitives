# Security case studies

These cases connect historical vulnerabilities to properties checked for this
project's actual implementation. Regression tests establish particular
behaviors; universal guarantees come from the Verus contracts and proofs.
Neither case asserts security of a complete application or universal equivalence
to upstream source. The trusted base is described in [PROOFS.md](PROOFS.md).

[SECURITY_CONTRACTS.md](SECURITY_CONTRACTS.md) gives the attacker domain and
proved/partial/proposed/unproved status across confidentiality, state, resources
and composition. In every case, callers must expose only the returned current
success prefix; preserved storage is not sanitized output.

Current-upstream comparisons and the actual historical LZ4 replay are reported
in [COMPARISON.md](COMPARISON.md). Exact approved references and features are
recorded in [REFERENCE_PROPOSAL.md](REFERENCE_PROPOSAL.md).

## CVE-2026-32829: disclosure of previous LZ4 destination contents

### Historical failure

Invalid match offsets in lz4_flex's block decoder could expose uninitialized
memory or previous decompression contents in a reused destination. The latter
case also affected safe decoding. Frame APIs were unaffected. Upstream patched
the issue in 0.11.6 and 0.12.1.

- [Upstream advisory](https://github.com/PSeitz/lz4_flex/security/advisories/GHSA-vvp9-7p8x-rfvv)
- [RustSec CVE mapping](https://rustsec.org/advisories/RUSTSEC-2026-0041.html)
- [Pinned upstream regression source](https://github.com/PSeitz/lz4_flex/blob/1bffdcbbf906a234b913937cb2f57c0245915038/src/block/decompress_safe.rs)

### Generalized checked property

The checked `decompress_block_into` postcondition says that its successful
returned prefix equals `decoded(input)`. This specification depends on the
compressed input and previously produced decoded bytes. Each executable match
read is restricted to bytes produced by the current call. Zero offsets and
references before the produced prefix are invalid.

The private proof `lz4::decoded_prefix_is_independent_of_previous_output`
establishes the security consequence: any two buffers satisfying that success
contract for the same input have equal returned prefixes, regardless of their
previous contents. Its premises are the separately checked implementation's
success postconditions. It adds no trusted assumption or public precondition.

Malformed input returns `InvalidInput` and preserves the complete destination,
even when the destination is too small. A successful call preserves the suffix
beyond its returned prefix. Callers must only expose the returned prefix; the
theorem does not sanitize the preserved suffix or establish constant time.

### Regression and negative proof control

Our test exercises the upstream zero-offset fixture:

```text
0e 00 00 70 00 00 00 00 00 00 00
```

It checks rejection with destination lengths 0, 1, 17, 25, and 256, each
initialized to four different byte values, and verifies full buffer preservation.
Another test checks successful overlapping matches with different initial
contents, equal returned prefixes, and preserved tails.

The negative control changes the actual match read to `output[j]` instead of
`output[j - step.offset]`. This can read a stale destination byte while staying
inside the allocation. Verification must reject it with specifications intact.
The optimized offset-one path has a separate mutation that captures
`output[j]` instead of the last produced byte, and must also be rejected.

The historical 0.12.0 safe decoder was also executed at the pinned Git revision.
It returned 25 bytes for this input, including 18 bytes copied from the old
destination contents. Changing the initialized destination changed its returned
bytes. The current 0.14.0 reference rejected the zero offset; our implementation
rejected it and preserved the complete destination. This is a local replay of
the reused-buffer disclosure, without uninitialized-memory or network execution.

## CVE-2017-1000430: Base64 sizing overflow

### Historical failure

The historical Base64 implementation calculated encoded capacity with unchecked
integer arithmetic before writing through unsafe code. The advisory describes
an undersized-buffer and memory-corruption risk. The fix uses checked sizing
operations; versions at least 0.5.2 were patched.

- [RustSec advisory](https://rustsec.org/advisories/RUSTSEC-2017-0004.html)
- [Original fixing change](https://github.com/marshallpierce/rust-base64/commit/24ead980daf11ba563e4fb2516187a56a71ad319)
- [Original sizing expression](https://github.com/marshallpierce/rust-base64/blob/21a9389cf340f1e36e48856859d5713b97744383/src/lib.rs)

### Generalized checked property

The private proof `base64::encoded_size_is_four_per_group` establishes the
mathematical encoded length `4 * ((input_length + 2) / 3)`, without wrapping.

Our executable sizing helper uses quotient/remainder arithmetic to count
groups without calculating `input_length + 2` in machine arithmetic. It checks
`groups <= capacity / 4` before multiplying by four. Its checked contract
returns the exact mathematical encoded length when it fits, and an
insufficient-capacity error otherwise. The writer proves every actual byte
refines that same specification
within the caller's destination. These obligations exclude successful writes
into an undersized destination caused by wrapping length arithmetic, for every
input and capacity admitted by the modeled Rust slice types.

### Arithmetic reproduction and negative proof control

The test evaluates the original no-line-wrap sizing expression with explicit
32-bit and 64-bit wrapping integers. It constructs lengths with mathematical
encoded sizes of `2^32` and `2^64` respectively; the historical expression
evaluates to zero.

This is an arithmetic counterexample, not execution of the old encoder, a giant
allocation, or evidence those lengths were reachable as valid historical Rust
slices. No historical exploit or allocation behavior is claimed to have been
reproduced. Assurance for our implementation comes from its checked contracts.

For real byte inputs the regression checks exact capacities and destinations
one byte too small, including unchanged output on failure. The negative proof
control incorrectly accepts one more four-byte group than fits the destination.
Verification must reject it with the original contracts intact.

The later Base64 table iterations retain these same specifications. Their
separate corruption controls change the executable encoding alphabet and make
the decoding table accept NUL; verification rejects both without modifying the
mathematical functions. See [TABLE_ITERATIONS.md](TABLE_ITERATIONS.md).

## CVE-2026-111497: Brotli streaming error-state confusion

The [Brotli roadmap entry](ROADMAP.md) records the upstream disclosure and fix.
Its generalized obligations are pending-buffer bounds, a correct distinction
between permanent format failure and genuine input exhaustion, and preservation
of those properties over every permitted streaming call sequence. The
applicable obligation fragments are now **proved for each admitted call and
state of the private B1, B2, B3a and B3b components**. B3b
proves bounded serialized compressed-header state, exact nonfinal suspension
versus final truncation, sticky terminal errors, and an exact initial B2 `Ready`
snapshot across context maps and tree groups. B2 proves the corrected rule
shared by literal, command and distance switches: one declared type makes a
switch a permanent zero-field error before prefix parsing. The E2 adapter proves
exact mapping of B2 ready, suspended and failed outcomes. Body execution does
not yet call that adapter when a category is exhausted, so complete-stream
status propagation remains unproved B3c/B4 work. The Rust code does not yet
decode a complete meta-block or emit Brotli output.

The approved native R1 replay checks Node's 22-byte witness at fixed input
chunks 1 through 22. The fix and v1.2.1 return permanent error `-17`; the
pre-fix parent returns later format error `-9`. All harness guards remain intact
and no ASan diagnostic occurred, so no memory overwrite reproduction is claimed.
See [BROTLI_B2.md](BROTLI_B2.md) and
[the raw structured record](evidence/brotli-r1.json). The
[B3b report](BROTLI_B3B.md) and [control record](evidence/brotli-b3b-controls.json)
retain the component proof boundary, runtime cases and 58 deliberate semantic
defects. These component results do not substitute for the future integrated
multi-call regression in the body decoder.

## Reproduce

Use the pinned tools and platform settings in [README.md](README.md):

```sh
cargo +1.99.1 verus build --fwd-verus-args-to roots --locked --release -- \
  --no-cheating --num-threads 1 --triggers-mode silent --rlimit 60
cargo +1.99.1 test --locked --release
VERUS_ROOT=/path/to/pinned/verus cargo +1.99.1 test --locked --release \
  --test proof_rejection -- --ignored --nocapture
```

The rejection suite verifies an unchanged positive control before requiring
rejection of the recorded implementation mutations. The proof record identifies
the exact checked source hashes. Tests do not substitute for the proof command
or establish equivalence to upstream implementations.
