# Brotli B3c C1 comparison-fixture addendum

Status: **Candidate F1 approved exactly as written by the human on 2026-10-27.**
This addendum changes only the approved C1 comparison matrix. It does not
change the decoder API, serialized state, algorithms, dependencies, tools,
resource policy, or proof trust boundary.

## Discovery

The C1 proposal classified the pinned `quickfox_repeated` and `monkey` pairs as
successful body and dictionary comparisons. Both streams are accepted by the
pinned native Brotli v1.2.1 reference, but they are rejected by the already
checked B3b component before body execution. Their context maps omit an
advertised tree. B3b deliberately enforces the RFC coverage rule that every
advertised tree must occur, and records native acceptance as an intentional
strict-coverage difference.

Changing B3b to accept those streams would contradict its approved and checked
contract. Treating them as successful B3c dictionary cases would also be
false: the B3c dictionary path is never reached.

## Candidate F1

Candidate F1 makes these exact comparison changes:

1. Retain the pinned `quickfox_repeated` and `monkey` bytes, hashes, native
   results and attribution.
2. Classify both as expected checked-decoder `InvalidFormat` results caused by
   B3b's documented strict tree-coverage rule. Require zero produced bytes and
   sticky zero-consumption failure on retry.
3. Add the following fixed successful dictionary-transform stream:

   | Field | Value |
   |---|---|
   | Compressed bytes | `1f0a00f825000298b0e501` |
   | Compressed length | 11 bytes |
   | Compressed SHA-256 | `a87bcbc0f45a2f793c075b26baec65ff9cd551e057c8cdef508231004ba4abf5` |
   | Expected bytes | ASCII `compression` (`636f6d7072657373696f6e`) |
   | Expected length | 11 bytes |
   | Expected SHA-256 | `d18f849bb8c5ffef9e1b9b8719e3bcbba35f100655be40f035aeace790dec16b` |

4. Run the new stream whole, one byte at a time, at every input split, and with
   one-byte, exact and sufficient output chunks. Require output-suffix
   preservation, exact final output, every truncated prefix, sticky errors,
   old-workspace/output variations and exact/one-short resource cases.
5. Retain the pinned native validation result: the v1.2.1 harness consumed all
   11 bytes, produced 11 bytes, finished successfully, preserved its guards and
   emitted the expected SHA-256 above with one-byte input and output chunks.

The source of the fixed compressed stream is recorded as a hand comparison
fixture validated against the pinned native reference. It is not represented
as an upstream corpus file.

## Consequence

F1 restores truthful comparison coverage without weakening B3b or treating a
general RFC coverage rule as a fixture exception. The successful fixed stream
exercises B3c dictionary selection, transformation, initialized staging and
bytewise emission. It does not establish complete Brotli equivalence or the
streaming security contract by itself.

The human approved **Candidate F1 as written** on 2026-10-27.
