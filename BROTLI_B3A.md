# Checked Brotli B3a workspace, meta-block, and code-description front end

This report records the checked components of the approved B3a milestone. They
remain a private implementation slice, not a complete Brotli decoder and not a
supported Brotli API.

## Checked workspace properties

The implementation fixes the caller workspace to a power-of-two window followed
by exactly **1,176,560 bytes** of byte-addressed scratch. Checked constants and
offset theorems cover every approved region: literal, command, and distance
trees; literal and distance context maps; context modes; block-type and
block-length trees; the bounded builder and temporary context tree; move-to-front
state; and the final state area.

`required_workspace_bytes` accepts only window bits 10 through 24 and returns
exactly `(1 << bits) + 1,176,560` without overflow. Every tree location proves
its tree and symbol indices are in the selected region and that its three-byte
record remains within the fixed scratch total.

Canonical records are stored as one length byte and a little-endian `u16` code.
Tree metadata distinguishes an unused tree, a single-symbol zero-bit tree, and
a canonical tree with a contiguous initialized prefix. Reads reject every
canonical record outside that initialized prefix. A single-symbol read returns
the logical zero-bit record without inspecting old workspace bytes. This is a
checked source-level prior-storage confidentiality property for these accessors.
Every successful record write proves the exact three resulting bytes and that
all other workspace bytes are preserved; an initialized read proves the exact
inverse little-endian reconstruction.

The 3,056-byte builder is partitioned exactly into 704 code-length bytes,
sixteen `u16` counts, sixteen `u32` next codes, 720 `u16` symbol-chain entries,
and the 816-byte temporary context tree. Each accessor proves its exact byte
range, initialized-read condition and write frame. The canonical installer
validates the complete 32,768-unit code space, uses only these fixed regions,
and proves that every destination record contains the original length and its
exact canonical code. Unused symbols receive `(length=0, code=0)` records, while
tree metadata continues to distinguish those records from a single-symbol
zero-bit tree. All bytes outside the builder bookkeeping and selected tree are
preserved.

## Checked meta-block-header properties

The private meta-block state machine starts from the retained B1 bit queue. It
parses RFC normal, last-empty, uncompressed, and metadata header forms one field
at a time while preserving the eight-byte pending invariant across arbitrary
byte splits.

The root contract connects each source transition to the exact bits accepted
from the old queue plus the current input prefix. It proves:

- successful normal lengths are 1 through 16,777,216;
- metadata lengths are 0 through 16,777,216;
- the RFC reserved bit is a permanent error;
- nonminimal final normal-length nibbles and metadata-length bytes are permanent
  errors;
- nonfinal exhaustion is retryable only when the required field is incomplete;
- final exhaustion is permanent truncation; and
- complete and failed states are sticky and consume no later input.

Runtime cases cover complete forms, one-byte chunking, retained bits from the
window header, the three permanent format failures, truncation, and retry after
failure.

## Checked prefix-code-description front end

The next private state machine continues from a completed compressed meta-block
header using the same retained-bit queue. Its source transition contract binds
every field result to the exact accepted bits.

For simple descriptions, it proves the selector, one-to-four symbol count,
alphabet-dependent bit width, symbol bounds, pairwise distinctness and both
four-symbol tree shapes. Out-of-alphabet and duplicate symbols are permanent
errors; final exhaustion is permanent truncation.

For complex descriptions, it proves the RFC 18-entry code-length permutation,
all six values of the fixed two-to-four-bit prefix code, skip values 0/2/3, and
exact 32-unit code-space accounting. A complete auxiliary alphabet has either
one nonzero code or exactly exhausted code space. Oversubscribed and incomplete
auxiliary alphabets are permanent errors. Runtime cases exercise whole-buffer
and one-byte chunking, every simple shape, every static prefix length, skips,
and malformed code space.

The final complex stream begins with previous length eight. Direct symbols
`0..15` reset repeat chaining, and nonzero direct symbols update the previous
length. Symbol 16 repeats that previous length with two suffix bits; symbol 17
repeats zero with three. The checked transition uses the RFC reset rule and
`(repeat - 2) << extra_bits` recurrence, proves the exact newly emitted span,
rejects expansion past the selected alphabet, and charges every nonzero span
against the 32,768-unit code space. Completion requires exact exhaustion;
oversubscription, incomplete space, final truncation and later retries after a
permanent failure retain their specified behavior. Runtime cases cover complete
input and one-byte chunks, both repeat kinds, chained repeats, initial previous
length eight, overflow, truncation and sticky failure. Auxiliary codes are
reversed to their active width before comparison with the raw least-significant-
bit-first stream; a non-palindromic two-bit case checks that source-linked rule.

## Checked evidence and deliberate defects

The current whole crate passes **350 verification checks with zero errors**
under `--no-cheating`. The evidence record binds the exact source, tool versions,
options, report, runtime tests, and checker output.

Twenty-eight B3a defects are rejected after unchanged positive controls:

1. shifting every workspace tree-record address by one byte;
2. reading the first uninitialized canonical record;
3. reducing the fixed scratch total by one byte;
4. accepting the RFC meta-block reserved bit;
5. accepting a nonminimal normal length;
6. accepting a nonminimal metadata length; and
7. reporting final truncation as retryable input exhaustion;
8. swapping the low and high bytes of a stored canonical code; and
9. reconstructing a canonical code from the record length byte;
10. misclassifying the simple/complex selector;
11. accepting a symbol equal to the alphabet limit;
12. accepting a duplicate simple symbol;
13. mapping a static-prefix value to the wrong code length;
14. misclassifying code-space overflow; and
15. changing the RFC code-length permutation;
16. shifting the builder code-length write region;
17. reading an uninitialized builder code-length entry;
18. storing the wrong byte in a builder count;
19. storing the wrong byte in a builder next-code value;
20. rejecting a required zero-length canonical record;
21. installing the wrong canonical code in a destination record;
22. initializing the repeated previous length to a value other than eight;
23. failing to reset a repeat after its repeated length changes;
24. subtracting one instead of two in chained-repeat expansion;
25. adding four instead of three to a repeat suffix;
26. rejecting a repeat that exactly fills the selected alphabet;
27. undercharging repeated nonzero lengths against final code space; and
28. comparing raw auxiliary stream bits with an unreversed canonical code.

A type error or checker failure is not counted as a defect rejection.

## Remaining complete-decoder work

The final-length parser exposes exact internal spans and the canonical installer
consumes initialized builder lengths. Tree-group orchestration will connect that
handoff in B3b. Context maps, literal/command/distance execution, LZ77, the
static dictionary, provisional output, resource budgets, and arbitrary
complete-stream sequences remain unimplemented or unproved. No complete or
supported Brotli claim is made.

See [the approved B3 architecture](BROTLI_B3_PROPOSAL.md),
[the security assessment](SECURITY_CONTRACTS.md), and
[the machine-readable B3a evidence](evidence/brotli-b3a.json).
