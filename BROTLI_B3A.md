# Checked Brotli B3a workspace and meta-block-header slice

This report records the first checked portion of the approved B3a milestone. It
is a private implementation slice, not a complete Brotli decoder and not a
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

## Checked evidence and deliberate defects

The current whole crate passes **244 verification checks with zero errors**
under `--no-cheating`. The evidence record binds the exact source, tool versions,
options, report, runtime tests, and checker output.

Nine B3a defects are rejected after unchanged positive controls:

1. shifting every workspace tree-record address by one byte;
2. reading the first uninitialized canonical record;
3. reducing the fixed scratch total by one byte;
4. accepting the RFC meta-block reserved bit;
5. accepting a nonminimal normal length;
6. accepting a nonminimal metadata length; and
7. reporting final truncation as retryable input exhaustion;
8. swapping the low and high bytes of a stored canonical code; and
9. reconstructing a canonical code from the record length byte.

A type error or checker failure is not counted as a defect rejection.

## Remaining B3a and complete-decoder work

Simple and complex prefix-code descriptions are not yet connected to the bit
queue and workspace records. Tree groups, context maps, literal/command/distance
execution, LZ77, the static dictionary, provisional output, resource budgets,
and arbitrary complete-stream sequences remain unimplemented or unproved.
B3a therefore remains in progress, and no complete or supported Brotli claim is
made.

See [the approved B3 architecture](BROTLI_B3_PROPOSAL.md),
[the security assessment](SECURITY_CONTRACTS.md), and
[the machine-readable B3a evidence](evidence/brotli-b3a.json).
