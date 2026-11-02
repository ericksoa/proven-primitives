# Brotli B3c C1 internal-boundary addendum

Status: **Candidate A1 approved exactly as written by the human on 2026-10-27.**
This addendum records the adopted internal boundary for Candidate C1.

## Approved boundary and discovered difference

Candidate C1 approves the public API in `src/brotli.rs` and the narrow
crate-private `src/brotli_input.rs` adapter surface enumerated in
`BROTLI_B3C_PROPOSAL.md`. The current unpublished implementation also makes the
following B3c implementation details callable across the crate boundary:

- serialized B3c layout constants, scalar specifications, and typed scalar
  read/write accessors;
- `BodyBitsStatus`, `BodyBitsStep`, and
  `advance_serialized_body_bits`;
- serialized meta-header reset and byte-alignment helpers;
- distance-LUT initialization and lookup helpers;
- dictionary staging, initialized-byte reads, and dictionary-state helpers;
- body block-count, tree-count, remaining-count, decrement, and active-type
  accessors.

They add no persistent state, dependency, tool, allocation, unsafe code,
executable recursion, I/O, trusted component, or public API. They do broaden
the crate-private component boundary beyond the exact C1 list, so they require
direct approval or refactoring before publication.

## Candidate A1: retain the current checked internal helpers

Candidate A1 approves the additional crate-private items listed above only for
the existing B3c implementation. Their effects remain constrained to the exact
C1 workspace layout, budget object, status families, algorithms, dependencies,
and proof trust boundary. They remain inaccessible to downstream crates.

The consequence is a wider internal seam between `brotli.rs` and
`brotli_input.rs`. It avoids duplicating serialized queue, scalar, LUT,
dictionary-staging, and B3b block-state logic in the public-core module. Every
helper still requires its own checked contract and deliberate-defect coverage;
approval does not accept a weak contract or a proof gap.

## Candidate A2: restore the original narrow surface

Candidate A2 keeps the original C1 list exact. The implementation must move or
duplicate all top-level scalar, raw-bit, LUT, dictionary-staging, and body-state
logic behind `src/brotli.rs` private functions, leaving only the named C1
adapters callable from `brotli_input.rs`.

The consequence is a substantially larger `brotli.rs` implementation and proof
surface, including a second private implementation of serialized bit-queue and
B3b body-state access. The public API, persistent state, dependencies, and
trust boundary remain unchanged.

## Approval requested

The human approved **Candidate A1 as written** on 2026-10-27. Candidate A2
remains unselected.
