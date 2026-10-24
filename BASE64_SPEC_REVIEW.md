# Base64 specification self-review

Reviewed against [RFC 4648](https://www.rfc-editor.org/rfc/rfc4648.html),
sections 3 and 4, on 2026-10-24. This is an implementation-author self-review.
Independent specification review and reproduction are pending.

| Requirement or policy | Specification and proof connection |
|---|---|
| Section 3.1: no unsolicited line breaks | `quantum` and `encoded` emit only alphabet bytes and final padding. |
| Sections 3.2 and 4: final padding | `quantum` handles one-, two-, and three-byte groups; `first` confines padding to the final group. |
| Section 3.3: reject non-alphabet data | `value`, `unquantum`, and `decoded` reject invalid bytes, including whitespace. |
| Section 3.5: zero unused bits | `quantum` emits zero pad bits. `unquantum` chooses the permitted strict rejection policy for nonzero pad bits. |
| Section 4: alphabet and bit order | `symbol` and `value` follow Table 1; `quantum` splits each three-byte group into four six-bit digits. |
| Canonical identities | `round_trip` and `canonical_round_trip` connect arbitrary sequences to the group identities. |

The fixed 48-bit batching proof must establish the same ordering across two
groups; it does not replace any of these definitions. Encoding concatenation
requires a boundary divisible by three. Decoder batching leaves the final
group to the original padding path.

Buffer preservation, error precedence, termination, and overflow handling are
additional project contracts, not requirements attributed to RFC 4648. Their
meaning is recorded in [CONTRACTS.md](CONTRACTS.md). Tests and source proofs
do not establish universal equivalence to a particular upstream binary.

An independent reviewer should check this mapping, the actual mathematical
definitions, and the public contracts before judging the advertised scope.
The verifier cannot establish that an informal standard was translated
accurately merely by proving the implementation satisfies that translation.
