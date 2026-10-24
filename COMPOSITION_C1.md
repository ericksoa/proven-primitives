# Checked C1 composition demonstration

C1 is a crate-private verified caller that strict-Base64 decodes into caller
scratch and then strict-percent decodes only the current returned scratch
prefix. It is a proof of this exact connecting program, not arbitrary callers.

The C1/B2 snapshot passed **177 verification checks with zero errors** under
`--no-cheating`. The later B3a record supersedes the whole-crate count while
preserving these checked C1 contracts for every admitted input, capacity and
initialized buffer:

- Exact stage order and distinct Base64-invalid, scratch-small,
  percent-invalid and output-small results.
- Both buffers remain unchanged when Base64 fails. After Base64 succeeds,
  scratch contains exactly its current produced prefix even if the downstream
  stage fails; this earlier effect is not described as rollback.
- Percent decoding receives `scratch[..middle_n]`, where `middle_n` is the
  current Base64 result. It cannot receive a stale length or unused suffix.
- Every error clears `published_len`; success records exactly the current final
  length. The authorized external observation is only that output prefix.
- Successful final bytes depend only on the current input, not old scratch or
  output storage. Scratch remains an explicitly internal permitted observation.
- `S <= 3(I/4)`, `O <= S`, and conservative successful source work is
  `8I + 12S + 4O + 56 <= 21I + 56`. Proof-only ledgers are connected to the
  actual Base64 and percent validation/writer loops; these units are not cycles.

After an unchanged 177-check positive control, the mutation suite rejected all
seven C1 corruptions: current-prefix handoff, Base64 and downstream stale-length
handling, publication length, error identity, one component's work ledger and
the downstream-error scratch effect. These are part of the complete 25-control
record in [`evidence/b2-c1-controls.json`](evidence/b2-c1-controls.json).

C1 does not prove protocol authorization, transport behavior, arbitrary retry
loops, constant-time handling of current secret input, compiler correctness or
machine side channels. Rust ownership/reference validity and the documented
source-to-binary boundary remain trusted.
