# Checked Brotli B2 prefix and block-switch core

B2 extends the private B1 foundation with a bounded canonical prefix-code core,
the RFC block-length range table and literal/command/distance block-switch state.
It remains a component, not a complete or supported Brotli decoder.

The B2/C1 snapshot passed **177 verification checks with zero errors** under
`--no-cheating`. The later B3a record supersedes the whole-crate count while
preserving these checked B2 properties:

- Code-length storage is bounded to 258 symbols and 15 bits. Successful table
  construction has the exact canonical code for every used symbol; exact
  decoding returns only a symbol whose stored width and code match.
- The 15-bit code-space validator tracks actual Kraft-space consumption and
  rejects invalid widths, degenerate, oversubscribed and incomplete alphabets.
- Every successful RFC block-length result equals the pinned 26-entry
  offset/extra-bit table and is positive; suffixes and symbols are checked.
- Literal, command and distance paths share the same checked state transition.
  Block type history, current type and remaining length stay in range through
  complete switches, consumption, suspension and explicit reset.
- A switch when the declared number of block types is one is immediately and
  permanently `InvalidBlockSwitch`, consumes zero decoded fields and remains
  sticky across retries. The check occurs before canonical prefix/length work.
- A viable missing field is `NeedInput`; wrong category continuation, invalid
  type symbols and invalid/zero lengths are permanent failures. A decoded type
  retained across suspension is neither reread nor replaced.

The approved R1 native replay is in
[`evidence/brotli-r1.json`](evidence/brotli-r1.json). Across fixed input chunks
1 through 22, the fix and v1.2.1 report permanent block-switch error `-17` for
Node's 22-byte witness. The pre-fix parent returns later format error `-9`.
All guards remain intact and no ASan diagnostic occurred, so this is a status
semantics replay, not a claimed reproduction of the historical overwrite.

Depending on chunking, the malformed native stream emits 16,777,216 or
16,777,218 provisional `A` bytes before failure. This is direct evidence for
the approved quarantining-caller policy: provisional output is not a valid
complete message.

B2 does not parse meta-block headers or code-length encodings from a full byte
stream, emit literals/copies, implement contexts/dictionaries, manage a window,
or decode the Node fixture in Rust. It therefore does not establish complete
stream correctness, arbitrary chunking for a complete decoder, native
equivalence, resource-policy enforcement or supported Brotli under a profile.
B3/B4 remain incomplete; the architecture is approved and independent review
is still pending.

After the unchanged 177-check positive control, the prover rejects changing
the permanent invalid switch into `NeedInput` and corrupting the canonical-code
recurrence, as part of the 25-control record. Tool or type failures do not count
as rejection evidence.
