# M1 context-mode proof boundary: Candidate K2

The human explicitly approved Candidate K2 in this chat on 2026-11-09:
“Approve K2 please”. This answers the pending K2 proposal described in the
continuation handoff. Candidate K1 remains held for review.

K2 strengthens only the existing crate-private `write_next_context_mode`
proof contract in `src/brotli_prefix.rs`. Under its existing requirements
(`initialized <= 256`, `value < 4`), it additionally guarantees success when:

- `window_bytes <= 16_777_216`;
- the workspace contains the window plus the existing fixed scratch region;
- `initialized < 256`.

Its signature, requirements, executable body, errors, storage layout and work
charges are unchanged. No mathematical definitions are exposed across the
canonical-code boundary held under K1. Input-local proofs may use this success
guarantee to establish normal context-mode planning and W1 execution agreement.
The approved 425-unit construction/reset charge remains fixed.

Verification must check the strengthened writer contract, its dependent
normal context-mode relations, the unchanged whole crate and deliberate-defect
controls. Completion of K2 does not complete M1 or establish a supported Brotli
decoder. The source-operation ledger, remaining phase/failure relations,
B3c/B3d/B4 closure and independent human review remain required.
