# B3c byte-emission effects and error atomicity

Status: the named shared-emission and uncompressed-caller effect checkpoint is
complete on the exact source bound in
[`evidence/brotli-b3c-atomic-emission.json`](evidence/brotli-b3c-atomic-emission.json).
It implements the already-approved C1 atomic-output/state-effect proof scope in
`BROTLI_B3C_PROPOSAL.md`, using the existing A1 scalar accessors. It preserves
executable/public interfaces, representations, dependencies, quota policy and
trusted components. No public or cross-module proof interface is added.

`BrotliDecoder::emit_byte` and its actual `emit_uncompressed_byte` caller now
bind the complete successful workspace image to the incoming workspace and the
emitted byte. One output byte equals the byte written at the incoming physical
window position. The exact serialized image also establishes:

- position advances once, wrapping at the physical window size;
- history increments while below the logical limit and otherwise retains its
  old value;
- second-previous byte becomes the previous byte, and previous byte becomes the
  emitted byte;
- the checked 64-bit total increments once without overflow;
- remaining meta-block length decrements once;
- every other workspace byte is preserved.

The image is expressed with the approved little-endian state layout, using the
existing scalar interpretations for incoming values. It specifies all 22 scalar
bytes and the single physical-window cell written by the source. The result
preserves limits, call credit and initialization credit; success retains the
existing exact eight-work/one-output debit and optional one-input debit. The
uncompressed caller fixes that input debit to one. The primitive and this
uncompressed caller are checked, with their original requirements retained.

For every error returned in the original admitted domain, the entire workspace,
budget and caller output are unchanged. The original output length, selected
output-byte identity and output-frame guarantees remain. Successful emission
also establishes valid incoming position/stream-bit/meta-length conditions and
a nonoverflowing total. These are postconditions; no entry requirement was
strengthened or admitted state excluded.

The old entry predicate admits malformed saved scalar values. Therefore the
history-limit consequence is conditional on incoming history already being
within that limit; the exact image still describes other admitted incoming
history values. This is a local transition/effect proof. It does not establish
arbitrary call-sequence history induction, the origin/correctness of the supplied
byte, complete error-cause classification, or absence of spurious failures.
Those obligations must not be inferred from this checkpoint.

The `b3c-atomic-emission-final04` gate passed **1397 whole-crate checks with
zero errors**, **116 runtime tests**, and **44 strict semantic defect
rejections across three complete suites** on the same frozen source. The actual
entire-crate `--no-cheating` positive precedes all deliberate defects. The three
suites are the prior 28 B3c controls, six constructor controls and ten new
emission controls. The new controls corrupt actual executable writes/counters:
window/output equality, position, history, total, previous-byte state,
meta-block length, an unrelated workspace cell, resource-error budget or window
atomicity, and the uncompressed caller's error frame. Every new mutation is
restricted to the named function body with its contract preserved. Syntax,
resource, panic and tool failures do not count as semantic rejections.

The separate source-preservation audit reconstructs the entire parent
`brotli.rs` by replacing only the two strengthened contract sections, removing
one existing-tool solver-isolation annotation, and restoring the module comment.
Both complete helper bodies, signatures, requirements and all old guarantees
are byte-identical. Every other tracked core/test/build input matches the
parent. Reversing only the documented legacy selector/checker repairs restores
the exact old test prefix, and the new ten-case suite is appended. This is a static source audit,
not a source-to-binary correctness theorem. No RequestBudget policy, runtime
algorithm, ordering, workspace layout, 425-unit initialization charge, F2
fixture policy or prior mathematical specification changed.

The evidence package binds actual logs, source/tool identities, the frozen
source archive, full suite identities, classifiers, preserved earlier partial
proof diagnostics and reproduction scripts. Getter-form diagnostic attempts
that exhausted solver effort remain failures and are not positive controls.
The final checked contracts describe the complete concrete image, retaining all
preexisting guarantees. The earlier 318-case M1 result remains a historical
checkpoint; it is not counted as a rerun in this 44-case gate.

The legacy 28-case suite had a stale command-decrement selector after M1's
receipt refactor. Its two selector strings now target the same faulty ordinary
write in the current `.0` implementation. All original assertions remain.
The larger emission root uses the whole gate's allowance of 300 in its selected
positive and negative checks. The terminal-retry control uses allowance 300 in
both temporary source copies, restoring the original temporary source after
each query; production `step` retains its original allowance of 60. No checker
assertion or strict rejection classifier was relaxed. Matched diagnostics show
clean semantic rejection; earlier mixed results are excluded.

Attempts `final01` and `final02` passed their whole/runtime positives but failed
new broad fault queries with mixed postcondition/resource results. Other running
regression suites were stopped after those blockers. The final fault definitions
skip the first history/total increment at zero or flip a window byte on the
resource-error path; original function requirements and contracts remain exact.
Attempt `final03` passed the whole/runtime positive and both the six-constructor
and ten-emission suites, then stopped at the stale legacy selector after eight
reported cases. Its interrupted/failed statuses and all original source/logs
remain historical, not final gate passes.

A separate source audit found a known C1 write-billing mismatch: the successful
emission path performs 24 source-level byte writes while its existing work debit
is eight. The 16-unit gap is the extra bytes in three four-byte writes and one
eight-byte write. `evidence/b3c-emission-write-audit/source-audit.json` retains
the static source inventory; it is not a checked per-invocation receipt or a
hardware/cycle measurement. The eight-unit counter-effect contract is therefore
not completion evidence for C1's per-byte work policy. Candidate E3 in
`BROTLI_B3C_EMISSION_WRITE_METERING_DECISION.md` requests the necessary direct
human approval for five internal receipt return types and a 24-unit write-only
charge/minimum. E3 has not been implemented in this checkpoint; source reads,
other caller actions and complete body billing remain open.

The actual B2 caller was also reviewed using a private fault copy. Replacing its
permanent single-type rejection with `NeedInput` is accepted by its existing
weak contract, as is the unchanged original. The accepted-fault result is bound
in `evidence/b3c-b2-caller-review/review.json` and is **not** counted among the 44
rejections. The production branch still invokes the checked rejection helper.
This confirms an actual-caller proof gap and leaves the full C1 control gate
incomplete, even when this named byte-effect gate passes.

The trusted base remains the mathematical specifications and interpretations,
pinned Verus/Z3/vstd and Rust/LLVM stack, Apple build tools and operating
environment. Technical checking does not replace independent human review of
the specification.

The broader B3c proof status is:

| Area | Checked scope and remaining obligation |
| --- | --- |
| Constructor | I2 binds successful validity and exact initialization/workspace/error effects. |
| M1 compressed header | The named source-receipt and prepaid-action refinement checkpoint is complete in its frozen scope. |
| Atomic emission | This checkpoint binds the shared primitive and uncompressed caller's exact serialized effects and complete error frames. Byte origin and whole-body composition remain open. |
| Public `step` | Existing consumed/produced bounds, output suffix preservation and already-stored terminal replay remain checked. Full fresh-result/status and resource composition remain open. |
| Metadata and EOF helpers | Existing local debit/frame and EOF-condition contracts remain checked; complete stream composition remains open. |
| Commands, literals, distance and dictionary | Existing accessor/arithmetic/safety contracts remain checked. Full executable phase refinement, LZ77 overlap induction and dictionary caller composition remain open. |
| Actual B2 body caller | The B2 transition root and permanent single-type rejection helper are checked. Saved-state loader/store correspondence and actual body-adapter binding remain open; a retry-bypass fault is accepted by the current caller contract. |
| B3d/B4 and release | Arbitrary call-sequence induction, source-observation claims, independent human specification review and supported-decoder/release gates remain separate. |

F2 is unchanged: `quickfox_repeated` decodes to pinned bytes; `monkey` retains
zero-output sticky `ContextMapRepeat` rejection and the unresolved native
comparison disagreement. This checkpoint does not complete B3c or establish a
supported Brotli decoder, side-channel claim or source-to-binary proof.
