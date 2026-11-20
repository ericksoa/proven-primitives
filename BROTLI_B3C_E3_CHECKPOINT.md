# B3c E3 reached byte-store receipts and write billing

Status: **E3's named write-only checkpoint is complete** on the exact source in
[`evidence/brotli-b3c-e3.json`](evidence/brotli-b3c-e3.json).
The human explicitly approved E3 on 2026-11-20 ("E3 approved, please continue")
in `BROTLI_B3C_EMISSION_WRITE_METERING_DECISION.md`. This closes the prior
24-write/eight-work discrepancy for the shared emission primitive's write
component. It does not complete B3c or the entire body resource ledger.

Exactly five existing producers now return `(T, Ghost<nat>)`, keeping their
ordinary result as component zero: the B3c byte/u32/u64 scalar writers,
`BrotliDecoder::emit_byte`, and `emit_uncompressed_byte`. These are actual
internal compiled return-type changes. Public Brotli/W1 APIs and arguments
remain. The 26 outside producer call sites extract the old ordinary result;
the six nested stores and uncompressed wrapper propagate reached receipts.
The complete qualified production graph contains the approved 33 caller sites.

Each raw writer starts a ghost counter at zero and increments it immediately
at each reached byte assignment. Its return receipt is the current counter on
every path: one/four/eight stores on success, zero on an address error. Shared
emission counts its caller-output and window assignments, then merges the six
actual child receipts (1 + 1 + 4 + 4 + 8 + 4). The wrapper forwards its child's
count through its own zero-initialized counter. Neither budget differences nor
expected formulas construct these receipts.

Checked contracts prove 24 reached stores on successful emission and zero on
its errors in the original admitted domain. The exact work debit equals that
returned successful count. Source-local checked assertions establish prefix
counts 1, 2, 3, 4, 8, 12, 20 and 24. The work decrement is checked before the
first output assignment, when the reached-store counter is still zero.
All original success byte/state images, output/window equality, output suffix,
error workspace/budget/output atomicity and non-work counter effects remain.

The private `B3C_EMISSION_WRITE_WORK` constant is 24. Shared emission checks and
charges that write amount before stores. The output-block classifier uses the
same minimum: with an output credit but only 23 work units, even an empty output
returns resource failure; with 24 work units and an empty output, it can report
`NeedOutput`. The uncompressed wrapper retains its original >=8 entry
requirement. Admitted calls with 8–23 units return `ResourceLimit` without writes
or counter changes. Zero quotas remain valid RequestLimits; budget construction
still validates only window bits 10..24. Initialization/reset remains 425 units,
with the same four-unit terminal escrow and no credit refund.

The b3c-e3-final03 gate passed **1398 whole-crate checks with zero errors**,
**118 runtime tests**, and **56 strict semantic defect rejections across
four complete suites** on one frozen source/test/build closure. The actual
unfiltered `--no-cheating` positive completed before all deliberate defects.
The suites contain the prior 28 B3c cases, six constructor cases, ten byte-effect
cases and 12 E3 cases. The E3 cases omit primitive/direct/child/wrapper receipts,
restore the eight-unit debit or minimum, or move the debit after the first
output write. Every mutation retains its actual function header and contract.
Resource, syntax, type, panic and tool failures do not count as rejections.

The two new runtime tests cover 24/23/8/0 work, both input-debit modes, the
actual uncompressed wrapper, physical position wrap, history growth/saturation,
previous bytes, total/meta updates, complete resource-error preservation and
empty-output priority. They also check zero-size receipt-marker and selected
paired-result size/alignment. Native tests cannot inspect erased `nat` values;
the receipt equalities are checked by Verus, not those runtime assertions.
This is not an ABI-stability or source-to-binary theorem.

The separate static source audit checks one adjacent increment per reached
primitive assignment, all child-receipt merges, no receipt assigned from a
charge/model/budget formula, and debit placement before all eight direct or
child-store sites. Three static guard corruptions are recorded separately;
they are not added to the semantic-verifier case count. The audit normalizes
only the approved result projections, tuple/error propagation, proof-only
receipt/binding statements and eight-to-24 terms, then checks the original
arguments, requirements, functional guarantees and statement/guard/error order.
All code outside the scoped changes is preserved, including the older M1,
B2, dictionary/context data and prefix proof models. No new mathematical
visibility, dependency, state field, workspace or producer graph was selected.

The existing fault harness required mechanical selector rebindings for the
approved tuple return and explicit error propagation, plus indentation changes;
assertions, case meanings and strict classifiers remain. The ten-case retained
emission suite uses the same 300 solver allowance on positive and negative
copies after earlier 60-limit results mixed semantic/resource diagnostics.
Production allowances are unchanged. The legacy core and retained emission
queries use `--no-auto-recommends-check` identically on their selected positive
and negative copies. Pinned-verifier help defines this as omitting automatic
advisory recommendation checks after a primary verification failure; primary
proof, lifetime, erasure and `--no-cheating` checks remain. The production whole
positive retains the original full command and does not use that switch.
Matched source-identical diagnostics pass the unchanged original and report a
checked semantic failure without resources for the unchanged second-previous
fault. Earlier logs show the primary three-second contract failure followed by
an advisory rerun/resource exhaustion; those mixed results are not counted.
Earlier failed/interrupted gate and preflight outputs retain their actual
statuses and are excluded from final counts; exact histories and source
archives are bound in the receipt.

The preceding B2/budget checkpoint's six controls remain a separate historical
result. This E3 gate does not relabel that result as a rerun. All its existing
contracts remain in the fresh whole-crate positive. F2 is preserved: quickfox
matches pinned output; monkey remains a zero-output sticky ContextMapRepeat
rejection with its unresolved native disagreement; strict tree coverage and
the compression dictionary fixture remain.

E3 prices the write component only. Input/window/dictionary source-read
prepayment, further caller scalar writes/transitions, metadata/body accounting,
complete B2 restore/store/call/snapshot and whole-stream composition remain
open. No unpaid read is declared free by this checkpoint. It does not complete
B3d/B4, supported-format refinement, independent human specification review or
the supported-decoder/release gate. Trusted components remain the specifications,
unit interpretation and counter placement, pinned Verus/Z3/vstd and Rust/LLVM,
Apple build tools, and the operating environment. Another architectural,
boundary, representation or unit-policy choice still requires exact human
approval; E3 supplies no such additional authority.
