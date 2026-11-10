# M1 loader table-read accounting: Candidate K5

Status: **approved as written by direct human reply on 2026-11-10**.
Implementation and verification are authorized within the exact scope below.

K4 was approved and corrects repeat history without changing work formulas.
The remaining M1 loader ledger needs a separate quota decision. The current
18-unit allowance counts auxiliary copies but omits validation scans. The
loader also unconditionally copies four saved simple-symbol `u16` entries
before auxiliary loading, after its alphabet guards. Whether to classify those
four indexed copies as table cells must be explicit; the earlier approval
named only the 18 auxiliary cells and left ordinary scalar bookkeeping alone.

## Exact proposed K5 policy and scope

Count each saved simple-symbol entry loaded by `read_simple_symbols` as **one
table-cell read**, four units for a complete load, rather than eight byte-read
units. Keep the existing one-unit charge for each of the 18 auxiliary length
copies. Ordinary individual scalar fields remain uncharged bookkeeping.

Additionally count every indexed table operand actually inspected by the
existing loader validation helpers:

- one per auxiliary length examined by `complex_code_valid_exec`;
- the selected length and each actually examined other entry in
  `singleton_code_valid_exec`, respecting its skipped index and first failure;
- one per active symbol examined by `active_symbols_in_range`; and
- two per comparison actually performed by `simple_symbols_distinct`.

Apply these reads to both actual read-only planning and **every** serialized
W1 execution reload. Preserve early guard order and exact inspected prefixes
on invalid alphabets, bad lengths, malformed progress, invalid singleton,
out-of-range symbols and duplicates. Do not charge an unperformed read, hide
reads in bookkeeping, or replace exact counts with a worst-case reservation.

Use the already selected M1 approach: a read-only forecast, charge its own
actual table reads as performed, prepay the complete next loader read count,
then call the unchanged W1 loader. Never move RequestBudget into W1.

Extend only the existing input-private pre-scan receipt:

```rust
plan_saved_aux_load(...) -> Result<(u64, bool), CoreFailure>
```

The existing `u64` remains the exact number of auxiliary cells inspected by
that pre-scan. The new transient boolean is true exactly when the alphabet
metadata is eligible and all 18 saved auxiliary lengths passed validation.
An early invalid alphabet returns `(0, false)`; a bad auxiliary cell returns
its inspected prefix and false. Resource errors keep their existing behavior.
This flag avoids a new uncharged/reread scan to distinguish a valid 18-cell
copy from an invalid last cell. It is not a persistent decoder field.

Within input-private planning helpers, forecast the existing validation guard
order and singleton/simple-symbol scans. Reuse the auxiliary pre-scan's checked
validity to forecast the mandatory 18-cell validation scan without redundantly
executing it in the forecast. Charge any table cells the forecast actually
reads. For later reloads, the already-valid local decoder permits exact
phase-based counts without rereading its valid table merely to compute a
constant count. Prove those counts agree with the W1 loader, including errors.

Update only the corresponding table-read terms in tree planning/execution
receipts, caller propagation, quota regressions and unchanged-root controls.
Keep the existing mutation, serialization and nested-reset/start formulas.
The private **proof-only** initial planning bound changes from 740 to 798:
704 builder-prefix reads plus at most 94 loader-forecast/replay reads. This is
not a runtime action cap or a RequestBudget policy limit.

## Concrete successful-load consequences

These totals count source-level table cells, including the proposed four
simple-symbol copies; they are not wall-clock or compiler instruction counts.

| Saved decoder phase | Existing loader table reads under K5 |
|---|---:|
| Selector or simple-size | 4 simple copies + 18 auxiliary copies = 22 |
| Valid complex prefix | 22 copies + 18 validation cells = 40 |
| Valid complex symbol without singleton | 40 |
| Valid complex symbol with singleton | 40 + 18 singleton cells = 58 |
| Valid four-symbol SimpleShape | 22 + 4 range operands + 12 distinctness operands = 38 |

For an initial valid complex singleton load, the forecast reads 18 auxiliary
cells and 18 singleton cells (36), and prepays the actual loader's 58 reads:
94 planning units before any builder-prefix copy. Invalid cases use their
actual shorter paths. Higher exact read charges can exhaust the same caller
work limit earlier; decoded semantics and error priority otherwise stay fixed.

The alternative of keeping the four simple-symbol copies as scalar
bookkeeping would yield different quotas and is not selected by this proposal.
No quota-policy or private-receipt change is implemented before human approval.

## Preserved boundary and required checks

Preserve W1 step/result interfaces, B3c budget ownership and reservation order,
workspace size/layout/byte meanings, dependencies/toolchain/trust boundary,
5,696 runtime action caps and the 425-unit construction/reset charge. Keep
K4's byte-71/174 correction and the separately approved F2 fixture expectations.
Do not narrow any original admitted input or replace a proof with tests.

Prove exact source-read/forecast agreement and framing for every loader branch.
Run the current runtime and native fixtures, a fresh unchanged whole-crate
positive, and unchanged-specification controls for omitted copies, validation
reads, early exits and per-reload charges. Preserve failed outputs; resource,
compiler and harness failures do not count as semantic defect rejections.
K5 does not itself complete tree replay, the rest of M1, B3c/B3d/B4 or the
independent human release review.

## Implemented and checked K5 checkpoint

The exact approved unit policy is implemented in read-only planning and every
planned W1 reload. The private pre-scan receipt now contains its unchanged
inspected auxiliary-prefix count and the precise all-auxiliary-valid flag,
including an invalid eighteenth cell. Validation forecasts preserve original
guard order, singleton skipped-index behavior and both distinctness operands.
They charge their own actual reads and prepay the existing W1 loader's count.
Ordinary individual scalar bookkeeping and all existing mutation formulas stay
fixed. Only the initial proof bound changes to 798; runtime caps stay 5,696.

Source-level loop/call counters and closed read-path models are checked in the
existing validators and at every loader exit. Successful loads bind their
source count to the validated logical phase. The valid-state scalar forecast
uses that phase count for every replay iteration. Checked adapter assertions
bind initial prepayment and each reload term to those models. These are logical
source-level work units, not machine-instruction or wall-clock measurements.

The unchanged final source passed **1,235 whole-crate checks with zero errors**
and `--no-cheating`. All **106 runtime tests** pass. The new matrix exercises
45 normal/malformed loader states across exact and short credits, and a
hand-counted three-step tree confirms all three reload charges (58 planning,
132 execution). F2 expectations stay unchanged. All **33 defects in three
affected suites** were semantically rejected after that exact whole-crate
positive: fourteen new K5 controls, fifteen saved-table controls and four
runtime-cap/span-drain controls. Raw logs and exact hashes are bound in
`evidence/brotli-b3c-m1-k5.json` and its control manifest.

Earlier proof failures and old quota-expectation failures are retained and are
not counted as rejections. Updating the approved quota expectations preserves
the prior semantic, exact-credit and one-short assertions.

K5's named change is complete; **M1 remains incomplete**. Full serialized-state
and tree/action replay, remaining header/body outcomes/frames/source ledgers,
complete control closure and B3c/B3d/B4/independent human release review remain
open. No supported-decoder or complete mathematical-safety claim is made.
