# B3c constructor proof interface decision: I2 approved

Status: the human explicitly approved **I2 as written** on 2026-11-19.
I1 remains unselected. I2 is implemented and checked in
`BROTLI_B3C_CONSTRUCTOR_CHECKPOINT.md` and
`evidence/brotli-b3c-constructor-i2.json`. The proposal and alternatives below
record the boundary presented for that decision; their preimplementation
limitations describe the earlier source.

The approved C1 behavior fixes constructor workspace priority, the 425-unit
initialization charge, and its counter effects. The next public-root proof
connects a successful constructor to the existing public `valid`,
`workspace_view`, `budget_view`, and `stored_terminal_result` observations.
It also uses the existing public `RequestBudget::reset_effect` relation for
successful construction and resource failure. Those guarantees require no new
interface, representation, algorithm or visibility.

Complete public workspace-error classification still needs a proof interface.
A public function's contract cannot refer to the crate-private fixed-scratch
constant, scalar-state definitions or the private fields of `RequestBudget`.
The pinned verifier rejected that boundary in
`evidence/b3c-constructor-i2-final02/diagnostics/b3c-constructor-selected02.log`. No visibility was opened to bypass it.
The current conditional constructor guarantees do not establish that every
sufficiently sized and funded construction succeeds; they must not be reported
as that stronger result.

The human must choose the public proof boundary before its implementation.
These alternatives retain every existing signature, requirement, guarantee,
executable statement, error priority, counter policy, workspace allocation,
dependency, pinned tool and trust boundary. They add only the named erased
proof interfaces and the corresponding public postconditions. No new ordinary
Rust API, runtime counter or persistent field is proposed.

## I1: one closed construction-effect relation

Add exactly this public, closed specification method in `RequestBudget`:

```rust
pub closed spec fn construction_effect(
    &self,
    before: RequestBudget,
    workspace_length: nat,
    result: Result<(), InitError>,
) -> bool
```

`self` is the post-construction budget. The method describes this exact C1
relation, under the constructor's existing valid-before-budget requirement:

- Required size is `(1 << before.limits.max_window_bits) + 1_176_560`.
- A smaller workspace means exactly `Err(WorkspaceTooSmall)` and an unchanged
  budget, before any credit attempt.
- A sufficient workspace means the existing `reset_effect(before, result)`:
  zero initialization credit fails unchanged; an initialization attempt with
  insufficient work consumes that initialization credit only; sufficient
  initialization and work credit succeeds with one initialization credit and
  425 work units consumed. Input, output and call counters stay unchanged.
- `InvalidLimits` is not a constructor result when the before-budget is valid.

Strengthen only `BrotliDecoder::new`'s postcondition to bind its actual returned
budget/result to that relation, keeping the existing successful validity,
nonterminal state, workspace length and error atomicity guarantees.
The existing initializer's canonical scalar-image guarantee remains a checked
premise; this alternative does not open private layout definitions publicly.

This keeps the added surface to one named relation. Its body stays closed to
other modules/crates. Downstream proofs can retain and compose the abstract
relation, but extracting additional numeric consequences outside the owning
module may require separately reviewed public lemmas later. No such later
lemmas are preapproved here.

## I2: three closed budget observations

Add exactly these public, closed specification methods in `RequestBudget`:

```rust
pub closed spec fn limits_view(&self) -> RequestLimits
pub closed spec fn remaining_work(&self) -> u64
pub closed spec fn remaining_initializations(&self) -> u32
```

They return the existing immutable limits, current work counter and current
initialization counter. Add the corresponding success guarantees to the
existing `RequestBudget::new` so the observations match its supplied public
limits. They must continue to describe the actual fields after later effects.

Express `BrotliDecoder::new`'s complete workspace/error classification directly
using these observations and the already-approved fixed overhead literal
1,176,560, with checked agreement to the implementation's existing private
constant. Keep using the existing `reset_effect` for exact counter changes,
including unchanged input/output/call counters. Preserve all other constructor
guarantees and executable code.

This exposes three independent proof observations rather than an opaque
construction relation, making later client reasoning about sizing and the two
initialization counters more direct. It makes a broader public proof API
commitment. It does not expose the input/output/call counters, add a new state
type, or authorize other observers or a visibility opening.

## Verification after selection

Verify the chosen relation/observations against actual fields and connect the
complete constructor result and budget effects without narrowing its admitted
inputs. Add unchanged-specification controls for spurious constructor failure,
workspace-error priority and initialization/work settlement. Run an unchanged
whole-crate `--no-cheating` positive before controls, retain actual logs and
source/tool identities, and reject syntax/type/resource failures as controls.
Preserve the completed M1 evidence as a historical checkpoint. Neither choice
completes B3c, B3d/B4, the F2 native disagreement, independent human
specification review, a supported decoder or release.

Architectural authority remains with the human. Approval to continue Brotli or
complete a milestone does not select either new public proof interface.
