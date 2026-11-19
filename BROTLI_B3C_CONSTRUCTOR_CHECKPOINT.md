# B3c public-constructor proof checkpoint

Status: the constructor checkpoint is complete for the exact source bound in
[`evidence/brotli-b3c-constructor-i2.json`](evidence/brotli-b3c-constructor-i2.json).
The human approved **I2 as written** on 2026-11-19 in
[`BROTLI_B3C_CONSTRUCTOR_PROOF_BOUNDARY_DECISION.md`](BROTLI_B3C_CONSTRUCTOR_PROOF_BOUNDARY_DECISION.md).
This checkpoint follows the completed M1 source-receipt refinement; it does not
complete B3c or a supported Brotli decoder.

The public `BrotliDecoder::new` contract now connects successful construction to
its existing `valid` predicate, the entry requirement of public `step`. It also
establishes the unchanged workspace length, no stored terminal result, immutable
limits, and exact consumption of one initialization credit and 425 work units.
The existing `reset_effect` relation preserves input, output and call counters.

For every admitted valid before-budget, the contract classifies all constructor
results. The required workspace length is
`(1 << max_window_bits) + 1_176_560`; checked constant equalities connect both
that fixed overhead and the 425 charge to the implementation's private constants.

- Too-small workspace returns `WorkspaceTooSmall`, preserving the entire
  workspace and budget before attempting a reservation.
- Adequate workspace with zero initialization credit returns `ResourceLimit`,
  preserving the workspace and budget.
- Adequate workspace with an initialization credit but fewer than 425 work
  units returns `ResourceLimit`, consuming one initialization credit, preserving
  work and the entire workspace.
- Adequate workspace and both credits yield success with the effects above.
  `InvalidLimits` is impossible under the existing valid-budget requirement.

I2 adds exactly three public closed specification observations on
`RequestBudget`: `limits_view`, `remaining_work`, and
`remaining_initializations`. They describe the actual existing fields.
`RequestBudget::new` now guarantees that those observations match its supplied
limits on success. No other observer or visibility opening was added.

The `b3c-constructor-i2-final02` gate records **1397 whole-crate checks with
zero errors**, **116 runtime tests**, and **six semantic defect rejections**.
The unchanged entire-crate `--no-cheating` positive completed before any defect
control. The constructor-only suite also checked its unmutated constructor
before changing private copies. Controls preserve the constructor contract and
change executable behavior: omitted reservation, spurious resource failure,
small-workspace credit consumption, replenished work, a finished initial state,
and wrong workspace-error classification. Every control was rejected by a
checked semantic error; syntax, type, solver-resource and tool failures do not
count. These six controls are this checkpoint's inventory; the earlier M1
318-case control result remains historical and was not rerun here.

The frozen gate records source/test/build inputs, tool identities, actual logs,
commands, the source archive, and strict control classifications. Its exact
helpers are bundled with reconstruction instructions. The separate static
preservation audit confirms that all other tracked core, tests and build inputs
match the M1 parent, the old test file is an unchanged prefix, and replacing only
the two approved constructor sections and removing the three observations
reconstructs the entire old `brotli.rs`, after also removing the single named
solver-isolation annotation. Both executable constructor bodies are
byte-identical after removing the newly inserted leading proof block. This is a
source preservation audit, not a source-to-binary theorem.

The preceding `final01` whole proof checked 1,396 functions and reported one
solver resource failure in the unchanged distance-symbol helper; controls were
not started. Its original logs and frozen source are retained. The final source
adds the existing `spinoff_prover` proof annotation to that helper, with its
original allowance of 90 and complete signature, contract and body unchanged.
An isolated diagnostic checked the helper before the fresh full gate. This
changes solver context only; no RequestBudget or runtime policy changed.

All prior requirements, models, guarantees, runtime signatures, algorithm and
error order, workspace layout, resource policy, dependencies and proof trust
remain. The trusted base includes the mathematical specifications, pinned
Verus/Z3/vstd and Rust/LLVM stack, Apple build tools, and operating environment.
This technical proof checkpoint is not independent human specification review.

Remaining B3c command/literal/distance and dictionary refinement, actual B2
caller composition, atomic output/history and LZ77, EOF/backpressure/resource
settlement and later public-root/call-sequence obligations remain separate.
B3d/B4 and release gates are also open. F2 is unchanged: `quickfox_repeated`
decodes to its pinned bytes; `monkey` retains zero-output sticky
`ContextMapRepeat` rejection and the unresolved native disagreement.
