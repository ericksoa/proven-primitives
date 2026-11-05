# Private tree-action bound decision

Status: **5,696 actions approved explicitly by the human on 2026-11-04:**
“Approve 5,696 actions.” The existing 2,000-action alternative is unselected.

A retained private-tree regression describes a complete 704-symbol canonical
command tree: final code lengths are one at indices 0 and 703 and zero at the
other 702 indices. A complete auxiliary alphabet gives zero a five-bit code;
using direct zero descriptions is permitted. The description occupies 442
bytes.

The current serialized tree parser completes this description in one-byte
chunks. Supplied as one slice, it reaches its 2,000-action loop cap after 251
bytes and 398 final symbols and returns `InternalState`. The retained evidence
is `evidence/brotli-m1-tree-action-bound-diagnostic.json`. This is an internal
tree description, not a complete Brotli message.

## Approved bound

Raise the two input-private tree-loop caps, in `advance_serialized_tree` and
`plan_serialized_tree`, from 2,000 to **5,696 actions**, expressed as
`8 * 704 + 64`. Complete the proof of the action bound and the unchanged
source/plan behavior, and rerun all affected verification and controls.

The ordinary request work budget remains authoritative and is charged for the
actions actually executed.

This changes only these two internal loop caps. Interfaces, workspace, parser
representations, dependencies, format target, error definitions, budget
ownership and the 425-unit construction/reset charge remain unchanged.

## Other choice

Keep the current 2,000-action caps while a different bound or approach is
reviewed. The demonstrated whole-slice failure remains unresolved and the
complete-decoder release gate stays closed.

The human approved this exact change and the subsequent proof and verification
work on 2026-11-04. Approval is not itself evidence that the universal action
bound or complete decoder has been proved.

## Checked action-rank argument

The current implementation assigns each field-parser phase a natural-number
rank in `code_phase_rank`. For an admitted alphabet limit `L`, it proves
`rank <= 8 * L + 63 <= 5,695`. Each nonterminal field action that continues
strictly decreases this rank. Pending-span drainage also decreases the rank;
an auxiliary-alphabet completion may perform a further zero-input action with
another strict decrease. NeedInput and terminal outcomes return immediately.

`code_rank_aligned` records the relation between a pending span's end and its
continuation. The loader establishes it from the existing serialized
representation. It is a theorem premise, not a new executable input
restriction. The load/store proofs connect the local rank to the serialized
rank, so the actual parser's repeated state reloads preserve the argument.

The actual parser maintains `actions + serialized_rank <= 5,695` after a
continuing action. The read-only planner maintains
`actions + local_rank <= initial_rank <= 5,695`. Thus neither can reach the
5,696-action fallthrough; both have a checked unreachable assertion there.
The selected parser and planner checks pass without assumptions, admitted
proofs or trust bypasses. Final whole-crate verification and deliberate-defect
controls are still pending; this does not establish M1's remaining full
plan/action and source-operation-ledger obligations.

The action-rank work also exposed an independent pending-span defect: a saved
implicit trailing-zero span was advanced before being written. Both loops now
drain an already-pending span before advancing. The retained regression
`m1_complex_tree_drains_implicit_trailing_zeros_before_install` failed before
the correction and passes afterward. The resulting F1 fixture-classification
conflict is documented separately in `BROTLI_B3C_FIXTURE_F2_DECISION.md`;
those approved expectations have not been silently replaced.

The human subsequently approved **F2 as written** on 2026-11-04. Its
comparison assertions now require correct `quickfox_repeated` output and
retain `monkey`'s checkpoint rejection with the actual unresolved reason.
Before those test changes and the additional local frame/debit contracts,
the frozen source passed 1,174 whole-crate checks with zero errors and all 87
deliberate defects across 13 suites were rejected. The exact source is retained
as `evidence/m1-saved-table-before-f2-source.patch.txt` relative to commit
`c3e6355`, with its original frozen hashes. Final F2-source validation remains
separate from that successful earlier run.
