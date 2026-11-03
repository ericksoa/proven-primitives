# Private tree-action bound decision

Status: **pending direct human approval**. Neither choice below is adopted.

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

## Proposed bound

Raise the two input-private tree-loop caps, in `advance_serialized_tree` and
`plan_serialized_tree`, from 2,000 to **5,696 actions**, expressed as
`8 * 704 + 64`. Complete the proof of the action bound and the unchanged
source/plan behavior, and rerun all affected verification and controls.

The allowance is intended to cover bounded auxiliary-prefix parsing and final
symbol/repeat/pending-span actions across the approved maximum 704-symbol
alphabet. It is not yet a checked universal bound. The ordinary request work
budget remains authoritative and is charged for the actions actually executed.

This changes only these two internal loop caps. Interfaces, workspace, parser
representations, dependencies, format target, error definitions, budget
ownership and the 425-unit construction/reset charge remain unchanged.

## Other choice

Keep the current 2,000-action caps while a different bound or approach is
reviewed. The demonstrated whole-slice failure remains unresolved and the
complete-decoder release gate stays closed.

Implementation of the changed bound waits for the human's explicit answer.
