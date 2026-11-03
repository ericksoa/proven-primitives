# M1 nested transition accounting decision

Status: **Option A approved explicitly by the human on 2026-11-03:**
“Charge nested resets/starts separately.”

M1 and C1 require exact work for parser transitions. The preceding
initialization formulas treated nested decoder starts inconsistently. The
human resolved that policy ambiguity by explicitly selecting Option A.

This decision is limited to nested parser reset/start events during compressed
header parsing. Both options retain the approved 425-unit construction/reset
charge, exact byte/cell charges, interfaces, workspace layout, dependency set,
budget ownership, and proof trust boundary.

## Evidence from the current source

- `context_bits_execution_work`, for phase 1 with zero or phase 2, charges the
  76 tree-start writes and an additional tree-start transition, then the
  max-run byte, context-phase byte and context transition. With its existing
  read/queue/action base this is `read_work + 91`.
- `plan_block_tree_action`, when a block-type tree completes and starts the
  length tree, charges `76 + 1 + 1`: tree-start writes, outer-phase write and
  one transition. This is `tree_execution_work + 78`.

The first formula charges the nested tree reset separately; the second
includes no separate unit for the analogous reset.

## Option A: charge nested resets/starts separately

Each explicit nested decoder reset/start adds one transition unit in addition
to the enclosing transition. Ordinary bookkeeping assignments and scratch
initialization do not independently create parser transitions.

For the two examples, the context-bit formula remains `read_work + 91`, and
the block-tree formula becomes `tree_execution_work + 79`. Apply the same rule
consistently to the remaining nested parser initializers and bind their exact
source events in the checked ledger.

## Option B: include resets/starts in the enclosing transition

A nested decoder reset/start is covered by its enclosing B3b transition rather
than charged as a separate transition. Independently executed parser steps
remain charged by their own existing transition contracts.

For the two examples, the context-bit formula becomes `read_work + 90`, and
the block-tree formula remains `tree_execution_work + 78`. Apply the same rule
consistently to the remaining nested parser initializers and bind their exact
source events in the checked ledger.

## Adopted rule

Option A is selected. Charge each explicit nested decoder reset/start separately
from its enclosing transition. Option B is unselected. Apply the rule throughout
M1 compressed-header parsing and bind the resulting formulas to the checked
source ledger. The 425-unit construction/reset charge remains fixed.

## Applied initialization formulas

The input-private planning helpers now use these Option A costs. Writes and
transitions are separate units; enclosing actions add their own documented
writes and transition.

| Existing action | Work |
|---|---|
| Serialized tree start | 76 writes + 1 nested transition = 77 |
| Context-map start, including VAR_UINT8 reset | 14 writes + 2 nested transitions = 16 |
| Installed-prefix reset | 5 writes + 1 nested transition = 6 |
| Group-tree start | Tree start + 3 writes + 1 group transition = 81 |
| Tree-group start | 4 writes + group reset + group-tree start + outer write/transition = 88 |
| Initial B2 Ready state | 28 writes + 1 nested transition = 29 |

The context-bit tree-start expression remains `read_work + 91`. The
block-type-to-length-tree handoff adds 79 to its tree-action work. Completing
literal context modes costs 18. These formula contracts and their undercharge
controls do not replace the remaining complete source-operation ledger proof.
