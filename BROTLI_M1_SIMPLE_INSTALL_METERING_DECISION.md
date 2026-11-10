# Brotli M1 simple-tree installation table-read decision

Status: **Candidate K6 proposed; not approved or implemented.**

## Existing boundary and source evidence

M1 requires charging table-cell reads as well as writes and transitions. K5
approved the loader accounting correction while explicitly preserving existing
mutation formulas. The current simple-install reservation remains five units
for a singleton, or `3 * alphabet_limit + 5` for other simple trees. It covers
record-byte writes, four metadata writes and one transition.

`brotli_prefix.rs::install_simple_tree` additionally executes its existing
symbol range/distinctness checks. On the valid descriptor domain used by M1,
these read `c` range operands and `c * (c - 1)` distinctness operands, totaling
`c * c` table reads. Its singleton path then reads `symbols[0]` once more.
For other simple trees, `simple_record_exec` probes the symbol list for every
alphabet value and stops at the first match. Distinct in-range symbols imply
that the complete alphabet scan reads
`c * A - c * (c - 1) / 2` operands, regardless of symbol order.

Here `A = alphabet_limit` and `c` is the existing selector-derived symbol count:
1 for selector 0, 2 for selector 1, 3 for selector 2, and 4 for selectors 3/4.
These are indexed symbol-table operands in the existing executable source.
This evidence is a source-derived count; no measured execution-counter or
complete M1 proof is claimed. The source and worked cases are recorded in
`evidence/m1-simple-install-k6-source-audit.json`.

For `A = 2`, selector 1, symbols `[0, 1]`, validation reads four operands and
record selection reads three. The existing reservation is eleven units; the
same action including those seven reads costs eighteen. For a singleton,
validation plus the final symbol access add two reads to the existing five.

## Candidate K6: meter existing installer reads

Approve exactly this narrow extension of M1:

1. Preserve the existing installer algorithms, guard/error order, admitted
   inputs and helper signatures. Do not remove repeated validation.
2. Charge the two existing singleton symbol reads, making its complete
   installation reservation **7** units instead of 5.
3. For selectors 1–4, add
   `c * c + c * A - c * (c - 1) / 2` table-read units to the current reservation.
   The resulting complete installation formula is
   **`(3 + c) * A + 5 + c * (c + 1) / 2`**.
4. Keep `simple_tree_install_work(alphabet, selector)`'s existing signature.
   Derive `c` from the existing selector; the already-required valid descriptor
   supplies the existing matching count and distinct in-range symbols.
5. Use this exact term in planning and prepaid execution. The read-only
   planner can forecast it with scalar arithmetic and needs no additional
   symbol-table scan. Preserve zero installation work on invalid destinations,
   whose existing guards run before symbol-table validation.
6. Prove the existing installer/table-probe source counts and their agreement
   with the reservation within the existing modules. Private mathematical
   models, ghost counters and proof lemmas may be added; do not add or expose
   any new runtime or cross-module proof API.
7. Retain failed evidence, add unchanged-contract controls for the missing
   read terms, and update only affected quota arithmetic in tests while
   preserving semantic comparisons and exact/one-short reservation checks.
   Run fresh whole-crate verification and the relevant runtime/control gates.

Examples of the resulting reservation:

| Alphabet A | Selector | Count c | Existing | K6 | Added reads |
| --- | --- | --- | --- | --- | --- |
| 2 | 0 | 1 | 5 | 7 | 2 |
| 2 | 1 | 2 | 11 | 18 | 7 |
| 4 | 3 | 4 | 17 | 43 | 26 |
| 704 | 4 | 4 | 2,117 | 4,943 | 2,826 |

This changes work-credit requirements for simple-tree installation. It does
not change format acceptance or decoded bytes. Existing record-write,
serialization and reset formulas stay fixed; this is an added table-read term.

Preserve W1 interfaces/results, B3c budget ownership, workspace layout,
5,696-action caps, the 798-unit initial planning proof bound, existing tree
iteration bounds and the **425-unit construction/reset charge**. The largest
new installation term is 4,943, within the existing 8,192-unit per-iteration
proof allowance. Preserve K4 and the separate F2 fixture policy, the pinned
Rust/Verus/dependencies and every existing root requirement and guarantee.

K6 grants no authority for another architectural or quota change. M1 and the
supported-decoder release gate remain incomplete after this correction alone.

## Approval

Exact direct human approval of Candidate K6 is required before implementing
these quota/formula changes. Broad Brotli authorization does not replace the
human approval rule in AGENTS.md. Independent replay/state proofs may continue
while this decision is pending.
