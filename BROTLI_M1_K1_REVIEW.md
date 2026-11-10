# K1 source review

Reviewed against `d48e8feb44cd2fc47363809832de295d18270776` on 2026-11-09.
This is the assistant's technical review of the proposed change, not human
approval, a checked implementation, or the independent specification review
required for release. K1 was held when this source review was performed.
The human subsequently explicitly approved K1 as written on 2026-11-09;
that direct approval, rather than this assistant review, lifts the hold.

The exact candidate remains `BROTLI_M1_CANONICAL_PROOF_BOUNDARY_DECISION.md`.
No change to that candidate or the prefix module was made for this review.

## Findings

Source inspection found no contradiction between the proposed classification
and the existing executable installer. This is a feasibility finding; the new
total-success and error-preservation obligations have not been proved.

The existing planner and installer use the same fifteen-bit weights: lengths
1 through 15 contribute 16,384 through 1, and other lengths contribute zero.
Both separately reject lengths above 15, require at least two nonzero lengths,
and require total weight 32,768. The installer additionally restricts sequence
length to 1..704, which the planner's successful scan already requires.
References: `src/brotli_input.rs:1758`, `:27500`, `:27527`, `:27550`;
`src/brotli_prefix.rs:77`, `:96`, `:106`, `:669`.

The recursive sums have different shapes. The prefix model consumes the head
and remaining sequence; the input model accumulates a bounded prefix by its
last element. Agreement needs checked induction and addition identities,
not merely matching names or a runtime comparison. The invalid classification
must preserve the first inspected failure and distinguish an oversized length,
an oversubscribed prefix, an incomplete final sum and insufficient nonzero
lengths. Its cost must retain the actual inspected prefix.

The installer's window/workspace, tree, metadata, symbol-count and initialized-
length guards precede its validation scan. Invalid lengths are rejected before
scratch or tree writes. Under the exact eligible destination domain in K1,
the proposed invalid-length result and unchanged workspace/metadata are
consistent with this order. Outside that domain, existing guard order and
error priority must remain intact. Reference: `src/brotli_prefix.rs:4666`.

Success still requires proving every later builder access and record store
succeeds, and proving both checked numeric guards unreachable for valid
lengths: the expanded next code must fit `u32`, and a canonical code plus rank
must fit `u16`. Existing builder helpers already expose conditional success
for valid workspace/index bounds. K1 must retain the existing canonical-record
and frame guarantees; replacing them with classification alone is insufficient.
References: `src/brotli_prefix.rs:1256`, `:1306`, `:1372`, `:1426`, `:1643`,
`:1773`, `:5279`, `:5495`.

## Exact boundary and tradeoff

K1 exposes the four named existing mathematical definitions and `CODE_SPACE`
to crate proofs and strengthens the existing installer contract. Opening
definitions couples input-module proofs to their exact recursive mathematics
and may increase solver work. It introduces no executable adapter, dependency,
storage, budget policy or changed algorithm. Definitions, constant value,
runtime signature, admitted inputs and executable body must stay unchanged.

No other cross-module definition or helper-contract change is authorized by
K1 as written. If an implementation needs one, that dependent change requires
another explicit human decision. Duplicating the held model elsewhere or
adding assumptions would not resolve the approval or proof obligation.

## Required validation

After explicit human approval, check the installer classification and original
record/frame contracts together; prove planner/installer agreement over the
original builder-length snapshot; verify the entire unchanged source before
running deliberate-defect controls. Controls must exercise false acceptance,
false rejection, numeric-bound reasoning, invalid-case workspace/metadata
preservation and disagreement in weights/counts. Resource exhaustion and
compiler failures cannot count as semantic rejections.

K1 alone cannot close M1. The complete operation ledger, serialized-tree replay,
remaining phase and malformed-state relations and their controls remain
separate M1 obligations. B3c completion, B3d/B4 and independent human review
also remain separate from M1.

## Approved implementation checkpoint

After the direct human K1/K3 approval, the implementation opened exactly the
four named definitions and CODE_SPACE and added the approved installer
classification. The original runtime signature, guard order, algorithm,
admitted inputs, canonical-record guarantees and frame remain intact. Private
checked lemmas equate the planner's prefix sums with the existing prefix model
and discharge the numeric guards for valid lengths.

The final library passed the entire pinned `--no-cheating` check: **1,207
verified, zero errors**, recorded in
`evidence/brotli-b3c-m1-k1-k3-attempt03-verification.json`. The earlier
1,205/one-error run is retained separately. Its loop-entry multiplication fact
was repaired with an explicit checked ghost assertion; no runtime action or
root contract changed. The final test-marker repair changes neither the
intended deliberate defect nor the selected root's specification.

All **33 deliberate defects across five affected suites** were rejected after
their recorded whole-crate positives on identical library bytes. Eight are new
K1/K3 controls and 25 cover the existing builder, table-read/canonical-planning
and suffix-formula behavior. Exact transcripts and ordering are recorded in
`evidence/brotli-b3c-m1-k1-k3-controls.json`. The scope remains the
named K1/K3 properties. The repeat-history runtime regression still fails;
Candidate K4 needs separate direct human approval before its private encoding
change. The complete source-operation ledger, tree replay, remaining M1 and
later decoder obligations, and independent human release review remain open.
