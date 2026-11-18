# M1 source-receipt and prepaid-action refinement checkpoint

Status: **the named M1 compressed-header source-receipt and prepaid-action
refinement scope is complete** on the exact source recorded in
[`evidence/brotli-b3c-m1-source-receipts.json`](evidence/brotli-b3c-m1-source-receipts.json).
The `m1-source-receipts-final04` gate binds **1397 whole-crate checks with zero
errors**, **116 runtime tests**, and all **48 required suites /
318 semantic defect rejections** after the unchanged positive. These totals
come from the actual gate records, not the earlier checkpoints or diagnostics.

Approach R transfers invocation-specific source counts from reached primitive
events and child receipts through the compressed-header helper graph. The
receipts cover partial input, validation failures and resource failures.
Ordinary plan fields remain forecasts; returned ghost receipts count the
operations actually reached. Reservation formulas and budget differences are
comparison targets, never substitutes for receipt construction.

Read-only planners charge the existing input-byte, selected-bit, logical-record,
table and context-cell units as their reads occur. Failed planning preserves
the caller workspace and retains charges for the inspected prefix. B3c remains
the RequestBudget owner. It reserves the exact remaining execution work before
the first mutation. Failed reservation preserves the whole workspace;
already-performed planning work stays charged. Successful reservation binds the
actual execution receipt and the owner's terminal or phase action to the debit.

The results retain the original phase, workspace, queue, metadata and saved-state
requirements, including malformed saved states admitted by the owners.
Installed-symbol cost equalities retain their existing conditional workspace
and tree-geometry hypotheses, established by the relevant callers. They do not
extend a legacy attempt-cost witness universally or strengthen helper entry
requirements. Planned and actual consumption, status/error and saved-state
transitions agree in the named admitted domains.

Serialized-tree frames distinguish parser/noncompletion writes from completion's
additional canonical scratch, selected-tree and metadata writes. Singleton
completion has no tree-record writes. Header/context ranges remain preserved.
Malformed tree starts consume no input and preserve the executor's entire
workspace; under valid workspace shape their error is InternalState. The owner
separately performs its prepaid terminal latch when required. Other
header/context/group/tail actions retain their outcome-specific frames. Frames
bound permitted writes; reached-operation receipts establish source counts.

The implementation changes **157 existing private helper return types** to
`(T, Ghost<nat>)`, keeping old results and guarantees on component 0. Together
with the new private `CompressedMetaBlockDecoder::step_with_receipt`, the exact
source inventory contains **158 receipt producers**. The original W1 `step`
wrapper, `CompressedHeaderStep` and public Brotli interfaces remain unchanged.
The private compiled return types do change. The actual library-test transcript
includes `m1_proof_receipts_erase_without_runtime_storage`, checking the
zero-sized ghost marker and the selected paired results' size and alignment.
This is not a source-to-binary correctness theorem.

The qualified audit preserves all **424 actual preimplementation e10c spec
bodies**, 423 byte-exact headers and the single approved
`m1_canonical_nonzero_index_sum` visibility opening with unchanged body and
decreases. The proposal f1a baseline separately has 416 preserved spec bodies.
Old arguments, requirements and guarantees remain. Original allowance values
and attachments remain; the two recorded solver-isolation additions are
identified separately. Source-origin and call-edge inventories are static
audits, not independent operation-equality proofs. Their exact core hashes are
bound to the passing gate; their historical test snapshots are retained, while
the final gate separately binds the complete final test closure.

Allowance preservation concerns the production annotated core.
`CodeDescriptionDecoder::advance_field` retains its production allowance of
500. One instrumented field-truncation control uses allowance 1,000 in both
its temporary positive and negative copies, matching the existing global
checker allowance. This is solver effort only; it changes no RequestBudget,
source-unit policy, admitted input, model, contract, API or production body.
Four native harness assertion predicates gained recognition of the existing
strict computed-false diagnostic, restricted to the cap, field, two named
suffix-family cases and cursor case. Every original assertion site, diagnostic
arm and tool/resource exclusion remains; those four predicate texts are
extended. The frozen gate classifier and production specifications are unchanged.

The proposal input
`f1a37362e128944c9c0ca49f00f30c172270677140e60027d3d655c46d831eef`
and actual preimplementation input
`e10c61b1354c5b1debef9e76aa55b412d06e35de210cb8949a73ef33b912da23`
remain distinct. The preceding two-cursor-owner repair uses the existing
four-write plus one-transition terminal-five policy. It is not a new R unit
policy. No audit infers human architectural approval or rewrites the proposal.

Existing scalar/forecast zero-unit rules, caller-owned workspace, K4 encoding,
K6 costs, 5,696 action caps, 798/8,192 proof bounds, 425-unit reset charge,
dependencies and proof trust remain fixed. Trusted components include the
mathematical specifications, source-unit interpretation and counter placement;
pinned Verus 0.2026.10.18.7d82994, Z3 and vstd; Rust 1.99.1/LLVM; Apple build
tools; and the machine and operating environment.

The final receipt binds the actual positive, all 48 complete suite rows, 318
fresh semantic-rejection records, frozen source archive, tools, gate driver,
gate inputs, and file/hash maps. Resource, syntax, panic and interrupted
results are excluded. Earlier final01 positive failures and final02 control
failures remain historical evidence; isolated repair diagnostics do not count
as the final gate.
The separately bound integrated-harness static review must match the actual
passed test closure. It preserves the old native assertion sites/arms and
checks generated-source assembly; it is not a proof, native run or gate result.

The immutable final03 whole/runtime positive passed 1,397 checks with zero
errors and 116 runtime tests. Its subsequent focused batch selected 11 suites
and 88 cases: eight suites passed, covering 70 accepted cases, while three
suites were blocked by resource failures. The full 48-suite gate was never
started for final03. This is a failed focused batch after a passed positive,
not a failed full-gate attempt. Its original receipts and all failed diagnostic
variants retain their statuses.

Sealed supplementary validation is published separately under
`evidence/m1-source-receipts-final04/supplemental-validation/initial/` and
`evidence/m1-source-receipts-final04/supplemental-validation/followup/`. The completion receipt
and documentation-promotion file map bind both published manifests and archives.
These bundles preserve admitted/reached witnesses, necessary consequences of
the unchanged contracts, isolated control pairs, independent technical audits
and historical failures. They do not replace the real whole/runtime gate or
any of the 48 suites / 318 cases, and they do not rewrite its frozen package.

Witness-coupled literal computed-false rejections occur during verification
before negative-body SMT may run. Checked admitted/reached witnesses and
old-contract implication proofs justify the required certificate, returned-status,
debit, frame or receipt consequence. The computed-false outputs reject its
source-coupled faulty instances; they do not establish negative-body SMT completion
or a native execution trace. The final receipt separately lists the actual raw cases whose
strict classifier reports computed false and those reporting a checked semantic
error. No isolated witness result is counted as a full-gate pass.

This completes the named M1 compressed-header resource/refinement scope.
Remaining B3c work, B3d/B4, arbitrary caller or call-sequence composition,
source-observation results, independent human specification review and release
obligations remain separate. F2 is unchanged: `quickfox_repeated` decodes to its
pinned bytes; `monkey` retains zero-output sticky `ContextMapRepeat` rejection
and its unresolved native disagreement. This checkpoint does not complete a
supported decoder, release, side-channel claim or source-to-binary proof.
