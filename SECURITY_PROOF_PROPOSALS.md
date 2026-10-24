# Security proof follow-ups requiring decisions

Status: proposals only. No new API, state model, dependency, tool or proof-trust
change is selected or implemented here. The current assessment is in
[SECURITY_CONTRACTS.md](SECURITY_CONTRACTS.md).

The concrete first Brotli milestone is approved in
[BROTLI_PROPOSAL.md](BROTLI_PROPOSAL.md). The reasons these other properties
can be proved, and the models/approvals required, are detailed in
[SECURITY_PROOF_EXTENSION_PROPOSAL.md](SECURITY_PROOF_EXTENSION_PROPOSAL.md).

| Follow-up | Concrete decision to approve first | Required result and limits |
|---|---|---|
| Caller composition | Specify a caller wrapper's observation policy and handling of each `Result`; decide whether it owns/reuses a buffer or a narrower returned view. | Prove that only the current `Ok(n)` prefix is exposed, no stale length survives an error, and any application interpretation/authorization policy uses the intended bytes. This would be a new wrapper/API decision. |
| Across-call state | Select the allowed call/reset/error sequences and a formal trace/state representation for a chosen streaming API. | Prove invariant establishment and preservation for all allowed transitions. Current stateless per-call contracts alone do not prove a session protocol. |
| Brotli | Select one-shot versus streaming scope, valid state construction, dictionary/window support, buffers/errors and exact comparison references. | For streaming, prove pending bounds, permanent-error versus true-input-exhaustion distinction, chunk-independent authorized output and progress under retries. Preserve an actual multi-call regression and a fatal-to-retry defect control. |
| Quantitative work | Approve which operations a Base64/percent cost ledger charges and which deployment limits it is meant to support; retain the existing LZ4 ledger's stated units. | Add checked accounting in the existing model without calling it a cycle or practical DoS bound. Input/output/concurrency/rate/time budgets need a separately specified caller policy. |
| Concrete deployment | Choose the exact shipped artifact, target, ABI/build flags and executable model; decide whether to retain compiler trust or propose an additional translation/machine checker. | Bind deployment to checked source and verify the chosen bridge. New verifier/runtime dependencies require exact approval. Current hashes and tests are provenance, not a verified compiler. |
| Side channels | Specify the secret/public labels, observable timing/cache/error behavior, target and cost semantics. | Prove the chosen noninterference/constant-time property or explicitly retain it as unproved. Table lookup correctness does not imply constant-time access. |

Independent specification review requires a reviewer and scope, followed by
actual findings and reproduction. Creating a checklist or running the proof
model again is not that review. Contacting reviewers needs explicit messaging
authorization; none is sent by these proposals.
