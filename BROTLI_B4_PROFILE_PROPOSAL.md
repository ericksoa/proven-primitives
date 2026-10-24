# B4 quarantining caller and PP-Security/1.0.0 proposal

Status: the human approved this B4 architecture exactly as written on
2026-10-24. It depends on a completed, checked B3 decoder. This approval does
not name an independent reviewer, add a dependency, service, or tool, or change
the proof trust boundary.

## Exact complete-message caller

Add a public safe wrapper around the approved provisional-output core:

```rust
pub struct BrotliMessageDecoder<'w, 'b, 'q> { /* private */ }

pub struct MessageStep {
    pub consumed: usize,
    pub status: MessageStatus,
}

pub enum MessageStatus {
    NeedInput,
    Finished,
    Failed(StreamError),
}

impl<'w, 'b, 'q> BrotliMessageDecoder<'w, 'b, 'q> {
    pub fn new(
        workspace: &'w mut [u8],
        quarantine: &'q mut [u8],
        budget: &'b mut RequestBudget,
    ) -> Result<Self, InitError>;

    pub fn step(&mut self, input: &[u8], end_of_input: bool) -> MessageStep;
    pub fn message(&self) -> Option<&[u8]>;
    pub fn reset(&mut self) -> Result<(), InitError>;
}
```

The wrapper directs every provisional core prefix into caller-owned quarantine
storage. It never returns a provisional slice. `message()` is `Some` only after
the current stream reaches `Finished`, the intended final input is consumed and
no trailing byte is present. It returns exactly `quarantine[..published_len]`.
Every error, limit, reset and new attempt clears `published_len` before any
further processing. Old quarantine bytes and suffixes remain physically present
but are never part of the authorized view.

The quarantine capacity must be no greater than `limits.max_output` and is the
complete-message storage bound. If it fills before stream completion, the
wrapper returns terminal `ResourceLimit`; it does not expose a partial message
or request an unbounded replacement buffer. Input not consumed because the core
stopped remains with the caller. Empty calls, arbitrary chunks and retries use
the core's finite call budget. Finished/failed states are sticky until an
explicit charged reset. Trailing data maps to permanent `InvalidFormat` under
the one-message policy.

Required checked caller properties cover every permitted call sequence:

- Core guarantees satisfy the wrapper's workspace, buffer, status and ownership
  preconditions at every call.
- Only the current produced prefix advances quarantine length; stale lengths,
  old suffixes and a failed attempt can never be published.
- Core provisional writes remain documented internal effects after a later
  error. There is no false system-wide rollback claim.
- `message()` equals the complete mathematical Brotli result exactly when it is
  present, and its bytes are independent of unrelated old workspace/quarantine
  storage.
- Total memory is workspace plus fixed wrapper state plus quarantine. Work,
  calls, input, output, initialization and reset remain bounded by the one
  request budget; wrapper transitions are charged.
- Deliberate defects pass the whole allocation, retain a stale length, expose a
  failed provisional prefix, accept trailing data, replenish credits on reset,
  ignore one core result, or loop without charging; every defect must be rejected.

This proves this exact wrapper, not arbitrary HTTP/RPC/file integrations or an
application that bypasses it and calls the provisional core directly.

## Exact PP-Security/1.0.0 normative families

Create profile `PP-Security/1.0.0` with these clause revisions. Every clause's
formal bindings, applicability rows and evidence files are part of the frozen
profile closure; unknown capability or applicability values deny release.

| Clause | Normative obligation |
|---|---|
| `BOUNDS/1` | Every read, write, index, offset, length and machine-integer operation is in range for all admitted inputs and modeled states; every internal loop terminates. |
| `FORMAT/1` | Success and permanent/retryable errors refine the approved mathematical format and exact error-priority contract. Unsupported format extensions receive the approved explicit result. |
| `FRAME/1` | Each returned result has its exact authorized buffer/state effects; successful prefixes and preserved suffixes are explicit, and error preservation never implies rollback of earlier successful stages. |
| `CONF-VALUE/1` | Every authorized returned/published byte depends only on current authorized inputs/state. Unrelated old buffer/workspace bytes cannot enter it. |
| `STATE/1` | Constructors establish and every permitted call/reset/error/retry preserves the state invariant. Permanent errors and completion are sticky; genuine exhaustion denotes a viable unfinished parse. |
| `CALLER/1` | A caller adapter handles every result, passes current prefixes/remainders only, clears stale publication state, follows the permitted call sequence and exposes only its authorized view. |
| `RESOURCE/1` | Input, output, memory, abstract work, calls, initialization and resets have checked per-call and cumulative request bounds; no retry/chunk/reset mints budget. |
| `SIDE-SOURCE/1` | With equal public inputs/capacities/logical state and different unrelated old storage, the checked source observation traces are equal. |
| `BUILD/1` | Evidence binds exact source/profile/approval/verifier/options/dependencies/target/build artifact and declared trusted components. |
| `REVIEW/1` | A named independent human reviewed the specification interpretation, threat model, applicability, proof bindings, controls, comparisons and trust boundary, with a hashed report and resolved findings. |

## Applicability matrix

The target advertised set is the five current public routines, C1, the raw
Brotli streaming core and `BrotliMessageDecoder`. No historical release is
retroactively assigned this profile.

| Capability | Applicable clauses |
|---|---|
| Stateless byte transform | `BOUNDS`, `FORMAT`, `FRAME`, `CONF-VALUE`, `STATE`, `RESOURCE`, `SIDE-SOURCE`, `BUILD`, `REVIEW`; `STATE` proves arbitrary independent reuse and errors cannot create retained library state |
| Complete-buffer decoder | The same stateless set, including the cross-call no-retained-state induction required by `STATE` |
| Retained-input/output-producing streaming decoder | All clauses except `CALLER`; provisional prefixes are an approved disclosure of the raw core and complete-message authorization is not claimed for it |
| Caller adapter or composition | `BOUNDS`, `FORMAT`, `FRAME`, `CONF-VALUE`, `STATE`, `CALLER`, `RESOURCE`, `SIDE-SOURCE`, `BUILD`, `REVIEW` |
| Request-resource policy | `BOUNDS`, `STATE`, `RESOURCE`, `BUILD`, `REVIEW` plus every clause inherited from the decoder/caller it governs |

`not_applicable` is derived only from this matrix and an object's approved
semantic capabilities. It is never a per-CVE waiver. C1 and the Brotli message
wrapper have their own composition identities and evidence; component proofs
are premises, not inherited system guarantees.

## Exact source-observation model

For `SIDE-SOURCE/1`, public information is: current input bytes and lengths,
capacities, approved initialized logical state, format mode, limits, call/chunk
schedule and permitted result/output disclosures. Secret state is unrelated old
destination, scratch, window and quarantine bytes outside initialized/authorized
ranges.

The source trace contains ordered events for:

- branch decisions;
- indexed read/write locations as `(approved region, logical index)`;
- charged source-work events and state transitions; and
- statuses, progress counts and authorized lengths already permitted as public.

Instrument the actual relevant source helpers with proof-only trace updates
adjacent to each modeled branch/access/action. A root relational theorem runs
two executions with equal public values and arbitrary different secret storage
and proves equal traces and equal authorized results. A separately written ghost
summary that is not connected to actual operations does not satisfy the clause.

This target does not hide current input, input length, validity, output or the
documented progress/status disclosures. It is not constant-time handling of a
secret compressed message. Rust/LLVM preservation of the source trace, machine
timing, caches, speculative execution, power and other physical leakage remain
outside the claim and explicitly trusted/unproved; no new compiler or hardware
checker is introduced.

## Resource and deployment statement

The complete wrapper theorem gives a finite bound for one admitted request.
Practical service availability additionally requires a deployment to choose and
enforce admission, concurrency, rate, host-capacity and scheduling policies.
B4 records those as deployment assumptions; the library does not invent numeric
defaults or claim unconditional availability under unlimited requests.

## Independent review and release gate

The human must name an independent reviewer who was not an author of the
implementation or proofs.
The required review scope is:

1. RFC 4648, RFC 3986, LZ4 raw-block and RFC 7932 interpretation, including the
   immutable dictionary/transforms and supported/unsupported modes.
2. Attacker controls, permitted observations/disclosures, error effects,
   resource units, call sequences and deployment assumptions.
3. Clause applicability for every advertised object and every known CVE case.
4. Root proof bindings, negative controls, native comparisons and all unresolved
   source-to-binary or source-to-machine gaps.

The signed review record contains reviewer identity, date, scope, exact profile
and source digests, report SHA-256, findings and dispositions. Automated review,
tests, and additional proof runs cannot satisfy the independent human review
requirement.

P1 then creates the immutable release manifest and denies release unless all
applicable rows are `checked`, the independent review is approved, current
source/artifact/verifier/dependency identities match, all required proof and
gate controls pass and the human explicitly selects the advertised support set.
Historical evidence remains unchanged and receives a visible newer-profile gap
assessment.

## Approval requested

Approval of B4 authorizes the exact `BrotliMessageDecoder` API/state/publication
policy, quarantine-capacity failure behavior, caller proofs/controls, normative
clause text, applicability matrix and source-observation model above. It does
not by itself mark any object supported, provide independent review, choose
deployment limits, approve B3, or change the proof trust boundary.
