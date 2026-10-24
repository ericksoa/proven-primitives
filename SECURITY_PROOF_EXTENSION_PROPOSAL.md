# Extending security proofs

Status: the human approved these proof scopes on 2026-10-24 where their exact
state, cost, and observation semantics are supplied by the approved B2 and C1
proposals. No new trust component or unspecified deployment model is approved.
“Unproved” in the [assessment](SECURITY_CONTRACTS.md) means no checked result is
claimed; it does not mean the property is inherently beyond mathematical proof.

## Why the existing proofs do not establish these properties

The current contracts describe values, memory effects, arithmetic and termination
of one invocation. They do not describe an application's publication behavior,
a stream protocol, timing/cache observations or admission/concurrency policy.
Those missing semantics require specification and implementation work.
Some stronger claims would also be false for the current algorithms or for
an environment allowed to submit infinitely many requests.

## Side channels: relational execution and an observation policy

A possible theorem compares two executions with equal approved public inputs
and different secret state, and proves their observable traces equal, except
for explicitly authorized disclosures. The observations must be specified:
for example branches, accessed addresses and operation counts. A relation over
return values alone does not establish equality of those traces.

The existing prefix-independence lemmas already compare returned bytes with
different old destination contents. A proposed next claim could hold the input
bytes and capacity public and vary old destination contents, proving that the
modeled branch/address/work trace is independent of those old contents too.
That would be narrower than hiding the current input's content or length.

For secret current input, the current Base64 tables use content-dependent
indices, decoding has content-dependent branches, and percent-encoded length
depends on content. A constant-time claim cannot simply be attached to these
implementations. Also, a publicly released reversible encoding intentionally
reveals its input; the permitted output disclosure must be explicit. A different
algorithm or observation policy would require its own approval.

Such proofs are established research, not an impossibility:
[Almeida et al., Verifying Constant-Time Implementations](https://www.usenix.org/conference/usenixsecurity16/technical-sessions/presentation/almeida)
verifies constant-time properties of optimized LLVM code through a reduction
to a product program simulating two executions. This is evidence that the
proof class is feasible, not an endorsement or installation of its tools here.

Source-level traces would still rely on a compiler/hardware bridge. Extending
the claim to a specific machine's timing/cache behavior needs a justified
machine model, instruction-latency assumptions and deployment binding.
An unrestricted claim covering every physical side channel is not proposed.

**Decision needed:** approve secret/public labels, authorized disclosures,
observations, exact implementation/target, and whether compiler/hardware
preservation stays assumed or is checked with separately approved tools.

## Caller composition: verify a particular caller

The proposed first example is a private, verified caller of an existing codec,
with reusable output storage and an explicit current-call publication view.
On success it exposes exactly the returned prefix; on either error its
publication view is empty and its remembered success length is invalidated.
An inductive proof over all allowed calls would cover success, error, retry,
arbitrary initialized buffers and reuse. A deliberate defect retaining the old
length after an error must fail that theorem.

This would verify the actual example's source against its publication model,
not arbitrary applications. A real I/O sink, transport or authorization layer
would need additional verified code or explicitly trusted specifications.
Rust ownership alone does not stop a caller from serializing the whole buffer.

**Decision needed:** approve that private caller and its observation/state
model, or select a deployable wrapper/API and its exact obligations. No new
wrapper or state model is implemented by this proposal.

## Resource exhaustion: credits, worst-case bounds and request limits

Proposed accounting would charge concrete source operations, including input
inspection, table construction, copying, state transitions and retry overhead.
A request receives a finite budget; operations decrease its remaining credits
and exhaustion has specified behavior. Bounds must cover every path, including
malformed input, zero-output metadata, empty chunks, resets and repeated retries.
An amortized potential can connect cheap and expensive transitions, but it
must not allow an attacker to mint credits by choosing chunk boundaries.

For a streaming decompressor, limits should cover input accepted, total output,
window/workspace storage, auxiliary tables and computational work across all
calls of the same request. Constructor/reset work must also be charged somewhere.
A limit-triggered rejection must be distinct from claiming the format invalid.
Output-cap checks alone do not bound input validation or table-building work.

This can establish a real algorithmic protection theorem: the implementation
cannot consume more than its specified modeled resources per admitted request.
Translating abstract work to elapsed time needs a machine-cost/scheduling model.
Service availability additionally depends on admission, concurrency and rate
limits, available capacity and the environment. No finite machine can promise
unconditional availability under unlimited attacker demand.

**Decision needed:** approve the charged operations, per-request limits,
budget lifetime, exhaustion/yield behavior and any service wrapper. Numeric
deployment limits require direct human approval.

## State and deployment

Constructor establishment plus transition preservation can prove invariants
for every finite permitted call sequence. Safety does not require the caller
eventually to provide more input; progress/liveness claims must state any such
environment assumption. [Brotli B1](BROTLI_PROPOSAL.md) proposes a concrete first
stateful input/header core. It does not yet approve a full streaming decoder.

Binary/source correspondence is also a proof topic: a verified compiler or a
checked translation can support a particular bridge. Existing hashes and
byte-identical builds are provenance, not that theorem. Selecting an additional
checker or changing the trust base requires explicit human approval.

Independent specification review remains necessary to assess whether the
chosen goals capture the intended threats. Additional checked obligations do
not supply that independent review.
