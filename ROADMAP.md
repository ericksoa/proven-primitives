# Candidate primitives and security case studies

Adding a target here records interest and research. Implementation scope, APIs,
state models, dependencies, comparison references and proof approaches require
separate human approval before implementation. The approved Base64 G iteration
is complete. Current Brotli work is format/source research and the
already-approved [B1 input/header milestone](BROTLI_PROPOSAL.md).
P1, B2/R1 and C1 are approved and implemented. The B3 and B4 architecture is
approved. The first B3a workspace/meta-header slice is checked, but no
comprehensive security profile has been adopted and independent review remains
pending.

B1 is now checked as a private component; see [BROTLI_B1.md](BROTLI_B1.md).
It does not change Brotli's candidate/support status. The actual block-switch,
complete decoder, caller/resource profile and comparison/replay milestones
remain subject to the decisions in the streaming proposal.

B2's canonical prefix/block-length and three-category block-switch core is now
checked as another private component; see [BROTLI_B2.md](BROTLI_B2.md). The R1
native status replay is complete. Full grammar/output decoding and B3/B4 remain
separate. [BROTLI_B3A.md](BROTLI_B3A.md) records the checked fixed workspace and
meta-block-header slice. The remaining approved implementation path is in
[BROTLI_B3_PROPOSAL.md](BROTLI_B3_PROPOSAL.md), followed by the caller/profile
work in [BROTLI_B4_PROFILE_PROPOSAL.md](BROTLI_B4_PROFILE_PROPOSAL.md).

## Compositional verification

Treat verified callers and adapters as checked components with their own
versioned contracts and evidence. Individual primitive proofs are premises,
not an automatic system theorem. The roadmap covers format/buffer/state
compatibility; current-prefix handoff; complete result handling and stale-length
invalidation; derived functional/confidentiality contracts; cumulative memory,
expansion and work; caller-loop termination; and explicit staged error effects.

Build reusable checked lemmas for frame chaining, prefix handoff, result/error
lifting, publication state and resource algebra, while leaving every unmet
premise visible. Bind each composition to exact components, connecting code,
profile, target and trusted base, and rerun the affected proof/evidence closure
after changes. Historical compositions keep their original profile identities.

The proposed first demonstration is strict Base64 decode followed by percent
decode through a crate-private stateful caller. It proves use of the current
intermediate prefix, invalidation after errors, stage-specific buffer effects
and combined bounds. Details and required approval are in
[COMPOSITION_PROPOSAL.md](COMPOSITION_PROPOSAL.md). It does not verify arbitrary
applications or imply system-wide rollback when a later stage fails.

C1 is now implemented and checked; see [COMPOSITION_C1.md](COMPOSITION_C1.md).

## Brotli decompression

Added at the human's request on 2026-10-24. Status: candidate with checked B1,
B2, and partial B3a private components; no complete Brotli decoder or supported
public streaming implementation exists.

### Recent security evidence

[Node.js's 21 October 2026 security release](https://nodejs.org/en/blog/vulnerability/october-2026-security-releases#nodejs-brotli-decoder-out-of-bounds-write-permits-remote-code-execution-cve-2026-111497---high)
describes CVE-2026-111497: an invalid Brotli block switch was treated as a
temporary need for more input rather than a permanent format error. Repeated
streaming retries could append beyond an eight-byte internal buffer. The
reported consequences include memory corruption, crashes, memory disclosure
and possible remote code execution in applications decompressing attacker
supplied Brotli input.

The [upstream fixing commit](https://github.com/google/brotli/commit/0ed4268a4401abcb4472096340477cf4af7d1a2b),
committed on 27 February 2026,
changes decoder status handling to distinguish invalid block switches from
genuine input exhaustion. The [Envoy advisory, published 23 October](https://github.com/envoyproxy/envoy/security/advisories/GHSA-3wvj-j6qm-62mr)
also tracks CVE-2026-111497 in deployments with the Brotli decompressor enabled.
These are disclosures about those implementations; they do not establish that
every Brotli implementation or integration is vulnerable.

### Why it belongs on the list

This case connects a wrong state transition to a memory-safety failure. A
buffer-bounds proof alone is less informative than also specifying the meaning
of permanent failure, temporary input exhaustion, retained state and progress
across calls. This makes Brotli a useful test of the project's security-contract
approach beyond the current small codecs.

Approved proof goals:

- Every pending-input and output write fits its actual buffer in every reachable
  state, including after repeated calls and errors.
- An established format error cannot be mistaken for retryable input exhaustion.
- Consumed/produced counts and retained state obey explicit progress rules.
- Supported chunkings produce the same decoded bytes as the specified whole
  stream; no stale decoder memory enters returned output.
- Window references, lengths and resource limits remain bounded under malformed
  input, with termination or an explicit, justified request for more input.

### Approved implementation path and remaining evidence

The approved B3/B4 documents fix streaming scope, dictionary/window support,
caller-buffer and error semantics, resource accounting, upstream identities,
workspace layout and the quarantining caller. The disclosed failure concerns
streaming state; a one-shot decoder alone would not demonstrate that its
streaming transition invariants have been proved.

The implementation retains the relevant regression input and negative proof
controls, explains intentional differences from upstream, and will benchmark
valid, truncated, malformed and resource-limited cases as matching paths land.
Finite test agreement remains distinct from universal upstream equivalence.

Brotli's format and streaming behavior expand the proof scope substantially
beyond the current LZ4 raw-block decoder. No completion date or claim of a
verified Brotli implementation is made here.

The [security-contract assessment](SECURITY_CONTRACTS.md) records the approved
Brotli streaming obligations and distinguishes them from the current checked
per-call guarantees. [Follow-up decisions](SECURITY_PROOF_PROPOSALS.md) remain
reserved to the human before new APIs, state models or dependencies are adopted.
