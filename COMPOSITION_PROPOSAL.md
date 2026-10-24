# Compositional verification roadmap and first demonstration

Status: the human approved C1 exactly as written on 2026-10-24. It is implemented
and checked as described in [COMPOSITION_C1.md](COMPOSITION_C1.md). No public API
or arbitrary-application claim is authorized.

## Governing composition rule

Individually checked components do not automatically give their composition a
checked system contract. A composition is supported under security profile `V`
only when every applicable component obligation and every applicable integration
obligation in `V` is checked for the exact component sources, adapters, state,
execution model and admitted call sequences.

The composition has its own identity, support status and evidence rows. A
component proof may be reused as a premise; the compatibility and caller
obligations still need checked connections. An unresolved connection is a
coverage gap, not an inherited guarantee.

## Roadmap obligations

| Family | Required composition result |
|---|---|
| Compatibility | Each stage's produced value, format, length, initialized prefix, ownership/lifetime and state satisfy the next stage's exact requirements. Format conversions or narrowed domains are explicit checked adapters. |
| Caller wiring | Call only with the current produced prefix; handle every result; invalidate stale lengths on all errors; preserve buffer/state invariants and exclusivity; obey every permitted call/reset/retry sequence. |
| Derived function | Define the complete mathematical transformation and prove actual connecting code refines it, including stage-specific failures and capacity behavior. |
| Derived confidentiality | Define authorized observations at each boundary. Prove final published bytes exclude unrelated prior storage. Identify whether intermediate buffers, lengths/statuses and provisional output are permitted disclosures. |
| Resources and liveness | Compose expansion formulas, working storage and abstract work; charge caller transitions/retries/initialization and prove caller loops terminate or have explicit environment/progress assumptions. Individual termination alone is insufficient. |
| Error semantics | State which buffers are preserved by the failing call and what earlier successful effects remain. A downstream unchanged-on-error contract does not roll back an already populated intermediate buffer. |
| Reusable proof rules | Checked lemmas may combine frame properties, prefix validity, staged results, error precedence and cost algebra. Every instantiation must expose unsatisfied premises; no lemma may manufacture applicability or hide a gap. |
| Versioned evidence | Bind the composition to exact component/adapter sources, contract revisions, profile/applicability, target/toolchain/options, locked dependencies, build artifact and trusted assumptions. |

## C1: proposed first real caller

Add a crate-private `composition_demo` module to the existing Cargo library.
It is verified with the whole crate and compiled from that same annotated
source. It adds no public API, dependency, executable recursion, heap
allocation, unsafe code, I/O, service or trust bypass.

The caller decodes a strict standard Base64 text into caller-provided scratch,
then percent-decodes **only the returned scratch prefix** into a caller-provided
destination. This is useful for systems transporting an RFC 3986 component
inside Base64 and gives us meaningful failures at either stage.

Proposed private shape:

```rust
enum ComposeError {
    Base64Invalid,
    ScratchTooSmall,
    PercentInvalid,
    OutputTooSmall,
}

struct DecodeCaller {
    published_len: Option<usize>,
}

impl DecodeCaller {
    fn new() -> Self;
    fn decode(
        &mut self,
        input: &[u8],
        scratch: &mut [u8],
        output: &mut [u8],
    ) -> Result<usize, ComposeError>;
}
```

`published_len` is cleared before processing and remains `None` on every
error. It becomes `Some(n)` only after both stages succeed. No method returns
or serializes the whole allocation. The demonstration's authorized external
view is only `output[..n]` from the current success. Scratch is a caller-owned
internal observation and is explicitly not authorized for publication.

### Exact derived function and error order

Define:

```text
composed(input) = percent::decoded(base64::decoded(input))
```

with option composition and the existing strict grammars. The executable
result must satisfy, over arbitrary admitted bytes, input length, capacities
and initialized scratch/output contents:

1. Invalid Base64 returns `Base64Invalid`; both buffers keep their old values;
   no published length exists. This wins over insufficient scratch capacity.
2. Valid Base64 whose decoded intermediate exceeds scratch returns
   `ScratchTooSmall`; both buffers remain unchanged; no published length exists.
3. Successful Base64 followed by invalid percent text returns `PercentInvalid`.
   Output remains unchanged. Scratch contains exactly the Base64-decoded prefix
   with its old suffix preserved. That earlier success is not rolled back.
4. Successful Base64 and valid percent text whose result exceeds output returns
   `OutputTooSmall`. Output remains unchanged; scratch retains the exact
   intermediate as above; no published length exists.
5. Otherwise `Ok(n)` and `published_len == Some(n)`; the current output prefix
   equals the composed mathematical result and its suffix is preserved.
   Scratch contains the exact intermediate prefix and preserves its suffix.

The proof must establish that percent decoding receives `&scratch[..middle_n]`,
where `middle_n` is the current successful Base64 result. It may not receive
the complete capacity, a previous length, or a guessed formula.

### Compatibility and ownership premises

- Both stages accept arbitrary byte slices, so the Base64 result needs no
  UTF-8 conversion. The percent stage's literal-plus and `%HH` rules are the
  intended downstream format and are part of this composition contract.
- The intermediate prefix is initialized by the first checked function and
  borrowed immutably for the second. Rust's valid-reference, lifetime and
  exclusive-mutable-access assumptions remain in trusted Rust semantics.
- Scratch and output must be disjoint mutable slices under safe Rust. Input
  aliasing rules remain those admitted by safe calls. No unsafe/FFI alias is
  covered.
- Empty input composes to empty output. All malformed/capacity combinations
  have the stage order above; there is no hidden valid-input precondition.

### Confidentiality and system effects

The checked final prefix depends only on current input. Old scratch/output
contents cannot enter it. Errors authorize no output prefix, and stale lengths
are invalidated. Intermediate scratch bytes after a successful first stage are
an explicit permitted internal disclosure, even if the second stage fails.
Neither buffer suffix is sanitized. The application must keep scratch internal
and expose only the current final prefix.

This is a value-confidentiality result. The current codecs' branches/table
addresses depend on current input; C1 does not establish constant-time handling
of secret current input or a compiler/hardware side-channel theorem.

### Combined memory, expansion, work and termination

Let `I` be input length, `S` the successful Base64 intermediate length and
`O` the successful final length. Existing checked length results give
`S <= 3 * (I / 4)` for accepted Base64 and `O <= S` for accepted percent text.
Writes are bounded by caller capacities. The adapter itself allocates only
fixed local state; caller storage is `scratch.len() + output.len()`. Concrete
stack bytes, allocator/OS memory and process-wide concurrency remain outside
this theorem.

C1 proposes adding proof-only work ledgers to the existing Base64 and percent
decoders, without changing runtime code/signatures. Charge one unit for each
modeled input-byte inspection, output-byte read/write and parser/loop transition.
Counters use mathematical naturals and cover malformed, small-output and
successful paths. The proposed deliberately conservative contracts are:

- Base64 decode work `<= 8I + 4S + 32` when `S` is produced, and
  `<= 8I + 32` before any successful writer result.
- Percent decode work `<= 8S + 4O + 16` when `O` is produced, and
  `<= 8S + 16` before any successful writer result.
- The two-call adapter charges an additional eight transitions, so successful
  composition work is `<= 8I + 12S + 4O + 56`, and therefore
  `<= 21I + 56` using the checked expansion bounds. Error paths use the
  corresponding completed-stage bound and are no larger.

These units are source operations, not cycles. The proof must connect every
charged loop/state step to actual source; if the proposed constants fail, stop
for a reviewed contract change rather than weakening the accounting silently.
The caller has no loop and makes at most two terminating calls, so its
termination follows from the checked callees plus straight-line control flow.
This says nothing about an arbitrary surrounding retry loop or service availability.

### Required C1 checks and deliberate defects

Actual root checking must cover the caller state machine, derived result/error
contract, both frame effects, confidentiality of the final prefix, expansion,
work algebra and termination. Runtime cases exercise standard/empty/binary
vectors; each malformed stage; exact/small capacities; arbitrary old buffers;
scratch suffixes; repeated success/error/success calls; and every stale-length
transition. Tests supplement proofs.

After an unchanged passing positive control, each mutation must produce a real
proof rejection against frozen specifications:

1. Pass all of scratch rather than `scratch[..middle_n]`.
2. Retain the previous published length on a Base64 error.
3. Retain the previous published length on a percent/small-output error.
4. Publish `scratch[..middle_n]` or the whole output allocation.
5. Map a Base64 invalid result to `ScratchTooSmall`, breaking stage semantics.
6. Omit one stage's work from the combined counter.
7. Claim output rollback includes scratch after a downstream failure.

Tool/type errors do not count as proof rejection. Each control targets actual
implemented wiring and stays distinct from finite runtime regressions.

## Reusable composition proofs

Proposed checked helpers in a private `composition` proof module:

- `written` frame chaining and disjoint-buffer preservation.
- Success-prefix handoff: a current checked `Ok(n)` produces exactly the
  initialized slice admitted by the next stage.
- Result lifting that preserves stage identity, error priority and frame effects.
- Publication-state induction: current success sets one authorized length;
  every error clears it; later calls cannot observe an old length.
- Sequential confidentiality: input-only stage results and correct prefix
  handoff imply input-only final authorized bytes, while explicitly listing
  permitted intermediate observations.
- Expansion/cost algebra over checked component bounds and finite caller steps.

These are ordinary Verus lemmas under `--no-cheating`, not an unchecked contract
language or proof plugin. Each lemma exposes its premises. A missing premise,
unsupported format conversion, unproved caller loop or unmatched error effect
remains an unresolved integration obligation in the profile coverage matrix.

## Versioned assurance and invalidation

A composition manifest binds exact component executable/specification hashes,
the adapter/caller source, reusable-lemma source, profile and applicability
digest, verifier/version/options, Rust/LLVM/erasure versions, locked dependencies,
target/features/flags, runtime/control evidence and trusted assumptions.

Rechecking rules:

- Any component contract/domain/format/error/frame/resource change invalidates
  compatibility, derived and caller proofs that cite it.
- Any executable component change requires component reverification and a new
  release binding. Even with an unchanged contract, the exact-source release
  gate and defect/runtime evidence rerun; logically contract-parametric
  composition lemmas may remain reusable after their premises are re-established.
- Any adapter, caller state, observation/publication or reusable-lemma change
  rechecks the whole composition proof and wiring controls.
- A profile/applicability change recomputes coverage; new applicable obligations
  block support until checked. Historical composition releases retain their
  original profile identity and receive a visible newer-gap assessment.
- Target/compiler/erasure/trusted-base changes require a new build/provenance
  binding and whatever proof reruns the approved execution model requires.

C1 remains a demonstration of this exact caller. It does not verify arbitrary
applications, transports, authorization logic or retry loops. Independent
review must assess its format interpretation, applicability and disclosure
policy. The source-to-binary boundary remains trusted as documented. A checked
composition theorem establishes only its stated contract under those assumptions.

## Approval requested

Approval of C1 authorizes the crate-private caller/state shape, exact stage
order/error/effect contract, proof-only Base64/percent work ledgers, reusable
private composition lemmas, tests and seven controls above. It does not approve
a public API, full security-profile adoption, arbitrary caller verification,
new dependencies/tools, a new verifier, or any source/compiler/hardware
side-channel claim.
