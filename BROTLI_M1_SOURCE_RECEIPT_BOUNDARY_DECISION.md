# M1 source-operation receipt boundary: human decision required

Status: **The human explicitly approved Approach R as written on 2026-11-17.**
Approach S remains unselected. The subsequently completed named M1
source-receipt scope and exact gate evidence are recorded in
`BROTLI_M1_SOURCE_RECEIPTS_CHECKPOINT.md` and
`evidence/brotli-b3c-m1-source-receipts.json`. The problem statement below
records the boundary at proposal time.

At proposal time, M1 remained incomplete. This proposal preserves M1's exact-work requirement;
accepting the current modular checkpoint would not establish that requirement.

## The missing connection

The source counters within individual helpers and the accumulated caller ledgers
are checked. Some helper contracts expose only their functional result or byte
frame. Their internal counters are not available after a call, so a caller that
adds the helper's cost formula has established a modeled call ledger, rather
than transferred that invocation's checked operation count. Reproving the same
formula or passing more runtime tests does not supply the missing connection.

The problem includes nested helpers. Changing the two outer installers alone
would leave the same gap in symbol probes, MTF moves and saved-state validation.
K6 explicitly excludes a new cross-module proof API, and K1/K7/K8 approve only
their named contracts and visibility. The existing approvals do not authorize
this new proof boundary.

## Exact common scope of either approach

Permit invocation-specific, proof-only operation-count receipts throughout the
existing M1 compressed-header helper graph in `src/brotli_input.rs` and
`src/brotli_prefix.rs`. This includes read/parse, saved-state load and validation,
queue/descriptor/span storage, tree construction and installation, context-map
and group/terminal handoffs. Include their existing direct callers and tests
only to propagate or discard those receipts while preserving ordinary results.
No other module's API is proposed for change. `RequestBudget` remains unchanged
and remains owned by the existing B3c adapter.

The frozen source defining this propagation scope is:

- `src/brotli_input.rs`: SHA-256 `f1a37362e128944c9c0ca49f00f30c172270677140e60027d3d655c46d831eef`.
- `src/brotli_prefix.rs`: SHA-256 `112d237139f6df4b6f3975b75c50543639b894fc733ddb024b6842471c265e03`.

Include fixed framed accessors when their invocation costs contribute to the
M1 total; do not silently treat a frame as a source-count receipt. Pure address
arithmetic and ordinary scalar reads retain their existing zero-unit policy.
Any required helper/module outside this frozen graph, extra mathematical
visibility, new unit classification or unapproved representation returns to the
human before implementation.

Concrete prefix edges that the closure audit must cover include:

- `install_simple_tree` calling `simple_record_exec`;
- `install_builder_canonical_tree` and its first-error and success paths;
- `inverse_mtf_context_map` calling `mtf_move_rank`;
- `decode_block_length` calling `block_length_range`;
- the existing returned-work guarantee of `check_context_tree_coverage`.

The input closure must cover the existing bit/variable-integer/code-description
readers, saved symbol/auxiliary loaders and validation helpers, descriptor and
queue stores, pending-span drains, start/reset and terminal helpers, installation
wrappers, and block/context/group execution and planning owners. Existing
`installed_symbol_full_step` cost witnesses may be reused where they already
provide the required checked handoff. Do not replace an adequate existing proof
with another modeled constant.

Each receipt must be constructed from the reached source counter or checked
source-event trace on **every return**, including partial input and errors. A
receipt must never be assigned from the planner's reservation or a duplicate
formula merely to make them equal. Prove the connection through nested helper
calls before claiming closure. A source-bound inventory must name every
composite cost edge and either its checked receipt/theorem or its explicit
primitive unit rule. Unresolved edges keep M1 incomplete.

Open exactly the existing derived prefix definition
`m1_canonical_nonzero_index_sum` as `pub(crate) open spec`, preserving its body
and termination argument. Prove equality with input's existing
`canonical_plan_index_sum`. No other mathematical visibility opening is included.
Use the existing K1-open definitions for inline canonical first-error receipt
contracts; retain the existing private scan model unchanged.

Preserve all existing unit definitions and early-exit charges. Prefix installer
receipts exclude caller-owned metadata writes and transitions. The input owner
charges its metadata `4` and successful-install transition `1` at their existing
actions. Deferred terminal `5` stays with the owner that performs it. Preserve
the K6 singleton total `7` and other approved formulas, workspace, W1 interface,
B3c budget ownership, 5,696-action caps, 798/8,192 proof bounds, 425-unit reset,
F2 fixtures, dependencies and pinned toolchain.

Preserve executable algorithms, reads/writes and guard/error order, ordinary
arguments, admitted inputs, all original requirements and guarantees, safe Rust,
and the proof trust boundary. Do not add assumptions, axioms, unchecked bodies,
stronger caller requirements, persistent counters, new resource policy, public
Brotli API changes, or supported-decoder claims.

## Approach R: explicit internal proof-receipt return pairs

Change each affected private helper's return representation from its existing
ordinary result `T` to `(T, Ghost<nat>)`. The ordinary result remains the first
component with all previous guarantees; the second carries the actual checked
operation count. Update existing callers and tests to destructure the pair and
prove the receipt equals the already-reserved work.

This explicitly authorizes the corresponding **private compiled Rust return-type
and caller changes** within the common scope. `Ghost` is a zero-sized proof
marker after erasure, but the tuple's Rust type still changes. Do not describe
this approach as preserving every ordinary private signature. The public Brotli
and W1 interfaces and their ordinary behavior remain unchanged. No new module,
runtime service, dependency or runtime counter is authorized.

This uses the existing return/ghost representation, with additional internal
call-site changes. Verify the compiled representation and runtime behavior;
record the private signature changes explicitly.

## Approach S: sidecar ghost outputs through the pinned annotation rewrite

Use the pinned existing `verus_spec(with ... -> Ghost(...))` annotation rewrite
for proof-only output receipts, rather than inserting an explicit tuple into
the ordinary Rust return type. It must retain the original ordinary compiled
signatures and call representations throughout the common scope.

This explicitly authorizes the annotation/rewrite changes needed to express
those sidecar proof outputs, including a bounded compatibility investigation
using the existing pinned toolchain. No new dependency, tool, runtime interface
or alternate receipt carrier is authorized. If the existing `verus!` sources
cannot use this approach while preserving the ordinary interfaces, stop the
dependent work and return the exact compatibility evidence for human review;
do not switch to Approach R or another design without approval.

Read-only inspection confirms the pinned macro source supports sidecar ghost
I/O and preserves the original input item in its ordinary erasure path. That
inspection is **not** a completed integration or erasure check for this code.
This approach preserves internal compiled signatures but requires validating a
different annotation path for the current sources.

## Required completion evidence after selection

Whichever approach the human selects, prove source-counter/receipt equality at
every relevant helper exit, receipt propagation through every composite edge,
complete planning and execution agreement, exact reservation/debit and byte
frames. Preserve all existing models and guarantees. Check the selected erasure
and interface promises, run exact-source whole verification with `--no-cheating`,
runtime and exact/short-credit comparisons, then unchanged-specification
source-read/write/transition/receipt/reservation defect controls after the
unchanged whole positive. Retain failures without classifying them as proofs.

This decision does not approve B3d/B4, an independent specification review, a
release, or a declaration that Brotli as a whole is mathematically safe.
