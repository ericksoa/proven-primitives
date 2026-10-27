# Brotli B3c body, resource, and public-core proposal

Status: **pending direct human approval**. The approved B3 architecture fixes
the supported format, public API shape, dictionary identity, workspace ceiling,
safe bytewise algorithms and resource categories. B3b intentionally leaves
13,028 workspace bytes unassigned until a concrete B3c layout is approved.
This document proposes that exact assignment and the remaining body-level
choices. No dependent implementation may begin until the human approves one
candidate.

B3c is not B3d or B4. It does not claim arbitrary call-sequence induction,
complete supported-format refinement, source-observation equality, an adopted
security profile, independent review, or supported Brotli.

## Candidate C1: serialized body state with fixed data modules

Candidate C1 keeps all persistent decoder state in caller-owned storage and
uses the already approved API without adding a dependency, runtime, build tool,
unsafe code, heap allocation, I/O, executable recursion, proof assumption or
trusted component.

Add these source boundaries:

- `src/brotli.rs`: the public `RequestLimits`, `RequestBudget`,
  `BrotliDecoder`, `Step`, `Status`, `StreamError` and `InitError` API; resource
  accounting; and the top-level stream/body state machine.
- `src/brotli_data.rs`: crate-private immutable command, context, dictionary
  metadata and transform tables plus checked accessors and transformations.
- `src/brotli_dictionary.rs`: only the exact 122,784-byte RFC dictionary
  constant and its source/hash comment; no logic.
- `src/brotli_input.rs`: retain ownership of B1/B3a/B3b parsing and add only
  the narrow metered serialized adapters listed below.
- `src/brotli_block.rs` and `src/brotli_prefix.rs`: preserve B2 and the checked
  workspace/tree accessors. B3c calls the E2 adapter rather than reimplementing
  a block switch.

`src/lib.rs` adds `pub mod brotli`. The private B1, B2, B3a and B3b components
do not become public APIs.

### Exact public representation

The approved signatures stay unchanged. Candidate C1 fixes their private
representation as:

```rust
pub struct RequestBudget {
    limits: RequestLimits,
    input_remaining: u64,
    output_remaining: u64,
    work_remaining: u64,
    calls_remaining: u64,
    initializations_remaining: u32,
}

pub struct BrotliDecoder<'w, 'b> {
    workspace: &'w mut [u8],
    budget: &'b mut RequestBudget,
}
```

No logical parser field is retained in the Rust object outside the workspace.
`RequestBudget::new` accepts zero byte/work/call/initialization limits, validates
only `10 <= max_window_bits <= 24`, and copies the supplied limits into the five
remaining counters. A successful decoder construction or reset consumes one
initialization credit. It never replenishes any counter.

`BrotliDecoder::new` first checks that the workspace has at least
`(1 << max_window_bits) + 1,176,560` bytes. `WorkspaceTooSmall` is returned
before any budget or workspace effect. Only then does construction attempt to
consume initialization/work credit and write the canonical state.

The physical circular window is the first `1 << limits.max_window_bits` bytes.
The stream header may select fewer bits. The logical backward-history limit is
`(1 << stream_window_bits) - 16`; using a larger physical ring cannot authorize
a longer reference.

### Narrow crate-private adapter surface

`brotli_input.rs` adds these callable boundaries. The result structs contain
only `consumed`, the named status, and the listed completed value; they expose no
slice or internal workspace reference.

```rust
pub(crate) enum CoreFormatDetail {
    WindowHeader,
    MetaHeader,
    Padding,
    PrefixCode,
    ContextMap,
    BlockSwitch,
    Command,
    BlockLength,
    Distance,
    Dictionary,
    Transform,
    UnexpectedInputAfterEof,
    StateEncoding,
}
pub(crate) enum CoreFailure {
    InvalidFormat(CoreFormatDetail),
    Truncated,
    UnsupportedMode,
    ResourceLimit,
}

pub(crate) enum WindowStatus {
    NeedInput,
    Complete { window_bits: u8 },
    Failed(CoreFailure),
}
pub(crate) struct WindowStep { consumed: usize, status: WindowStatus }

pub(crate) struct MetaHeaderValue {
    is_last: bool,
    is_empty: bool,
    is_uncompressed: bool,
    is_metadata: bool,
    length: u32,
}
pub(crate) enum MetaStatus {
    NeedInput,
    Complete(MetaHeaderValue),
    Failed(CoreFailure),
}
pub(crate) struct MetaStep { consumed: usize, status: MetaStatus }

pub(crate) enum CompressedStatus {
    NeedInput,
    Complete,
    Failed(CoreFailure),
}
pub(crate) struct CompressedStep { consumed: usize, status: CompressedStatus }

pub(crate) enum BodySymbolStatus {
    NeedInput,
    Symbol(u16),
    Failed(CoreFailure),
}
pub(crate) struct BodySymbolStep { consumed: usize, status: BodySymbolStatus }

pub(crate) enum BodySwitchStatus {
    NeedInput,
    Complete { kind: u8, block_type: u16, block_length: u32 },
    Failed(CoreFailure),
}
pub(crate) struct BodySwitchStep { consumed: usize, status: BodySwitchStatus }

pub(crate) fn initialize_serialized_b3c(
    workspace: &mut [u8], window_bytes: u32,
) -> Result<(), WorkspaceError>;

pub(crate) fn advance_serialized_window_header(
    workspace: &mut [u8], window_bytes: u32,
    budget: &mut RequestBudget, input: &[u8], end_of_input: bool,
) -> WindowStep;

pub(crate) fn advance_serialized_meta_header(
    workspace: &mut [u8], window_bytes: u32,
    budget: &mut RequestBudget, input: &[u8], end_of_input: bool,
) -> MetaStep;

pub(crate) fn start_serialized_compressed_header(
    workspace: &mut [u8], window_bytes: u32,
    budget: &mut RequestBudget,
) -> Result<(), CoreFailure>;

pub(crate) fn advance_serialized_compressed_header(
    workspace: &mut [u8], window_bytes: u32,
    budget: &mut RequestBudget, input: &[u8], end_of_input: bool,
) -> CompressedStep;

pub(crate) fn advance_serialized_body_symbol(
    workspace: &mut [u8], window_bytes: u32,
    budget: &mut RequestBudget, region: TreeRegion, tree: u16,
    alphabet_limit: u16, input: &[u8], end_of_input: bool,
) -> BodySymbolStep;

pub(crate) fn advance_serialized_body_block_switch(
    workspace: &mut [u8], window_bytes: u32,
    budget: &mut RequestBudget, kind: u8,
    input: &[u8], end_of_input: bool,
) -> BodySwitchStep;
```

The block-switch adapter owns type-symbol and block-length parsing, invokes
`advance_b3b_switch`, and is the checked actual body caller for all three kinds.
If the serialized remaining count is zero while the declared type count is one,
it reaches E2 without reading a prefix field and returns a permanent failure.
No B3c caller may translate that result to `NeedInput`.

Each metered adapter either reserves its exact next-action work before mutation
or executes one fixed-cost source action. The existing unmetered component roots
remain checked and unchanged; new refinement roots connect each metered adapter
to them.

## Exact reserved-workspace assignment

All offsets below are relative to the approved B3b reserved-state start at
fixed-scratch offset **1,163,532**. Multi-byte values are little endian. The
layout consumes the existing 13,028 bytes exactly and does not increase the
workspace requirement.

| Relative offset | Bytes | B3c region |
|---:|---:|---|
| 0 | 128 | serialized B3c scalar state |
| 128 | 520 | distance extra-bit widths |
| 648 | 2,080 | 520 distance base offsets as `u32` |
| 2,728 | 40 | transformed dictionary-word staging |
| 2,768 | 10,260 | checked padding, never read |
| **Total** | **13,028** | existing B3b reserved region |

The distance arrays use only the initialized prefix named by the scalar state.
The dictionary staging region uses only its initialized output prefix. Reset
sets both initialized lengths to zero and does not clear either region.

### Exact 128-byte scalar image

| Offset | Bytes | Field |
|---:|---:|---|
| 0 | 1 | stream phase tag |
| 1 | 1 | terminal error family |
| 2 | 1 | terminal error detail |
| 3 | 1 | meta-block flags |
| 4 | 1 | meta-header phase tag |
| 5 | 1 | meta-header width/count |
| 6 | 1 | meta-header index |
| 7 | 1 | selected stream window bits |
| 8 | 4 | meta-header partial value |
| 12 | 4 | meta-block bytes remaining |
| 16 | 4 | physical window write index |
| 20 | 4 | logical history length |
| 24 | 8 | total produced bytes |
| 32 | 1 | previous output byte |
| 33 | 1 | second-previous output byte |
| 34 | 1 | compressed-body phase tag |
| 35 | 1 | committed-EOF flag |
| 36 | 2 | current command symbol |
| 38 | 1 | command insert-extra width |
| 39 | 1 | command copy-extra width |
| 40 | 4 | decoded insertion length |
| 44 | 4 | insertion bytes remaining |
| 48 | 4 | decoded copy length |
| 52 | 4 | copy bytes remaining |
| 56 | 1 | command distance mode |
| 57 | 1 | distance context |
| 58 | 2 | selected distance tree |
| 60 | 2 | current distance symbol |
| 62 | 1 | distance-extra width |
| 63 | 1 | dictionary transform index |
| 64 | 4 | resolved backward distance |
| 68 | 16 | four recent distances as `u32` |
| 84 | 1 | recent-distance ring cursor, modulo four |
| 85 | 1 | dictionary base-word length |
| 86 | 1 | transformed dictionary output length |
| 87 | 1 | transformed dictionary output cursor |
| 88 | 4 | dictionary word index |
| 92 | 2 | initialized distance-LUT entries |
| 94 | 1 | initialized dictionary-staging length |
| 95 | 1 | terminal-work escrow marker, value four while nonterminal |
| 96 | 32 | initialized zero padding, never read |

Construction writes the canonical B3b image and seven metadata records using
the existing 292 byte writes, then writes the 128-byte B3c scalar image once.
The B3c initial image sets the stream phase to window header, previous bytes to
zero, recent distances to `[16, 15, 11, 4]`, the recent-distance cursor to zero,
initialized lengths to zero, and the escrow marker to four. The three terminal
bytes and logical transition consume the four units already removed from the
budget; the marker need not be rewritten because terminal state never reads it.
It does not read old window, LUT, staging or padding bytes.

The stream phase tags are: `0 WindowHeader`, `1 MetaHeader`, `2 ByteAlign`,
`3 Metadata`, `4 Uncompressed`, `5 CompressedHeader`, `6 CompressedBody`,
`7 FinalPadding`, `8 Finished`, and `9 Failed`.

The body phase tags are: `0 CommandReady`, `1 SwitchType`, `2 SwitchLength`,
`3 CommandSymbol`, `4 CommandInsertExtra`, `5 CommandCopyExtra`,
`6 LiteralReady`, `7 LiteralSymbol`, `8 DistanceReady`, `9 DistanceSymbol`,
`10 DistanceExtra`, `11 CopyClassify`, `12 WindowCopy`,
`13 DictionaryBuild`, `14 DictionaryEmit`, and `15 MetaDone`.

The meta-header phase tags exactly serialize the existing B3a `Last`, `Empty`,
`Nibbles`, `Size`, `Uncompressed`, `Reserved`, `MetadataBytes`,
`MetadataSize`, and `Complete` phases. A meta failure is immediately lifted to
the top-level failed state rather than stored as another meta tag.

Terminal family tags are `0 None`, `1 InvalidFormat`, `2 Truncated`,
`3 UnsupportedMode`, and `4 ResourceLimit`. Invalid-format detail tags follow
the `CoreFormatDetail` declaration order from zero through twelve. Detail is
zero for every other family. The public mapping is exact by family and hides
only the private invalid-format detail. `StateEncoding` is proved unreachable
from a successful constructor and admitted Rust calls; it gives defensive
executable handling to a malformed internal encoding without adding a public
error variant or proof assumption.

## Exact immutable data

Candidate C1 commits literal constants derived from google/brotli v1.2.1 commit
`db24a98aed38a16de78cc05ca15cdd8dc2a0d92d`:

| Data | Exact source and SHA-256 |
|---|---|
| 704 command entries | `c/dec/prefix_inc.h`, `e1ade26b7b1e1e56b1a91af20ef93f81ef7a4ed83e0543fd6d9eb29f5c6d2983` |
| Command-table construction cross-check | `c/dec/prefix.c`, `0a31304f440f7bb2017d52b83ae35cb428cbc5ac2fc172c8eec2fea449c2f7cd` |
| Decoder transition reference | `c/dec/decode.c`, `8d7beeafed5ff9f3f00f6e528e92ad6a36059b3549356bed5a9ca3ee16938438` |
| Decoder state definition | `c/dec/state.h`, `8937c3799c177eacfaf3c0dba8da8c2558f435d6baffa2d787aec3212eaca041` |
| Decoder state initialization | `c/dec/state.c`, `66a7c3d9c01cda374d33d3693ba45d059ff00b12114a8844ee4f2519ba2af14e` |
| 2,048 literal-context bytes | `c/common/context.c`, `c9aa1acb35af38c90c4a38ba168885b649838236b2d57adb5e76d687bdbe252e` |
| Context definition | `c/common/context.h`, `2745ef910928a4acd58e1cb98128a0a228fa1812c61e69538c9d393d405bf047` |
| 122,784 dictionary bytes | decoded `c/common/dictionary_inc.h`, `20e42eb1b511c21806d4d227d07e5dd06877d8ce7b3a817f378f313653f35c70` |
| Dictionary length metadata | `c/common/dictionary.c`, `0890056e4ae595efab6bbf3bf1fd244332e2cfad3adcb9f5793ee29a8f3a18c5` |
| 121 transforms | `c/common/transform.c`, `47f229a79c3542ea57ec07145d7eaf77300a02816d95695332f9911ea19d6ab3` |
| Transform definitions | `c/common/transform.h`, `b79dd99d1dcc618c1a4284b74dd04adda099fc3f65f906924991a736e09c125c` |
| License | `LICENSE`, `3d180008e36922a4e8daec11c34c7af264fed5962d07924aea928c38e8663c94` |

RFC 7932 text fetched from the RFC Editor has SHA-256
`394abd1879e016f4eac89512c2acaf92f7b2d67feb8ab58b6b118c213be07146`.
The transform proof uses its 13-byte maximum affix expansion. A transformed
word contains at most 37 output bytes; the 40-byte staging allocation leaves
three unread padding bytes. Every committed constant is compared byte-for-byte
with a frozen test fixture from the same pinned source, and the production
constant itself is the value used by the checked specification.

The test-only reference bytes live under `tests/fixtures/brotli/reference/`:
the dictionary as its 122,784 raw bytes; command entries as 704 consecutive
eight-byte records in the field order shown by `CmdLutElement`, with `u16`
values little endian; the 2,048 raw context bytes; 32 size-bit bytes followed by
32 little-endian `u32` dictionary offsets; and the prefix/suffix bytes,
50 little-endian `u16` prefix/suffix offsets, and 121 three-byte transform
records. These fixtures are never compiled into the library or used as proof
assumptions.

## Exact body transitions

### Commands and literals

When command remaining is zero, `CommandReady` enters the generic body switch
for kind one. Otherwise it selects the command tree from the active command
block type, decodes one symbol, decrements command remaining exactly once, and
loads the six fields from the 704-entry command table. Insert and copy extra
bits are read in separate resumable phases.

Before literal emission, B3c rejects an insertion length larger than meta-block
remaining. Each literal first completes a kind-zero switch if required, then
computes its context from the two serialized previous bytes and the exact
2,048-byte context table. It selects
`literal_map[64 * literal_block_type + context]`, decodes one byte, and performs
one atomic emission. If the insert part reaches the meta-block length, the copy
part of that last command is ignored exactly as RFC 7932 requires.

### Distances and the CVE-sensitive switch

Copy lengths map to distance contexts `0, 1, 2, 3` for lengths `2, 3, 4, >4`.
An explicit distance first completes a kind-two block switch if required, then
uses `distance_map[4 * distance_block_type + context]`.

The first sixteen symbols use these fixed recent-ring index deltas and signed
value deltas:

```text
index delta: [3,2,1,0, 3,3,3,3,3,3, 2,2,2,2,2,2]
value delta: [0,0,0,0,-1,1,-2,2,-3,3,-1,1,-2,2,-3,3]
```

A nonpositive result is invalid. Later symbols use the checked 520-entry
distance LUT built from `NPOSTFIX`, `NDIRECT` and the approved normal-window
alphabet. LUT construction writes an exact initialized prefix and is charged
before each entry.

The command-distance mode byte is `0` for the command's implicit last distance,
`1` for an explicit distance symbol that must not update the recent ring, and
`2` for an explicit nonzero symbol eligible to update the ring after a valid
LZ77 copy. Explicit symbol zero selects mode one; every other explicit symbol
selects mode two.

`history_len` is always `min(total_produced, (1 << stream_window_bits) - 16)`.
A resolved distance at most `history_len` is an LZ77 reference; a larger one is
a standard static-dictionary reference. Only a successful LZ77 copy in mode two
pushes its nonzero distance into the recent ring. Implicit distance, explicit
symbol zero, and every dictionary reference leave the logical ring unchanged.
The normalized modulo-four cursor is proved equivalent to the RFC/native
recent-distance behavior.

### Atomic output and overlapping LZ77

One emitted byte is the atomic backpressure unit. Before it, the decoder
requires one output slot, one output credit, and the exact work for its source
read, caller-output write, window write and state updates. It then writes the
same byte to `output[produced]` and the physical ring at `window_position`,
advances the position modulo the physical power-of-two window, updates the two
previous bytes, total output, history and meta-block remaining, and preserves
the output suffix.

An LZ77 byte reads
`(window_position - distance) mod physical_window_bytes` immediately before the
write. Bytewise repetition therefore reads bytes produced earlier in the same
copy and implements overlap without `unsafe` code or a speculative fast path.
Zero and non-dictionary distances beyond logical history are rejected.

### Static dictionary

Dictionary copy length must be 4 through 24. Candidate C1 computes:

```text
word_id      = distance - history_len - 1
word_index   = word_id & ((1 << size_bits[length]) - 1)
transform_id = word_id >> size_bits[length]
source       = offsets[length] + word_index * length
```

It rejects a zero size-bit entry, transform above 120, or any checked range
failure. It precomputes the complete transformed result into the 40-byte
staging region only after charging the exact dictionary reads, transform work
and staging writes. It verifies the transformed length does not exceed the
remaining meta-block length before the first staging write, then emits the
initialized staging prefix through the same atomic output/window action.

RFC 7932 permits omission transforms to produce an empty string. Candidate C1
accepts a valid zero-length transformed dictionary result and continues with
the next command under the work/call budgets. The pinned native decoder rejects
a subset when the resolved distance is at most 120; this is recorded as an
intentional RFC/native difference rather than hidden in comparison counts.

### Metadata, uncompressed data and final padding

Metadata and uncompressed meta-blocks first consume exactly the pending bits to
the next byte boundary and require every discarded bit to be zero. Metadata
bytes consume input/work credits but never change output, history or previous
bytes. Uncompressed bytes use the same atomic emission path as literals.

At a final meta-block, final padding consumes only the remaining bits of the
current byte and requires zero. The raw core then returns `Finished` and leaves
any complete trailing input byte unconsumed. Rejecting that remainder is the
approved B4 one-message caller policy.

## EOF, output and terminal priority

`end_of_input` becomes committed only when the complete supplied slice has been
consumed. Before that point, `NeedOutput` leaves the caller responsible for
resupplying the unconsumed suffix with the intended final flag. Once committed,
later calls may provide only empty input; any still-required field or byte is
terminal `Truncated` and nonempty replacement input is `InvalidFormat`.

`NeedInput` means the supplied input was fully consumed, EOF is not committed,
and the serialized state remains a viable prefix. `NeedOutput` means the next
justified action is an emission and the supplied output has no remaining slot.
It never stands for malformed input or exhausted request credit.

Every public failure and `Finished` state is sticky and consumes/produces zero
on later `step` calls. `reset` is the only recovery operation.

For a nonterminal call, `Step.consumed` and `Step.produced` describe only that
call. `output[..produced]` is provisional even when `status` is `Failed`; the
suffix from `produced` onward is preserved. Earlier calls' prefixes and window
effects are not rolled back by a later error.

### Explicit terminal-call policy

The general B3 text both charges every `step` entry and requires terminal states
to return the same result forever. Candidate C1 resolves that conflict as
follows:

1. A nonterminal `step` must debit one call credit before any parser action.
2. If no call credit remains, it uses the reserved terminal-work escrow to
   enter sticky `ResourceLimit` without consuming input or producing output.
3. A decoder already in `Finished` or `Failed` returns that exact stored status
   before consulting the call counter. This preserves terminal identity.
4. The raw-core cumulative theorem ends at its first terminal result. B4 proves
   its caller never invokes the core again until an explicitly charged reset.

Thus hostile direct callers can still spend constant host work by repeatedly
calling a terminal raw core; B3c does not claim service availability for an
unbounded external invocation sequence.

## Exact resource policy

Successful construction or reset precharges **425 work units**: 292 existing
B3b initialization byte writes, 128 B3c scalar writes, one logical reset
transition, and four escrowed units for a future `ResourceLimit` transition
(phase byte, error family, error detail, and logical transition). If the
initialization or work credit is unavailable, the operation returns
`InitError::ResourceLimit`, consumes the attempted initialization credit when
one existed, and leaves workspace unchanged. Unused escrow is never refunded,
including on reset or drop.

For parsing, the ledger charges the already approved units:

- accepted input bytes;
- provisional output bytes;
- each bit inspected and prefix/tree/table/context/dictionary/window cell read;
- each workspace, window and caller-output byte write;
- each logical state transition; and
- calls and initialization/reset attempts in their separate counters.

Multi-cell B3a/B3b operations expose a proved exact next-work formula. B3c
reserves that complete amount before the first write. The existing MTF and
coverage formulas remain unchanged. Single-byte emissions reserve their full
read/write/update amount before reading the source byte. Failure to reserve
enters `ResourceLimit` through escrow before the unpaid action.

Input is offered to parser helpers only up to `input_remaining`; actual consumed
bytes are then debited. If a helper needs another byte while the caller supplied
one beyond the budget-limited prefix, the result is terminal `ResourceLimit`,
not `NeedInput`. Output credit exhaustion is likewise `ResourceLimit`; an empty
caller output with remaining output credit is `NeedOutput`.

All arithmetic is checked. B3c proves per-call termination and that charged
actions through the first terminal result cannot exceed the supplied counters.
B3d still owes arbitrary permitted call-sequence induction and B4 still owes
the caller-loop and deployment assumptions.

## Proof roots and deliberate-defect controls

B3c must add root-checked contracts for:

- exact region layout, canonical initialization and initialized-read authority;
- public constructor, step, reset, status and buffer effects;
- executable refinement of command, context, distance, LZ77, dictionary,
  metadata, uncompressed and padding transitions;
- exact B2 state restoration/call/snapshot in the real body path;
- provisional output independence from old workspace and output suffix bytes;
- output/window equality, overlapping-copy induction and history bounds;
- exact resource debits, escrow use and absence of credit replenishment; and
- unchanged B1/B2/B3a/B3b contracts as premises, not copied assumptions.

At minimum, unchanged-specification controls corrupt:

1. a B3c region boundary;
2. a scalar tag or little-endian field;
3. the `[16,15,11,4]` initial distance ring;
4. the real body caller so B2 permanent failure becomes `NeedInput`;
5. command remaining so a suspended command decrements twice;
6. a command-table offset or extra-bit width;
7. literal context row stride or previous-byte order;
8. a literal tree index to read an uninitialized tree;
9. copy-length context selection;
10. a recent-distance index or signed delta;
11. distance-LUT postfix/offset arithmetic;
12. zero or beyond-history LZ77 acceptance;
13. overlap copying from a stale pre-copy snapshot;
14. a dictionary word/transform range guard;
15. dictionary source offset or transform operation;
16. dictionary staging initialization or meta-length bound;
17. an incorrect dictionary update to the recent-distance ring;
18. metadata changing history or output;
19. uncompressed input bypassing output/window accounting;
20. nonzero byte-alignment or final-padding acceptance;
21. EOF commitment before the supplied final slice is consumed;
22. `NeedOutput` masking a permanent or resource error;
23. an output/window write before resource precharge;
24. reset replenishing a counter or reading stale state;
25. publication of the output suffix beyond `produced`; and
26. replacement of a sticky terminal result after call-credit exhaustion;
27. rejection of a valid zero-length dictionary transform; and
28. execution of a last command's copy after its insert exactly reaches MLEN.

Compile errors, mutation-anchor failures, resource limits and checker failures
are not semantic rejections.

## Exact comparison fixtures and boundary

Use the already approved native harness, compiler, flags and v1.2.1 source
closure. Do not add an encoder, FFI path, package or network-dependent test.
Copy only the named fixture bytes from the pinned upstream commit and retain
their MIT attribution.

| Fixture pair | Compressed bytes / SHA-256 | Expected bytes / SHA-256 | Purpose |
|---|---|---|---|
| `empty` | 1 / `67586e98fad27da0b9968bc039a1ef34c939b9b8e523a8bef89d478608c5ecf6` | 0 / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | final-empty stream |
| `x` | 5 / `cd094a625b695542a1d37b3a11ea849d8db9584a2f9df4e60cf6158bb39bbf61` | 1 / `4b68ab3847feda7d6c62c1fbcbeebfa35eab7351ed5e78f4ddadea5df64b8015` | minimal output |
| `xyzzy` | 9 / `c3f042a6be42887f842324d0e39dabd0d873e1676cd3dd2d7e2824242b318f14` | 5 / `7609128715518308672067aab169e24944ead24e3d732aab8a8f0b7013a65564` | short literal stream |
| `10x10y` | 12 / `d666afc0f6c35d8d7796175aa9a68f16ba59afedee946d4bce9167f6c86e0b84` | 20 / `41bd4c895e9fb36d74bc97db5092872a24267e3b0455ff6152b0d262faa00d49` | short overlap/copy |
| `64x` | 10 / `f0273c38c6a55c1d9ccb047da04bacdc4bb07acc44ff83871e6b3490dfc2c313` | 64 / `be4d3ed1fc5f5cfa00735b28605a975f3293fa235d23abb1d9dea380fba0fb87` | repeated-byte overlap |
| `quickfox_repeated` | 58 / `f732c7cfd6e33481e99352ed901b90647a6177dc3e34f5d1de1658c24e2d6e5a` | 176,128 / `254fdc641d1a65d0b1e427e4b0a1e16a96a5242adb98af71833782ba99c3dd82` | static dictionary plus long copies |
| `monkey` | 425 / `37bcdd7a42a6c5b119926d5af0f0d4e9162304592a2ded12c8fe9b06bf3908d9` | 843 / `937ad127fe0e373e0e267d11905f2bca154f40fe6fd438b6ddcce40de2ddcd99` | dictionary and mixed commands |
| `zeros` | 13 / `d1236d7fdab24209a747aa471f1bf33765b27adfd676355d4b4b310195dca49f` | 262,144 / `8a39d2abd3999ab73c34db2476849cddf303ce389b35826850f9a700589b4a90` | large expansion and output backpressure |

Two independent hand fixtures supplement those upstream pairs:

- `2c00a503` is a one-byte metadata block containing `a5`, followed by a
  final-empty meta-block, with no output.
- `0000105a03` is a one-byte uncompressed block producing `5a`, followed by a
  final-empty meta-block.

Changing the metadata padding byte to `80` and the uncompressed alignment byte
from `10` to `30` must be permanent padding errors. These fixtures and expected
native results were checked during proposal research; they remain finite tests.

Run each small fixture whole, one input byte at a time, at every byte split,
with output chunks zero, one and exact where applicable. Run large-output cases
with one-byte, boundary and sufficient output chunks. Add truncation at every
input prefix, late malformed data, exact/one-short budgets, retries, reset and
old-workspace/output variations. The Node witness must reach the actual Rust
body switch, become permanently failed, consume no later retry input and never
produce an authorized complete message.

## Implementation order after approval

1. Add immutable data modules, byte-for-byte checks, license notice and data
   accessor proofs without connecting the public decoder.
2. Add the exact B3c layout, canonical initializer, budget representation and
   metered header/meta/compressed-header adapters.
3. Add command/literal/distance and actual E2 block-switch integration.
4. Add atomic LZ77/uncompressed emission and metadata/final-padding handling.
5. Add dictionary staging/transforms and exact resource settlement.
6. Add the frozen runtime/comparison matrix, full defect controls, fresh
   whole-crate proof JSON, compiled-artifact binding and scoped documentation.

Each step preserves a passing whole-crate positive control. A later step may
not weaken an earlier contract, narrow admitted inputs, add an assumption or
change the trust boundary to make verification pass.

## Alternatives not selected by Candidate C1

- **C2: extend `brotli_input.rs` directly.** This avoids the new public-core
  module boundary but adds the public API and body/resource logic to the already
  large parser module.
- **C3: compute distance formulas on demand and stream dictionary transforms
  without staging.** This uses less of the reserved region but adds resumable
  transform state and more proof branches at every output boundary.
- **C4: let call-budget exhaustion replace an existing terminal result.** This
  charges every invocation but violates the approved sticky-terminal identity
  and weakens the CVE-facing guarantee.
- **C5: reject all zero-length dictionary transforms to match a stricter native
  subset.** This simplifies progress reasoning but narrows the RFC 7932 format
  accepted by the approved B3 scope.

## Approval requested

The human may approve **Candidate C1 as written** or select a listed alternative.
C1 approval authorizes the exact modules and crate-private adapters, public
private-field representations, 13,028-byte assignment, scalar tags and reset
image, immutable data identities, terminal/call priority, four-unit terminal
escrow, 425-unit initialization charge, command/distance/LZ77/dictionary/
metadata algorithms, RFC zero-length-transform behavior, proof controls,
fixtures and implementation order above.

It does not approve B3d/B4 implementation, profile adoption, independent-review
identity, deployment defaults, new dependencies/tools/services, or a changed
proof trust boundary.
