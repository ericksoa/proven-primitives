//! Private canonical prefix-code foundation for Brotli B2.
//!
//! The implementation deliberately uses bounded straight-line scans instead
//! of speculative lookup tables. It validates the complete 15-bit code space,
//! constructs RFC-style canonical codes and resolves only exact code/length
//! pairs. Full stream code-length decoding remains a later integration step.

#![allow(dead_code)]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_is_distributive_add_other_way};

verus! {

pub(crate) const MAX_SYMBOLS: usize = 258;
pub(crate) const MAX_BITS: u8 = 15;
const CODE_SPACE: u32 = 1 << 15;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PrefixError {
    EmptyAlphabet,
    TooManySymbols,
    InvalidCodeLength,
    DegenerateAlphabet,
    Oversubscribed,
    Incomplete,
    InvalidBlockLengthSymbol,
    InvalidBlockLengthSuffix,
    BlockLengthOverflow,
}

pub(crate) const BLOCK_LENGTH_OFFSETS: [u32; 26] = [
    1, 5, 9, 13, 17, 25, 33, 41, 49, 65, 81, 97, 113, 145, 177, 209, 241, 305,
    369, 497, 753, 1265, 2289, 4337, 8433, 16625,
];
pub(crate) const BLOCK_LENGTH_EXTRA_BITS: [u8; 26] = [
    2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 8, 9, 10, 11,
    12, 13, 24,
];

pub(crate) open spec fn block_length_value(symbol: u8, suffix: u32) -> nat {
    BLOCK_LENGTH_OFFSETS@[symbol as int] as nat + suffix as nat
}

fn block_length_range(symbol: u8) -> (r: (u32, u8))
    requires symbol < 26,
    ensures r.0 == BLOCK_LENGTH_OFFSETS@[symbol as int],
        r.1 == BLOCK_LENGTH_EXTRA_BITS@[symbol as int],
        1 <= r.0 <= 16625, 2 <= r.1 <= 24,
{
    (BLOCK_LENGTH_OFFSETS[symbol as usize], BLOCK_LENGTH_EXTRA_BITS[symbol as usize])
}

pub(crate) fn decode_block_length(symbol: u8, suffix: u32) -> (r: Result<u32, PrefixError>)
    ensures r.is_ok() ==> {
        &&& symbol < 26
        &&& suffix < (1u32 << BLOCK_LENGTH_EXTRA_BITS@[symbol as int])
        &&& r.unwrap() as nat == block_length_value(symbol, suffix)
        &&& r.unwrap() > 0
    },
{
    if symbol >= 26 {
        return Err(PrefixError::InvalidBlockLengthSymbol);
    }
    let (offset, width) = block_length_range(symbol);
    if suffix >= (1u32 << width) {
        return Err(PrefixError::InvalidBlockLengthSuffix);
    }
    match offset.checked_add(suffix) {
        Some(value) => Ok(value),
        None => Err(PrefixError::BlockLengthOverflow),
    }
}

spec fn code_weight(length: u8) -> nat {
    if length == 1 { 16_384 }
    else if length == 2 { 8_192 }
    else if length == 3 { 4_096 }
    else if length == 4 { 2_048 }
    else if length == 5 { 1_024 }
    else if length == 6 { 512 }
    else if length == 7 { 256 }
    else if length == 8 { 128 }
    else if length == 9 { 64 }
    else if length == 10 { 32 }
    else if length == 11 { 16 }
    else if length == 12 { 8 }
    else if length == 13 { 4 }
    else if length == 14 { 2 }
    else if length == 15 { 1 }
    else { 0 }
}

spec fn used_space(lengths: Seq<u8>) -> nat
    decreases lengths.len(),
{
    if lengths.len() == 0 {
        0
    } else {
        code_weight(lengths[0]) + used_space(lengths.skip(1))
    }
}

spec fn nonzero_count(lengths: Seq<u8>) -> nat
    decreases lengths.len(),
{
    if lengths.len() == 0 {
        0
    } else {
        (if lengths[0] == 0 { 0nat } else { 1nat }) + nonzero_count(lengths.skip(1))
    }
}

spec fn count_length(lengths: Seq<u8>, length: u8) -> nat
    decreases lengths.len(),
{
    if lengths.len() == 0 {
        0
    } else {
        (if lengths[0] == length { 1nat } else { 0nat })
            + count_length(lengths.skip(1), length)
    }
}

spec fn first_code(lengths: Seq<u8>, length: nat) -> nat
    decreases length,
{
    if length <= 1 {
        0
    } else {
        2 * (first_code(lengths, (length - 1) as nat)
            + count_length(lengths, (length - 1) as u8))
    }
}

spec fn canonical_code(lengths: Seq<u8>, symbol: int) -> nat {
    let length = lengths[symbol];
    first_code(lengths, length as nat)
        + count_length(lengths.take(symbol), length)
}

spec fn valid_lengths(lengths: Seq<u8>) -> bool {
    &&& 1 <= lengths.len() <= MAX_SYMBOLS
    &&& forall|i: int| 0 <= i < lengths.len() ==> lengths[i] <= MAX_BITS
    &&& nonzero_count(lengths) >= 2
    &&& used_space(lengths) == CODE_SPACE
}

proof fn used_space_step(lengths: Seq<u8>, i: int)
    requires 0 <= i < lengths.len(),
    ensures used_space(lengths.take(i + 1))
        == used_space(lengths.take(i)) + code_weight(lengths[i]),
{
    assert(lengths.take(i + 1) =~= lengths.take(i) + seq![lengths[i]]);
    lemma_used_space_concat(lengths.take(i), seq![lengths[i]]);
    reveal_with_fuel(used_space, 2);
}

proof fn lemma_used_space_concat(a: Seq<u8>, b: Seq<u8>)
    ensures used_space(a + b) == used_space(a) + used_space(b),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_used_space_concat(a.skip(1), b);
        assert((a + b).skip(1) =~= a.skip(1) + b);
    } else {
        assert(a =~= Seq::<u8>::empty());
    }
}

proof fn nonzero_step(lengths: Seq<u8>, i: int)
    requires 0 <= i < lengths.len(),
    ensures nonzero_count(lengths.take(i + 1)) == nonzero_count(lengths.take(i))
        + if lengths[i] == 0 { 0nat } else { 1nat },
{
    assert(lengths.take(i + 1) =~= lengths.take(i) + seq![lengths[i]]);
    lemma_nonzero_concat(lengths.take(i), seq![lengths[i]]);
    reveal_with_fuel(nonzero_count, 2);
}

proof fn lemma_nonzero_concat(a: Seq<u8>, b: Seq<u8>)
    ensures nonzero_count(a + b) == nonzero_count(a) + nonzero_count(b),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_nonzero_concat(a.skip(1), b);
        assert((a + b).skip(1) =~= a.skip(1) + b);
    } else {
        assert(a =~= Seq::<u8>::empty());
    }
}

proof fn count_step(lengths: Seq<u8>, i: int, length: u8)
    requires 0 <= i < lengths.len(),
    ensures count_length(lengths.take(i + 1), length)
        == count_length(lengths.take(i), length)
            + if lengths[i] == length { 1nat } else { 0nat },
{
    assert(lengths.take(i + 1) =~= lengths.take(i) + seq![lengths[i]]);
    lemma_count_concat(lengths.take(i), seq![lengths[i]], length);
    reveal_with_fuel(count_length, 2);
}

proof fn lemma_count_concat(a: Seq<u8>, b: Seq<u8>, length: u8)
    ensures count_length(a + b, length) == count_length(a, length) + count_length(b, length),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_count_concat(a.skip(1), b, length);
        assert((a + b).skip(1) =~= a.skip(1) + b);
    } else {
        assert(a =~= Seq::<u8>::empty());
    }
}

fn weight(length: u8) -> (r: u32)
    requires 1 <= length <= 15,
    ensures r as nat == code_weight(length),
{
    if length == 1 { 16_384 }
    else if length == 2 { 8_192 }
    else if length == 3 { 4_096 }
    else if length == 4 { 2_048 }
    else if length == 5 { 1_024 }
    else if length == 6 { 512 }
    else if length == 7 { 256 }
    else if length == 8 { 128 }
    else if length == 9 { 64 }
    else if length == 10 { 32 }
    else if length == 11 { 16 }
    else if length == 12 { 8 }
    else if length == 13 { 4 }
    else if length == 14 { 2 }
    else {
        proof { assert(length == 15); }
        1
    }
}

fn validate_lengths(lengths: &[u8]) -> (r: Result<(), PrefixError>)
    ensures r.is_ok() ==> valid_lengths(lengths@),
{
    if lengths.len() == 0 {
        return Err(PrefixError::EmptyAlphabet);
    }
    if lengths.len() > MAX_SYMBOLS {
        return Err(PrefixError::TooManySymbols);
    }
    let mut i: usize = 0;
    let mut space: u32 = CODE_SPACE;
    let ghost mut used: nat = 0;
    let mut nonzero: usize = 0;
    while i < lengths.len()
        invariant i <= lengths.len(), lengths.len() <= MAX_SYMBOLS,
            nonzero <= i,
            used == used_space(lengths@.take(i as int)),
            nonzero as nat == nonzero_count(lengths@.take(i as int)),
            space as nat + used == CODE_SPACE,
            forall|j: int| 0 <= j < i ==> lengths@[j] <= MAX_BITS,
        decreases lengths.len() - i,
    {
        let length = lengths[i];
        if length > MAX_BITS {
            return Err(PrefixError::InvalidCodeLength);
        }
        proof {
            used_space_step(lengths@, i as int);
            nonzero_step(lengths@, i as int);
        }
        if length != 0 {
            let amount = weight(length);
            if amount > space {
                return Err(PrefixError::Oversubscribed);
            }
            space = space - amount;
            nonzero = nonzero + 1;
            proof { used = used + code_weight(length); }
        }
        i = i + 1;
    }
    proof {
        assert(lengths@.take(i as int) =~= lengths@);
    }
    if nonzero < 2 {
        return Err(PrefixError::DegenerateAlphabet);
    }
    if space != 0 {
        return Err(PrefixError::Incomplete);
    }
    Ok(())
}

fn count_exec(lengths: &[u8], length: u8, limit: usize) -> (r: u32)
    requires limit <= lengths.len() <= MAX_SYMBOLS,
    ensures r as nat == count_length(lengths@.take(limit as int), length),
{
    let mut i: usize = 0;
    let mut count: u32 = 0;
    while i < limit
        invariant i <= limit <= lengths.len() <= MAX_SYMBOLS,
            count <= i,
            count as nat == count_length(lengths@.take(i as int), length),
        decreases limit - i,
    {
        proof { count_step(lengths@, i as int, length); }
        if lengths[i] == length {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn first_code_exec(lengths: &[u8], length: u8) -> (r: Result<u32, PrefixError>)
    requires 1 <= length <= MAX_BITS, lengths.len() <= MAX_SYMBOLS,
        forall|i: int| 0 <= i < lengths.len() ==> lengths@[i] <= MAX_BITS,
    ensures r.is_ok() ==> r.unwrap() as nat == first_code(lengths@, length as nat),
{
    let mut bits: u8 = 1;
    let mut code: u32 = 0;
    while bits < length
        invariant 1 <= bits <= length <= MAX_BITS,
            lengths.len() <= MAX_SYMBOLS,
            forall|i: int| 0 <= i < lengths.len() ==> lengths@[i] <= MAX_BITS,
            code as nat == first_code(lengths@, bits as nat),
        decreases length - bits,
    {
        let ghost old_bits = bits;
        assert(lengths.len() <= MAX_SYMBOLS);
        let count = count_exec(lengths, bits, lengths.len());
        proof {
            assert(lengths@.take(lengths.len() as int) =~= lengths@);
            assert(count as nat == count_length(lengths@, bits));
        }
        if count > u32::MAX - code {
            return Err(PrefixError::Oversubscribed);
        }
        let combined = code + count;
        if combined > u32::MAX / 2 {
            return Err(PrefixError::Oversubscribed);
        }
        code = combined * 2;
        proof {
            reveal(first_code);
            assert(first_code(lengths@, (old_bits + 1) as nat)
                == 2 * (first_code(lengths@, old_bits as nat)
                    + count_length(lengths@, old_bits)));
        }
        bits = bits + 1;
    }
    Ok(code)
}

fn canonical_code_exec(lengths: &[u8], symbol: usize) -> (r: Result<u32, PrefixError>)
    requires symbol < lengths.len() <= MAX_SYMBOLS,
        1 <= lengths@[symbol as int] <= MAX_BITS,
        forall|i: int| 0 <= i < lengths.len() ==> lengths@[i] <= MAX_BITS,
    ensures r.is_ok() ==> r.unwrap() as nat == canonical_code(lengths@, symbol as int),
{
    let length = lengths[symbol];
    let first = match first_code_exec(lengths, length) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let rank = count_exec(lengths, length, symbol);
    if rank > u32::MAX - first {
        return Err(PrefixError::Oversubscribed);
    }
    Ok(first + rank)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PrefixCode {
    pub(crate) codes: [u32; MAX_SYMBOLS],
    pub(crate) lengths: [u8; MAX_SYMBOLS],
    pub(crate) symbols: usize,
}

impl PrefixCode {
    pub(crate) closed spec fn valid_for(&self, source: Seq<u8>) -> bool {
        &&& valid_lengths(source)
        &&& self.symbols == source.len()
        &&& forall|i: int| 0 <= i < self.symbols ==> self.lengths@[i] == source[i]
        &&& forall|i: int| 0 <= i < self.symbols && source[i] != 0
            ==> self.codes@[i] as nat == canonical_code(source, i)
    }

    pub(crate) fn from_lengths(source: &[u8]) -> (r: Result<Self, PrefixError>)
        ensures r.is_ok() ==> r.unwrap().valid_for(source@),
    {
        match validate_lengths(source) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        let mut result = Self {
            codes: [0u32; MAX_SYMBOLS],
            lengths: [0u8; MAX_SYMBOLS],
            symbols: source.len(),
        };
        let mut i: usize = 0;
        while i < source.len()
            invariant i <= source.len() <= MAX_SYMBOLS,
                result.symbols == source.len(),
                valid_lengths(source@),
                forall|j: int| 0 <= j < i ==> result.lengths@[j] == source@[j],
                forall|j: int| 0 <= j < i && source@[j] != 0
                    ==> result.codes@[j] as nat == canonical_code(source@, j),
            decreases source.len() - i,
        {
            let length = source[i];
            result.lengths[i] = length;
            if length != 0 {
                result.codes[i] = match canonical_code_exec(source, i) {
                    Ok(code) => code,
                    Err(error) => return Err(error),
                };
            }
            i = i + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < result.symbols
                implies result.lengths@[j] == source@[j] by {}
            assert forall|j: int| 0 <= j < result.symbols && source@[j] != 0
                implies result.codes@[j] as nat == canonical_code(source@, j) by {}
        }
        Ok(result)
    }

    pub(crate) fn decode_exact(&self, bits: u32, width: u8) -> (r: Option<u16>)
        requires 1 <= width <= MAX_BITS, self.symbols <= MAX_SYMBOLS,
        ensures r.is_some() ==> {
            &&& (r.unwrap() as int) < self.symbols
            &&& self.lengths@[r.unwrap() as int] == width
            &&& self.codes@[r.unwrap() as int] == bits
        },
    {
        let mut i: usize = 0;
        while i < self.symbols
            invariant i <= self.symbols <= MAX_SYMBOLS,
            decreases self.symbols - i,
        {
            if self.lengths[i] == width && self.codes[i] == bits {
                return Some(i as u16);
            }
            i = i + 1;
        }
        None
    }
}

// B3 fixed caller-workspace layout. Offsets below are relative to the byte
// immediately following the power-of-two LZ77 window.
pub(crate) const FIXED_SCRATCH_BYTES: u32 = 1_176_560;
pub(crate) const LITERAL_TREES_OFFSET: u32 = 0;
pub(crate) const LITERAL_TREES_BYTES: u32 = 196_608;
pub(crate) const COMMAND_TREES_OFFSET: u32 = 196_608;
pub(crate) const COMMAND_TREES_BYTES: u32 = 540_672;
pub(crate) const DISTANCE_TREES_OFFSET: u32 = 737_280;
pub(crate) const DISTANCE_TREES_BYTES: u32 = 399_360;
pub(crate) const LITERAL_CONTEXT_MAP_OFFSET: u32 = 1_136_640;
pub(crate) const LITERAL_CONTEXT_MAP_BYTES: u32 = 16_384;
pub(crate) const DISTANCE_CONTEXT_MAP_OFFSET: u32 = 1_153_024;
pub(crate) const DISTANCE_CONTEXT_MAP_BYTES: u32 = 1_024;
pub(crate) const LITERAL_CONTEXT_MODES_OFFSET: u32 = 1_154_048;
pub(crate) const LITERAL_CONTEXT_MODES_BYTES: u32 = 256;
pub(crate) const BLOCK_TYPE_TREES_OFFSET: u32 = 1_154_304;
pub(crate) const BLOCK_TYPE_TREES_BYTES: u32 = 2_322;
pub(crate) const BLOCK_LENGTH_TREES_OFFSET: u32 = 1_156_626;
pub(crate) const BLOCK_LENGTH_TREES_BYTES: u32 = 234;
pub(crate) const BUILDER_OFFSET: u32 = 1_156_860;
pub(crate) const BUILDER_BYTES: u32 = 3_056;
pub(crate) const BUILDER_CODE_LENGTHS_OFFSET: u32 = BUILDER_OFFSET;
pub(crate) const BUILDER_CODE_LENGTHS_BYTES: u32 = 704;
pub(crate) const BUILDER_COUNTS_OFFSET: u32 = 1_157_564;
pub(crate) const BUILDER_COUNTS_BYTES: u32 = 32;
pub(crate) const BUILDER_NEXT_CODES_OFFSET: u32 = 1_157_596;
pub(crate) const BUILDER_NEXT_CODES_BYTES: u32 = 64;
pub(crate) const BUILDER_SYMBOL_CHAIN_OFFSET: u32 = 1_157_660;
pub(crate) const BUILDER_SYMBOL_CHAIN_BYTES: u32 = 1_440;
pub(crate) const TEMP_CONTEXT_TREE_OFFSET: u32 = 1_159_100;
pub(crate) const TEMP_CONTEXT_TREE_BYTES: u32 = 816;
pub(crate) const MTF_OFFSET: u32 = 1_159_916;
pub(crate) const MTF_BYTES: u32 = 260;
pub(crate) const STATE_OFFSET: u32 = 1_160_176;
pub(crate) const STATE_BYTES: u32 = 16_384;
pub(crate) const LITERAL_METADATA_OFFSET: u32 = STATE_OFFSET;
pub(crate) const LITERAL_METADATA_BYTES: u32 = 1_024;
pub(crate) const COMMAND_METADATA_OFFSET: u32 = 1_161_200;
pub(crate) const COMMAND_METADATA_BYTES: u32 = 1_024;
pub(crate) const DISTANCE_METADATA_OFFSET: u32 = 1_162_224;
pub(crate) const DISTANCE_METADATA_BYTES: u32 = 1_024;
pub(crate) const BLOCK_TYPE_METADATA_OFFSET: u32 = 1_163_248;
pub(crate) const BLOCK_TYPE_METADATA_BYTES: u32 = 12;
pub(crate) const BLOCK_LENGTH_METADATA_OFFSET: u32 = 1_163_260;
pub(crate) const BLOCK_LENGTH_METADATA_BYTES: u32 = 12;
pub(crate) const TEMP_CONTEXT_METADATA_OFFSET: u32 = 1_163_272;
pub(crate) const TEMP_CONTEXT_METADATA_BYTES: u32 = 4;
const B3B_SCALAR_OFFSET: u32 = 1_163_276;
const B3B_SCALAR_BYTES: u32 = 256;
const B3B_RESERVED_STATE_OFFSET: u32 = 1_163_532;
const B3B_RESERVED_STATE_BYTES: u32 = 13_028;
const TREE_METADATA_RECORD_BYTES: u32 = 4;
pub(crate) const MTF_LIST_OFFSET: u32 = MTF_OFFSET + 4;
pub(crate) const MTF_LIST_BYTES: u32 = 256;
const COVERAGE_BITMAP_BYTES: u16 = 32;

pub(crate) const MAX_TREE_GROUPS: u16 = 256;
pub(crate) const LITERAL_SYMBOLS: u16 = 256;
pub(crate) const COMMAND_SYMBOLS: u16 = 704;
pub(crate) const DISTANCE_SYMBOLS: u16 = 520;
pub(crate) const BLOCK_TYPE_SYMBOLS: u16 = 258;
pub(crate) const BLOCK_LENGTH_SYMBOLS: u16 = 26;
pub(crate) const TEMP_CONTEXT_SYMBOLS: u16 = 272;
pub(crate) const BUILDER_CODE_LENGTHS: u16 = 704;
pub(crate) const BUILDER_COUNTS: u16 = 16;
pub(crate) const BUILDER_NEXT_CODES: u16 = 16;
pub(crate) const BUILDER_SYMBOL_CHAIN_ENTRIES: u16 = 720;
const TREE_RECORD_BYTES: u32 = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WorkspaceError {
    InvalidWindowBits,
    WorkspaceTooSmall,
    InvalidTree,
    InvalidSymbol,
    InvalidCodeLength,
    UninitializedRecord,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MetadataReadError {
    Workspace(WorkspaceError),
    InvalidEncoding,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContextMapKind {
    Literal,
    Distance,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TreeRegion {
    Literal,
    Command,
    Distance,
    BlockType,
    BlockLength,
    TemporaryContext,
}

pub(crate) open spec fn tree_region_offset(region: TreeRegion) -> nat {
    match region {
        TreeRegion::Literal => LITERAL_TREES_OFFSET as nat,
        TreeRegion::Command => COMMAND_TREES_OFFSET as nat,
        TreeRegion::Distance => DISTANCE_TREES_OFFSET as nat,
        TreeRegion::BlockType => BLOCK_TYPE_TREES_OFFSET as nat,
        TreeRegion::BlockLength => BLOCK_LENGTH_TREES_OFFSET as nat,
        TreeRegion::TemporaryContext => TEMP_CONTEXT_TREE_OFFSET as nat,
    }
}

pub(crate) open spec fn tree_region_count(region: TreeRegion) -> nat {
    match region {
        TreeRegion::Literal | TreeRegion::Command | TreeRegion::Distance => 256,
        TreeRegion::BlockType | TreeRegion::BlockLength => 3,
        TreeRegion::TemporaryContext => 1,
    }
}

pub(crate) open spec fn tree_region_symbols(region: TreeRegion) -> nat {
    match region {
        TreeRegion::Literal => LITERAL_SYMBOLS as nat,
        TreeRegion::Command => COMMAND_SYMBOLS as nat,
        TreeRegion::Distance => DISTANCE_SYMBOLS as nat,
        TreeRegion::BlockType => BLOCK_TYPE_SYMBOLS as nat,
        TreeRegion::BlockLength => BLOCK_LENGTH_SYMBOLS as nat,
        TreeRegion::TemporaryContext => TEMP_CONTEXT_SYMBOLS as nat,
    }
}

spec fn tree_region_bytes(region: TreeRegion) -> nat {
    tree_region_count(region) * tree_region_symbols(region) * TREE_RECORD_BYTES as nat
}

pub(crate) open spec fn tree_record_at(
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbol: u16,
) -> nat {
    window_bytes as nat + tree_region_offset(region)
        + (tree as nat * tree_region_symbols(region) + symbol as nat) * 3
}

proof fn fixed_layout_is_exact()
    ensures
        LITERAL_TREES_OFFSET + LITERAL_TREES_BYTES == COMMAND_TREES_OFFSET,
        COMMAND_TREES_OFFSET + COMMAND_TREES_BYTES == DISTANCE_TREES_OFFSET,
        DISTANCE_TREES_OFFSET + DISTANCE_TREES_BYTES == LITERAL_CONTEXT_MAP_OFFSET,
        LITERAL_CONTEXT_MAP_OFFSET + LITERAL_CONTEXT_MAP_BYTES == DISTANCE_CONTEXT_MAP_OFFSET,
        DISTANCE_CONTEXT_MAP_OFFSET + DISTANCE_CONTEXT_MAP_BYTES == LITERAL_CONTEXT_MODES_OFFSET,
        LITERAL_CONTEXT_MODES_OFFSET + LITERAL_CONTEXT_MODES_BYTES == BLOCK_TYPE_TREES_OFFSET,
        BLOCK_TYPE_TREES_OFFSET + BLOCK_TYPE_TREES_BYTES == BLOCK_LENGTH_TREES_OFFSET,
        BLOCK_LENGTH_TREES_OFFSET + BLOCK_LENGTH_TREES_BYTES == BUILDER_OFFSET,
        BUILDER_CODE_LENGTHS_OFFSET == BUILDER_OFFSET,
        BUILDER_CODE_LENGTHS_OFFSET + BUILDER_CODE_LENGTHS_BYTES == BUILDER_COUNTS_OFFSET,
        BUILDER_COUNTS_OFFSET + BUILDER_COUNTS_BYTES == BUILDER_NEXT_CODES_OFFSET,
        BUILDER_NEXT_CODES_OFFSET + BUILDER_NEXT_CODES_BYTES == BUILDER_SYMBOL_CHAIN_OFFSET,
        BUILDER_SYMBOL_CHAIN_OFFSET + BUILDER_SYMBOL_CHAIN_BYTES == TEMP_CONTEXT_TREE_OFFSET,
        BUILDER_OFFSET + BUILDER_BYTES == MTF_OFFSET,
        MTF_OFFSET + MTF_BYTES == STATE_OFFSET,
        STATE_OFFSET + STATE_BYTES == FIXED_SCRATCH_BYTES,
        LITERAL_METADATA_OFFSET == STATE_OFFSET,
        LITERAL_METADATA_OFFSET + LITERAL_METADATA_BYTES == COMMAND_METADATA_OFFSET,
        COMMAND_METADATA_OFFSET + COMMAND_METADATA_BYTES == DISTANCE_METADATA_OFFSET,
        DISTANCE_METADATA_OFFSET + DISTANCE_METADATA_BYTES == BLOCK_TYPE_METADATA_OFFSET,
        BLOCK_TYPE_METADATA_OFFSET + BLOCK_TYPE_METADATA_BYTES == BLOCK_LENGTH_METADATA_OFFSET,
        BLOCK_LENGTH_METADATA_OFFSET + BLOCK_LENGTH_METADATA_BYTES
            == TEMP_CONTEXT_METADATA_OFFSET,
        TEMP_CONTEXT_METADATA_OFFSET + TEMP_CONTEXT_METADATA_BYTES == B3B_SCALAR_OFFSET,
        B3B_SCALAR_OFFSET + B3B_SCALAR_BYTES == B3B_RESERVED_STATE_OFFSET,
        B3B_RESERVED_STATE_OFFSET + B3B_RESERVED_STATE_BYTES == FIXED_SCRATCH_BYTES,
        MTF_LIST_OFFSET + MTF_LIST_BYTES == STATE_OFFSET,
        TEMP_CONTEXT_TREE_OFFSET >= BUILDER_OFFSET,
        TEMP_CONTEXT_TREE_OFFSET + TEMP_CONTEXT_TREE_BYTES == MTF_OFFSET,
{
}

pub(crate) open spec fn builder_entry_at(
    window_bytes: u32,
    offset: u32,
    index: u16,
    width: u8,
) -> nat {
    window_bytes as nat + offset as nat + index as nat * width as nat
}

pub(crate) open spec fn builder_length_sequence(
    workspace: Seq<u8>,
    window_bytes: u32,
    symbols: u16,
) -> Seq<u8> {
    Seq::new(symbols as nat, |i: int| {
        workspace[(window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat + i) as int]
    })
}

pub(crate) open spec fn builder_count_byte_sequence(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> Seq<u8> {
    Seq::new(BUILDER_COUNTS_BYTES as nat, |i: int| {
        workspace[(window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + i) as int]
    })
}

pub(crate) open spec fn builder_next_code_byte_sequence(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> Seq<u8> {
    Seq::new(BUILDER_NEXT_CODES_BYTES as nat, |i: int| {
        workspace[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + i) as int]
    })
}

pub(crate) closed spec fn valid_builder_lengths(lengths: Seq<u8>) -> bool {
    &&& 1 <= lengths.len() <= BUILDER_CODE_LENGTHS
    &&& forall|i: int| 0 <= i < lengths.len() ==> lengths[i] <= MAX_BITS
    &&& nonzero_count(lengths) >= 2
    &&& used_space(lengths) == CODE_SPACE
}

pub(crate) open spec fn little_u16_at(workspace: Seq<u8>, at: nat) -> nat {
    workspace[at as int] as nat + 256 * workspace[(at + 1) as int] as nat
}

pub(crate) open spec fn little_u32_at(workspace: Seq<u8>, at: nat) -> nat {
    workspace[at as int] as nat
        + 256 * workspace[(at + 1) as int] as nat
        + 65_536 * workspace[(at + 2) as int] as nat
        + 16_777_216 * workspace[(at + 3) as int] as nat
}

pub(crate) open spec fn builder_count_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    index: int,
) -> nat {
    little_u16_at(
        workspace,
        window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + index as nat * 2,
    )
}

pub(crate) open spec fn builder_next_code_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    index: int,
) -> nat {
    little_u32_at(
        workspace,
        window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + index as nat * 4,
    )
}

spec fn builder_counts_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    lengths: Seq<u8>,
    initialized: nat,
) -> bool {
    &&& initialized <= BUILDER_COUNTS
    &&& forall|i: int| 0 <= i < initialized
        ==> #[trigger] builder_count_at(workspace, window_bytes, i)
            == count_length(lengths, i as u8)
}

spec fn builder_next_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    lengths: Seq<u8>,
    initialized: nat,
) -> bool {
    &&& initialized <= BUILDER_NEXT_CODES
    &&& forall|i: int| 0 <= i < initialized
        ==> #[trigger] builder_next_code_at(workspace, window_bytes, i)
            == first_code(lengths, i as nat)
}

spec fn builder_next_for_symbol_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    lengths: Seq<u8>,
    processed: nat,
) -> bool {
    &&& processed <= lengths.len()
    &&& forall|i: int| 1 <= i < BUILDER_NEXT_CODES
        ==> #[trigger] builder_next_code_at(workspace, window_bytes, i)
            == first_code(lengths, i as nat)
                + count_length(lengths.take(processed as int), i as u8)
}

proof fn builder_counts_prefix_after_write(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    lengths: Seq<u8>,
    index: u16,
    value: u16,
)
    requires
        index < BUILDER_COUNTS,
        builder_counts_prefix(before, window_bytes, lengths, index as nat),
        value as nat == count_length(lengths, index as u8),
        {
            let at = builder_entry_at(window_bytes, BUILDER_COUNTS_OFFSET, index, 2);
            &&& at + 2 <= before.len()
            &&& after == before
                .update(at as int, (value % 256) as u8)
                .update(at as int + 1, (value / 256) as u8)
        },
    ensures builder_counts_prefix(
        after,
        window_bytes,
        lengths,
        index as nat + 1,
    ),
{
    reveal(builder_counts_prefix);
    split_builder_u16_is_exact(value);
    assert forall|i: int| 0 <= i < index + 1 implies
        #[trigger] builder_count_at(after, window_bytes, i)
            == count_length(lengths, i as u8) by {
        if i < index {
            assert(builder_count_at(before, window_bytes, i)
                == count_length(lengths, i as u8));
        } else {
            assert(i == index);
        }
    }
}

proof fn builder_next_prefix_after_write(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    lengths: Seq<u8>,
    index: u16,
    value: u32,
)
    requires
        index < BUILDER_NEXT_CODES,
        builder_next_prefix(before, window_bytes, lengths, index as nat),
        value as nat == first_code(lengths, index as nat),
        {
            let at = builder_entry_at(window_bytes, BUILDER_NEXT_CODES_OFFSET, index, 4);
            &&& at + 4 <= before.len()
            &&& after == before
                .update(at as int, (value % 256) as u8)
                .update(at as int + 1, ((value / 256) % 256) as u8)
                .update(at as int + 2, ((value / 65_536) % 256) as u8)
                .update(at as int + 3, (value / 16_777_216) as u8)
        },
    ensures builder_next_prefix(
        after,
        window_bytes,
        lengths,
        index as nat + 1,
    ),
{
    reveal(builder_next_prefix);
    split_builder_u32_is_exact(value);
    assert forall|i: int| 0 <= i < index + 1 implies
        #[trigger] builder_next_code_at(after, window_bytes, i)
            == first_code(lengths, i as nat) by {
        if i < index {
            assert(builder_next_code_at(before, window_bytes, i)
                == first_code(lengths, i as nat));
        } else {
            assert(i == index);
        }
    }
}

spec fn canonical_tree_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    lengths: Seq<u8>,
    initialized: nat,
) -> bool {
    &&& initialized <= lengths.len()
    &&& forall|i: int| 0 <= i < initialized
        ==> #[trigger] workspace[
            tree_record_at(window_bytes, region, tree, i as u16) as int
        ] == lengths[i]
    &&& forall|i: int| 0 <= i < initialized
        ==> #[trigger] little_u16_at(
            workspace,
            tree_record_at(window_bytes, region, tree, i as u16) + 1,
        )
            == if lengths[i] == 0 { 0 } else { canonical_code(lengths, i) }
}

pub(crate) closed spec fn canonical_tree_installed(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    lengths: Seq<u8>,
) -> bool {
    canonical_tree_prefix(
        workspace,
        window_bytes,
        region,
        tree,
        lengths,
        lengths.len(),
    )
}

proof fn canonical_tree_prefix_after_write(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    lengths: Seq<u8>,
    index: u16,
    record: TreeRecord,
)
    requires
        index < lengths.len(),
        canonical_tree_prefix(
            before,
            window_bytes,
            region,
            tree,
            lengths,
            index as nat,
        ),
        record.length == lengths[index as int],
        record.code as nat == if record.length == 0 {
            0
        } else {
            canonical_code(lengths, index as int)
        },
        {
            let at = tree_record_at(window_bytes, region, tree, index);
            &&& at + 3 <= before.len()
            &&& after == before
                .update(at as int, record.length)
                .update(at as int + 1, (record.code % 256) as u8)
                .update(at as int + 2, (record.code / 256) as u8)
        },
    ensures canonical_tree_prefix(
        after,
        window_bytes,
        region,
        tree,
        lengths,
        index as nat + 1,
    ),
{
    reveal(canonical_tree_prefix);
    split_builder_u16_is_exact(record.code);
    assert(index as nat + 1 <= lengths.len());
    assert forall|i: int| 0 <= i < index + 1 implies {
        &&& after[tree_record_at(window_bytes, region, tree, i as u16) as int]
            == lengths[i]
        &&& #[trigger] little_u16_at(
            after,
            tree_record_at(window_bytes, region, tree, i as u16) + 1,
        )
            == if lengths[i] == 0 { 0 } else { canonical_code(lengths, i) }
    } by {
        if i < index {
            assert(tree_record_at(window_bytes, region, tree, i as u16) + 3
                <= tree_record_at(window_bytes, region, tree, index));
            assert(little_u16_at(
                before,
                tree_record_at(window_bytes, region, tree, i as u16) + 1,
            ) == if lengths[i] == 0 { 0 } else { canonical_code(lengths, i) });
            assert(before[tree_record_at(window_bytes, region, tree, i as u16) as int]
                == lengths[i]);
        } else {
            assert(i == index);
            assert(after[tree_record_at(window_bytes, region, tree, index) as int]
                == record.length);
            assert(little_u16_at(
                after,
                tree_record_at(window_bytes, region, tree, index) + 1,
            ) == record.code as nat);
        }
    }
    assert(canonical_tree_prefix(
        after,
        window_bytes,
        region,
        tree,
        lengths,
        index as nat + 1,
    )) by {
        reveal(canonical_tree_prefix);
        assert(index as nat + 1 <= lengths.len());
        assert forall|i: int| 0 <= i < index as int + 1 implies {
            &&& after[tree_record_at(window_bytes, region, tree, i as u16) as int]
                == lengths[i]
            &&& #[trigger] little_u16_at(
                after,
                tree_record_at(window_bytes, region, tree, i as u16) + 1,
            ) == if lengths[i] == 0 { 0 } else { canonical_code(lengths, i) }
        } by {
            assert(little_u16_at(
                after,
                tree_record_at(window_bytes, region, tree, i as u16) + 1,
            ) == if lengths[i] == 0 { 0 } else { canonical_code(lengths, i) });
            assert(after[tree_record_at(window_bytes, region, tree, i as u16) as int]
                == lengths[i]);
        }
    }
}

pub(crate) open spec fn canonical_installer_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbols: u16,
) -> bool {
    &&& before.len() == after.len()
    &&& forall|i: int| 0 <= i < before.len() ==> {
        let builder_start = window_bytes as nat + BUILDER_COUNTS_OFFSET as nat;
        let builder_end = window_bytes as nat + TEMP_CONTEXT_TREE_OFFSET as nat;
        let tree_start = tree_record_at(window_bytes, region, tree, 0);
        let tree_end = tree_start + symbols as nat * 3;
        !(builder_start <= i < builder_end || tree_start <= i < tree_end)
            ==> #[trigger] after[i] == before[i]
    }
}

proof fn builder_length_sequence_index(
    workspace: Seq<u8>,
    window_bytes: u32,
    symbols: u16,
    index: u16,
)
    requires
        index < symbols,
        window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat + symbols as nat
            <= workspace.len(),
    ensures builder_length_sequence(workspace, window_bytes, symbols)[index as int]
        == workspace[(window_bytes as nat
            + BUILDER_CODE_LENGTHS_OFFSET as nat
            + index as nat) as int],
{
}

proof fn builder_count_byte_sequence_index(
    workspace: Seq<u8>,
    window_bytes: u32,
    index: int,
)
    requires
        0 <= index < BUILDER_COUNTS_BYTES,
        window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + BUILDER_COUNTS_BYTES as nat
            <= workspace.len(),
    ensures builder_count_byte_sequence(workspace, window_bytes)[index]
        == workspace[(window_bytes as nat
            + BUILDER_COUNTS_OFFSET as nat
            + index as nat) as int],
{
}

proof fn builder_next_code_byte_sequence_index(
    workspace: Seq<u8>,
    window_bytes: u32,
    index: int,
)
    requires
        0 <= index < BUILDER_NEXT_CODES_BYTES,
        window_bytes as nat
            + BUILDER_NEXT_CODES_OFFSET as nat
            + BUILDER_NEXT_CODES_BYTES as nat
            <= workspace.len(),
    ensures builder_next_code_byte_sequence(workspace, window_bytes)[index]
        == workspace[(window_bytes as nat
            + BUILDER_NEXT_CODES_OFFSET as nat
            + index as nat) as int],
{
}

proof fn builder_length_matches_snapshot(
    current: Seq<u8>,
    original: Seq<u8>,
    window_bytes: u32,
    symbols: u16,
    index: u16,
)
    requires
        index < symbols <= BUILDER_CODE_LENGTHS,
        window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= current.len(),
        current.len() == original.len(),
        builder_length_sequence(current, window_bytes, BUILDER_CODE_LENGTHS)
            == builder_length_sequence(original, window_bytes, BUILDER_CODE_LENGTHS),
    ensures current[(window_bytes as nat
        + BUILDER_CODE_LENGTHS_OFFSET as nat
        + index as nat) as int]
        == builder_length_sequence(original, window_bytes, symbols)[index as int],
{
    builder_length_sequence_index(
        current,
        window_bytes,
        BUILDER_CODE_LENGTHS,
        index,
    );
    builder_length_sequence_index(
        original,
        window_bytes,
        BUILDER_CODE_LENGTHS,
        index,
    );
    builder_length_sequence_index(original, window_bytes, symbols, index);
}

proof fn builder_count_matches_snapshot(
    current: Seq<u8>,
    snapshot: Seq<u8>,
    window_bytes: u32,
    index: u16,
)
    requires
        index < BUILDER_COUNTS,
        window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= current.len(),
        current.len() == snapshot.len(),
        builder_count_byte_sequence(current, window_bytes)
            == builder_count_byte_sequence(snapshot, window_bytes),
    ensures builder_count_at(current, window_bytes, index as int)
        == builder_count_at(snapshot, window_bytes, index as int),
{
    let byte = index as int * 2;
    assert(0 <= byte && byte + 1 < BUILDER_COUNTS_BYTES);
    builder_count_byte_sequence_index(current, window_bytes, byte);
    builder_count_byte_sequence_index(current, window_bytes, byte + 1);
    builder_count_byte_sequence_index(snapshot, window_bytes, byte);
    builder_count_byte_sequence_index(snapshot, window_bytes, byte + 1);
    assert(builder_count_byte_sequence(current, window_bytes)[byte]
        == builder_count_byte_sequence(snapshot, window_bytes)[byte]);
    assert(builder_count_byte_sequence(current, window_bytes)[byte + 1]
        == builder_count_byte_sequence(snapshot, window_bytes)[byte + 1]);
    assert(current[(window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + byte as nat) as int]
        == snapshot[(window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + byte as nat) as int]);
    assert(current[(window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + byte as nat + 1) as int]
        == snapshot[(window_bytes as nat + BUILDER_COUNTS_OFFSET as nat + byte as nat + 1) as int]);
}

proof fn builder_next_code_matches_snapshot(
    current: Seq<u8>,
    snapshot: Seq<u8>,
    window_bytes: u32,
    index: u16,
)
    requires
        index < BUILDER_NEXT_CODES,
        window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= current.len(),
        current.len() == snapshot.len(),
        builder_next_code_byte_sequence(current, window_bytes)
            == builder_next_code_byte_sequence(snapshot, window_bytes),
    ensures builder_next_code_at(current, window_bytes, index as int)
        == builder_next_code_at(snapshot, window_bytes, index as int),
{
    let byte = index as int * 4;
    assert(0 <= byte && byte + 3 < BUILDER_NEXT_CODES_BYTES);
    builder_next_code_byte_sequence_index(current, window_bytes, byte);
    builder_next_code_byte_sequence_index(current, window_bytes, byte + 1);
    builder_next_code_byte_sequence_index(current, window_bytes, byte + 2);
    builder_next_code_byte_sequence_index(current, window_bytes, byte + 3);
    builder_next_code_byte_sequence_index(snapshot, window_bytes, byte);
    builder_next_code_byte_sequence_index(snapshot, window_bytes, byte + 1);
    builder_next_code_byte_sequence_index(snapshot, window_bytes, byte + 2);
    builder_next_code_byte_sequence_index(snapshot, window_bytes, byte + 3);
    assert(builder_next_code_byte_sequence(current, window_bytes)[byte]
        == builder_next_code_byte_sequence(snapshot, window_bytes)[byte]);
    assert(builder_next_code_byte_sequence(current, window_bytes)[byte + 1]
        == builder_next_code_byte_sequence(snapshot, window_bytes)[byte + 1]);
    assert(builder_next_code_byte_sequence(current, window_bytes)[byte + 2]
        == builder_next_code_byte_sequence(snapshot, window_bytes)[byte + 2]);
    assert(builder_next_code_byte_sequence(current, window_bytes)[byte + 3]
        == builder_next_code_byte_sequence(snapshot, window_bytes)[byte + 3]);
    assert(current[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat) as int]
        == snapshot[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat) as int]);
    assert(current[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat + 1) as int]
        == snapshot[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat + 1) as int]);
    assert(current[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat + 2) as int]
        == snapshot[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat + 2) as int]);
    assert(current[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat + 3) as int]
        == snapshot[(window_bytes as nat + BUILDER_NEXT_CODES_OFFSET as nat + byte as nat + 3) as int]);
}

fn builder_entry_offset(
    window_bytes: u32,
    offset: u32,
    entries: u16,
    width: u8,
    index: u16,
) -> (r: Result<usize, WorkspaceError>)
    requires
        BUILDER_OFFSET <= offset,
        1 <= width <= 4,
        offset as nat + entries as nat * width as nat
            <= BUILDER_OFFSET as nat + BUILDER_BYTES as nat,
    ensures
    window_bytes <= 16_777_216 && index < entries ==> r.is_ok(),
    r.is_ok() ==> {
        &&& index < entries
        &&& r.unwrap() as nat == builder_entry_at(window_bytes, offset, index, width)
        &&& r.unwrap() as nat + width as nat
            <= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    if index >= entries {
        return Err(WorkspaceError::InvalidSymbol);
    }
    proof {
        assert(index as nat + 1 <= entries as nat);
        lemma_mul_inequality(
            index as int + 1,
            entries as int,
            width as int,
        );
        assert(index as nat * width as nat + width as nat
            <= entries as nat * width as nat);
        assert(offset as nat + index as nat * width as nat + width as nat
            <= BUILDER_OFFSET as nat + BUILDER_BYTES as nat);
        fixed_layout_is_exact();
        assert(BUILDER_OFFSET as nat + BUILDER_BYTES as nat
            <= FIXED_SCRATCH_BYTES as nat);
        assert(index as nat * width as nat <= u32::MAX);
        assert(offset as nat + index as nat * width as nat <= u32::MAX);
        assert(window_bytes as nat + offset as nat + index as nat * width as nat
            <= u32::MAX);
    }
    let bytes = (index as u32) * (width as u32);
    let relative = offset + bytes;
    let absolute = window_bytes + relative;
    proof {
        assert(bytes as nat == index as nat * width as nat);
        assert(relative as nat == offset as nat + bytes as nat);
        assert(absolute as nat == window_bytes as nat + relative as nat);
    }
    Ok(absolute as usize)
}

pub(crate) fn write_next_builder_code_length(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    value: u8,
) -> (r: Result<u16, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized < BUILDER_CODE_LENGTHS
            ==> r.is_ok(),
        r.is_ok() ==> {
            let at = builder_entry_at(
                window_bytes,
                BUILDER_CODE_LENGTHS_OFFSET,
                initialized,
                1,
            );
            &&& initialized < BUILDER_CODE_LENGTHS
            &&& r.unwrap() == initialized + 1
            &&& at < old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@.update(at as int, value)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized >= BUILDER_CODE_LENGTHS {
        return Err(WorkspaceError::InvalidSymbol);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_CODE_LENGTHS_OFFSET,
        BUILDER_CODE_LENGTHS,
        1,
        initialized,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = value;
    Ok(initialized + 1)
}

pub(crate) fn read_builder_code_length(
    workspace: &[u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
) -> (r: Result<u8, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized <= BUILDER_CODE_LENGTHS
            && index < initialized
            ==> r.is_ok(),
        r.is_ok() ==> {
        let at = builder_entry_at(window_bytes, BUILDER_CODE_LENGTHS_OFFSET, index, 1);
        &&& initialized <= BUILDER_CODE_LENGTHS
        &&& index < initialized
        &&& at < workspace@.len()
        &&& r.unwrap() == workspace@[at as int]
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized > BUILDER_CODE_LENGTHS || index >= BUILDER_CODE_LENGTHS {
        return Err(WorkspaceError::InvalidSymbol);
    }
    if index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_CODE_LENGTHS_OFFSET,
        BUILDER_CODE_LENGTHS,
        1,
        index,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(workspace[at])
}

pub(crate) fn write_next_builder_count(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    value: u16,
) -> (r: Result<u16, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_length_sequence(
                final(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ) == builder_length_sequence(
                old(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized < BUILDER_COUNTS
            ==> r.is_ok(),
        r.is_ok() ==> {
            let at = builder_entry_at(window_bytes, BUILDER_COUNTS_OFFSET, initialized, 2);
            let low = (value % 256) as u8;
            let high = (value / 256) as u8;
            &&& initialized < BUILDER_COUNTS
            &&& r.unwrap() == initialized + 1
            &&& at + 2 <= old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at as int, low)
                .update(at as int + 1, high)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized >= BUILDER_COUNTS {
        return Err(WorkspaceError::InvalidSymbol);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_COUNTS_OFFSET,
        BUILDER_COUNTS,
        2,
        initialized,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = (value % 256) as u8;
    workspace[at + 1] = (value / 256) as u8;
    Ok(initialized + 1)
}

pub(crate) fn read_builder_count(
    workspace: &[u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
) -> (r: Result<u16, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized <= BUILDER_COUNTS
            && index < initialized
            ==> r.is_ok(),
        r.is_ok() ==> {
        let at = builder_entry_at(window_bytes, BUILDER_COUNTS_OFFSET, index, 2);
        &&& initialized <= BUILDER_COUNTS
        &&& index < initialized
        &&& at + 2 <= workspace@.len()
        &&& r.unwrap() as nat == workspace@[at as int] as nat
            + 256 * workspace@[at as int + 1] as nat
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized > BUILDER_COUNTS || index >= BUILDER_COUNTS {
        return Err(WorkspaceError::InvalidSymbol);
    }
    if index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_COUNTS_OFFSET,
        BUILDER_COUNTS,
        2,
        index,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let low = workspace[at];
    let high = workspace[at + 1];
    proof { join_tree_code_is_exact(low, high); }
    Ok(low as u16 | ((high as u16) << 8))
}

pub(crate) fn write_next_builder_next_code(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    value: u32,
) -> (r: Result<u16, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_count_byte_sequence(final(workspace)@, window_bytes)
                == builder_count_byte_sequence(old(workspace)@, window_bytes),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_length_sequence(
                final(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ) == builder_length_sequence(
                old(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized < BUILDER_NEXT_CODES
            ==> r.is_ok(),
        r.is_ok() ==> {
            let at = builder_entry_at(window_bytes, BUILDER_NEXT_CODES_OFFSET, initialized, 4);
            let byte0 = (value % 256) as u8;
            let byte1 = ((value / 256) % 256) as u8;
            let byte2 = ((value / 65_536) % 256) as u8;
            let byte3 = (value / 16_777_216) as u8;
            &&& initialized < BUILDER_NEXT_CODES
            &&& r.unwrap() == initialized + 1
            &&& at + 4 <= old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at as int, byte0)
                .update(at as int + 1, byte1)
                .update(at as int + 2, byte2)
                .update(at as int + 3, byte3)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized >= BUILDER_NEXT_CODES {
        return Err(WorkspaceError::InvalidSymbol);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_NEXT_CODES_OFFSET,
        BUILDER_NEXT_CODES,
        4,
        initialized,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = (value % 256) as u8;
    workspace[at + 1] = ((value / 256) % 256) as u8;
    workspace[at + 2] = ((value / 65_536) % 256) as u8;
    workspace[at + 3] = (value / 16_777_216) as u8;
    Ok(initialized + 1)
}

pub(crate) fn read_builder_next_code(
    workspace: &[u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
) -> (r: Result<u32, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized <= BUILDER_NEXT_CODES
            && index < initialized
            ==> r.is_ok(),
        r.is_ok() ==> {
        let at = builder_entry_at(window_bytes, BUILDER_NEXT_CODES_OFFSET, index, 4);
        &&& initialized <= BUILDER_NEXT_CODES
        &&& index < initialized
        &&& at + 4 <= workspace@.len()
        &&& r.unwrap() as nat == workspace@[at as int] as nat
            + 256 * workspace@[at as int + 1] as nat
            + 65_536 * workspace@[at as int + 2] as nat
            + 16_777_216 * workspace@[at as int + 3] as nat
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized > BUILDER_NEXT_CODES || index >= BUILDER_NEXT_CODES {
        return Err(WorkspaceError::InvalidSymbol);
    }
    if index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_NEXT_CODES_OFFSET,
        BUILDER_NEXT_CODES,
        4,
        index,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let byte0 = workspace[at];
    let byte1 = workspace[at + 1];
    let byte2 = workspace[at + 2];
    let byte3 = workspace[at + 3];
    proof { join_builder_u32_is_exact(byte0, byte1, byte2, byte3); }
    Ok(byte0 as u32
        | ((byte1 as u32) << 8)
        | ((byte2 as u32) << 16)
        | ((byte3 as u32) << 24))
}

pub(crate) fn write_builder_next_code_at(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
    value: u32,
) -> (r: Result<(), WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_count_byte_sequence(final(workspace)@, window_bytes)
                == builder_count_byte_sequence(old(workspace)@, window_bytes),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_length_sequence(
                final(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ) == builder_length_sequence(
                old(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized <= BUILDER_NEXT_CODES
            && index < initialized
            ==> r.is_ok(),
        r.is_ok() ==> {
            let at = builder_entry_at(window_bytes, BUILDER_NEXT_CODES_OFFSET, index, 4);
            let byte0 = (value % 256) as u8;
            let byte1 = ((value / 256) % 256) as u8;
            let byte2 = ((value / 65_536) % 256) as u8;
            let byte3 = (value / 16_777_216) as u8;
            &&& initialized <= BUILDER_NEXT_CODES
            &&& index < initialized
            &&& at + 4 <= old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at as int, byte0)
                .update(at as int + 1, byte1)
                .update(at as int + 2, byte2)
                .update(at as int + 3, byte3)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized > BUILDER_NEXT_CODES || index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_NEXT_CODES_OFFSET,
        BUILDER_NEXT_CODES,
        4,
        index,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = (value % 256) as u8;
    workspace[at + 1] = ((value / 256) % 256) as u8;
    workspace[at + 2] = ((value / 65_536) % 256) as u8;
    workspace[at + 3] = (value / 16_777_216) as u8;
    Ok(())
}

pub(crate) fn write_next_builder_symbol_chain(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    value: u16,
) -> (r: Result<u16, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_count_byte_sequence(final(workspace)@, window_bytes)
                == builder_count_byte_sequence(old(workspace)@, window_bytes),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_length_sequence(
                final(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ) == builder_length_sequence(
                old(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized < BUILDER_SYMBOL_CHAIN_ENTRIES
            ==> r.is_ok(),
        r.is_ok() ==> {
            let at = builder_entry_at(
                window_bytes,
                BUILDER_SYMBOL_CHAIN_OFFSET,
                initialized,
                2,
            );
            let low = (value % 256) as u8;
            let high = (value / 256) as u8;
            &&& initialized < BUILDER_SYMBOL_CHAIN_ENTRIES
            &&& r.unwrap() == initialized + 1
            &&& at + 2 <= old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at as int, low)
                .update(at as int + 1, high)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized >= BUILDER_SYMBOL_CHAIN_ENTRIES {
        return Err(WorkspaceError::InvalidSymbol);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_SYMBOL_CHAIN_OFFSET,
        BUILDER_SYMBOL_CHAIN_ENTRIES,
        2,
        initialized,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = (value % 256) as u8;
    workspace[at + 1] = (value / 256) as u8;
    Ok(initialized + 1)
}

pub(crate) fn read_builder_symbol_chain(
    workspace: &[u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
) -> (r: Result<u16, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized <= BUILDER_SYMBOL_CHAIN_ENTRIES
            && index < initialized
            ==> r.is_ok(),
        r.is_ok() ==> {
        let at = builder_entry_at(window_bytes, BUILDER_SYMBOL_CHAIN_OFFSET, index, 2);
        &&& initialized <= BUILDER_SYMBOL_CHAIN_ENTRIES
        &&& index < initialized
        &&& at + 2 <= workspace@.len()
        &&& r.unwrap() as nat == workspace@[at as int] as nat
            + 256 * workspace@[at as int + 1] as nat
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized > BUILDER_SYMBOL_CHAIN_ENTRIES || index >= BUILDER_SYMBOL_CHAIN_ENTRIES {
        return Err(WorkspaceError::InvalidSymbol);
    }
    if index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_SYMBOL_CHAIN_OFFSET,
        BUILDER_SYMBOL_CHAIN_ENTRIES,
        2,
        index,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let low = workspace[at];
    let high = workspace[at + 1];
    proof { join_tree_code_is_exact(low, high); }
    Ok(low as u16 | ((high as u16) << 8))
}

pub(crate) fn write_builder_symbol_chain_at(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
    value: u16,
) -> (r: Result<(), WorkspaceError>)
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_count_byte_sequence(final(workspace)@, window_bytes)
                == builder_count_byte_sequence(old(workspace)@, window_bytes),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            ==> builder_length_sequence(
                final(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ) == builder_length_sequence(
                old(workspace)@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized <= BUILDER_SYMBOL_CHAIN_ENTRIES
            && index < initialized
            ==> r.is_ok(),
        r.is_ok() ==> {
            let at = builder_entry_at(window_bytes, BUILDER_SYMBOL_CHAIN_OFFSET, index, 2);
            let low = (value % 256) as u8;
            let high = (value / 256) as u8;
            &&& initialized <= BUILDER_SYMBOL_CHAIN_ENTRIES
            &&& index < initialized
            &&& at + 2 <= old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at as int, low)
                .update(at as int + 1, high)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if initialized > BUILDER_SYMBOL_CHAIN_ENTRIES || index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    proof { fixed_layout_is_exact(); }
    let at = match builder_entry_offset(
        window_bytes,
        BUILDER_SYMBOL_CHAIN_OFFSET,
        BUILDER_SYMBOL_CHAIN_ENTRIES,
        2,
        index,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = (value % 256) as u8;
    workspace[at + 1] = (value / 256) as u8;
    Ok(())
}

proof fn tree_layout_is_bounded(region: TreeRegion)
    ensures tree_region_offset(region) + tree_region_bytes(region)
        <= FIXED_SCRATCH_BYTES,
{
    fixed_layout_is_exact();
    match region {
        TreeRegion::Literal => {}
        TreeRegion::Command => {}
        TreeRegion::Distance => {}
        TreeRegion::BlockType => {}
        TreeRegion::BlockLength => {}
        TreeRegion::TemporaryContext => {}
    }
}

proof fn tree_record_outside_builder_code_lengths(
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbol: u16,
)
    requires
        tree < tree_region_count(region),
        symbol < tree_region_symbols(region),
    ensures {
        let at = tree_record_at(window_bytes, region, tree, symbol);
        let lengths_start = window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat;
        let lengths_end = lengths_start + BUILDER_CODE_LENGTHS as nat;
        at + 3 <= lengths_start || lengths_end <= at
    },
{
    fixed_layout_is_exact();
    tree_layout_is_bounded(region);
    assert(symbol as nat + 1 <= tree_region_symbols(region));
    assert(tree as nat + 1 <= tree_region_count(region));
    assert(tree as nat * tree_region_symbols(region) + symbol as nat + 1
        <= tree as nat * tree_region_symbols(region) + tree_region_symbols(region));
    lemma_mul_is_distributive_add_other_way(
        tree_region_symbols(region) as int,
        tree as int,
        1,
    );
    assert(tree as nat * tree_region_symbols(region) + symbol as nat + 1
        <= (tree as nat + 1) * tree_region_symbols(region));
    lemma_mul_inequality(
        tree as int + 1,
        tree_region_count(region) as int,
        tree_region_symbols(region) as int,
    );
    assert(tree_record_at(window_bytes, region, tree, symbol) + 3
        <= window_bytes as nat + tree_region_offset(region) + tree_region_bytes(region));
    match region {
        TreeRegion::Literal => {}
        TreeRegion::Command => {}
        TreeRegion::Distance => {}
        TreeRegion::BlockType => {}
        TreeRegion::BlockLength => {}
        TreeRegion::TemporaryContext => {}
    }
}

proof fn tree_record_outside_builder_bookkeeping(
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbol: u16,
)
    requires
        tree < tree_region_count(region),
        symbol < tree_region_symbols(region),
    ensures {
        let at = tree_record_at(window_bytes, region, tree, symbol);
        let builder_start = window_bytes as nat + BUILDER_COUNTS_OFFSET as nat;
        let builder_end = window_bytes as nat + TEMP_CONTEXT_TREE_OFFSET as nat;
        at + 3 <= builder_start || builder_end <= at
    },
{
    fixed_layout_is_exact();
    tree_layout_is_bounded(region);
    assert(symbol as nat + 1 <= tree_region_symbols(region));
    assert(tree as nat + 1 <= tree_region_count(region));
    assert(tree as nat * tree_region_symbols(region) + symbol as nat + 1
        <= tree as nat * tree_region_symbols(region) + tree_region_symbols(region));
    lemma_mul_is_distributive_add_other_way(
        tree_region_symbols(region) as int,
        tree as int,
        1,
    );
    assert(tree as nat * tree_region_symbols(region) + symbol as nat + 1
        <= (tree as nat + 1) * tree_region_symbols(region));
    lemma_mul_inequality(
        tree as int + 1,
        tree_region_count(region) as int,
        tree_region_symbols(region) as int,
    );
    assert(tree_record_at(window_bytes, region, tree, symbol) + 3
        <= window_bytes as nat + tree_region_offset(region) + tree_region_bytes(region));
    match region {
        TreeRegion::Literal => {}
        TreeRegion::Command => {}
        TreeRegion::Distance => {}
        TreeRegion::BlockType => {}
        TreeRegion::BlockLength => {}
        TreeRegion::TemporaryContext => {}
    }
}

#[verifier::bit_vector]
proof fn workspace_size_fits_u32(window_bits: u8)
    requires 10 <= window_bits <= 24,
    ensures (1u32 << window_bits) <= 16_777_216,
        (1u32 << window_bits) + FIXED_SCRATCH_BYTES <= u32::MAX,
{
}

pub(crate) fn required_workspace_bytes(window_bits: u8) -> (r: Result<u32, WorkspaceError>)
    ensures r.is_ok() ==> {
        &&& 10 <= window_bits <= 24
        &&& r.unwrap() == (1u32 << window_bits) + FIXED_SCRATCH_BYTES
    },
{
    if window_bits < 10 || window_bits > 24 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    proof { workspace_size_fits_u32(window_bits); }
    Ok((1u32 << window_bits) + FIXED_SCRATCH_BYTES)
}

fn tree_region_offset_exec(region: TreeRegion) -> (r: u32)
    ensures r as nat == tree_region_offset(region),
{
    match region {
        TreeRegion::Literal => LITERAL_TREES_OFFSET,
        TreeRegion::Command => COMMAND_TREES_OFFSET,
        TreeRegion::Distance => DISTANCE_TREES_OFFSET,
        TreeRegion::BlockType => BLOCK_TYPE_TREES_OFFSET,
        TreeRegion::BlockLength => BLOCK_LENGTH_TREES_OFFSET,
        TreeRegion::TemporaryContext => TEMP_CONTEXT_TREE_OFFSET,
    }
}

fn tree_region_count_exec(region: TreeRegion) -> (r: u16)
    ensures r as nat == tree_region_count(region),
{
    match region {
        TreeRegion::Literal | TreeRegion::Command | TreeRegion::Distance => 256,
        TreeRegion::BlockType | TreeRegion::BlockLength => 3,
        TreeRegion::TemporaryContext => 1,
    }
}

fn tree_region_symbols_exec(region: TreeRegion) -> (r: u16)
    ensures r as nat == tree_region_symbols(region),
{
    match region {
        TreeRegion::Literal => LITERAL_SYMBOLS,
        TreeRegion::Command => COMMAND_SYMBOLS,
        TreeRegion::Distance => DISTANCE_SYMBOLS,
        TreeRegion::BlockType => BLOCK_TYPE_SYMBOLS,
        TreeRegion::BlockLength => BLOCK_LENGTH_SYMBOLS,
        TreeRegion::TemporaryContext => TEMP_CONTEXT_SYMBOLS,
    }
}

fn tree_record_offset(
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbol: u16,
) -> (r: Result<usize, WorkspaceError>)
    ensures
    window_bytes <= 16_777_216
        && tree < tree_region_count(region)
        && symbol < tree_region_symbols(region)
        ==> r.is_ok(),
    r.is_ok() ==> {
        &&& tree < tree_region_count(region)
        &&& symbol < tree_region_symbols(region)
        &&& r.unwrap() as nat == tree_record_at(window_bytes, region, tree, symbol)
        &&& r.unwrap() + 3 <= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let count = tree_region_count_exec(region);
    let symbols = tree_region_symbols_exec(region);
    if tree >= count {
        return Err(WorkspaceError::InvalidTree);
    }
    if symbol >= symbols {
        return Err(WorkspaceError::InvalidSymbol);
    }
    let region_offset = tree_region_offset_exec(region);
    proof {
        tree_layout_is_bounded(region);
        assert(count as nat == tree_region_count(region));
        assert(symbols as nat == tree_region_symbols(region));
        assert(tree < count);
        assert(symbol < symbols);
        assert(symbol as nat + 1 <= symbols as nat);
        assert(tree as nat + 1 <= count as nat);
        assert(tree as nat * symbols as nat + symbol as nat + 1
            <= tree as nat * symbols as nat + symbols as nat);
        lemma_mul_is_distributive_add_other_way(
            symbols as int,
            tree as int,
            1,
        );
        assert(tree as nat * symbols as nat + symbol as nat + 1
            <= (tree as nat + 1) * symbols as nat);
        lemma_mul_inequality(
            tree as int + 1,
            count as int,
            symbols as int,
        );
        assert((tree as nat + 1) * symbols as nat <= count as nat * symbols as nat);
        assert(tree as nat * tree_region_symbols(region) + symbol as nat + 1
            <= tree_region_count(region) * tree_region_symbols(region));
        assert(tree as nat * symbols as nat + symbol as nat <= u32::MAX);
        assert((tree as nat * symbols as nat + symbol as nat) * 3 <= u32::MAX);
        assert(region_offset as nat
            + (tree as nat * symbols as nat + symbol as nat) * 3
            <= FIXED_SCRATCH_BYTES as nat);
        assert(window_bytes as nat + region_offset as nat
            + (tree as nat * symbols as nat + symbol as nat) * 3
            <= u32::MAX);
    }
    let record = (tree as u32) * (symbols as u32) + symbol as u32;
    let bytes = record * TREE_RECORD_BYTES;
    let relative = region_offset + bytes;
    let absolute = window_bytes + relative;
    proof {
        assert(record as nat
            == tree as nat * tree_region_symbols(region) + symbol as nat);
        assert(bytes as nat == record as nat * 3);
        assert(relative as nat == tree_region_offset(region) + bytes as nat);
        assert(absolute as nat == window_bytes as nat + relative as nat);
        assert(relative as nat + 3
            <= tree_region_offset(region) + tree_region_bytes(region));
        assert(relative as nat + 3 <= FIXED_SCRATCH_BYTES);
    }
    Ok(absolute as usize)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TreeRecord {
    pub(crate) length: u8,
    pub(crate) code: u16,
}

#[verifier::bit_vector]
proof fn join_tree_code_is_exact(low: u8, high: u8)
    ensures (low as u16 | ((high as u16) << 8)) as nat
        == low as nat + 256 * high as nat,
{
}

#[verifier::bit_vector]
proof fn split_builder_u16_is_exact(value: u16)
    ensures (value % 256) as nat + 256 * (value / 256) as nat == value as nat,
{
}

#[verifier::bit_vector]
proof fn join_builder_u32_is_exact(byte0: u8, byte1: u8, byte2: u8, byte3: u8)
    ensures (byte0 as u32
        | ((byte1 as u32) << 8)
        | ((byte2 as u32) << 16)
        | ((byte3 as u32) << 24)) as nat
        == byte0 as nat
            + 256 * byte1 as nat
            + 65_536 * byte2 as nat
            + 16_777_216 * byte3 as nat,
{
}

#[verifier::bit_vector]
proof fn split_builder_u32_is_exact(value: u32)
    ensures (value % 256) as nat
        + 256 * ((value / 256) % 256) as nat
        + 65_536 * ((value / 65_536) % 256) as nat
        + 16_777_216 * (value / 16_777_216) as nat
        == value as nat,
{
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TreeStorageState {
    Unused,
    Single { symbol: u16 },
    Canonical { initialized: u16 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TreeMetadata {
    pub(crate) symbols: u16,
    pub(crate) storage: TreeStorageState,
}

impl TreeMetadata {
    pub(crate) open spec fn valid_for(&self, region: TreeRegion) -> bool {
        &&& self.symbols <= tree_region_symbols(region)
        &&& match self.storage {
            TreeStorageState::Unused => self.symbols == 0,
            TreeStorageState::Single { symbol } => self.symbols > 0 && symbol < self.symbols,
            TreeStorageState::Canonical { initialized } => {
                self.symbols > 0 && initialized <= self.symbols
            },
        }
    }

    pub(crate) fn unused() -> (r: Self)
        ensures
            r.valid_for(TreeRegion::Literal),
            r.valid_for(TreeRegion::Command),
            r.valid_for(TreeRegion::Distance),
            r.valid_for(TreeRegion::BlockType),
            r.valid_for(TreeRegion::BlockLength),
            r.valid_for(TreeRegion::TemporaryContext),
            r.symbols == 0,
            r.storage == TreeStorageState::Unused,
    {
        Self { symbols: 0, storage: TreeStorageState::Unused }
    }

    pub(crate) fn single(
        region: TreeRegion,
        symbols: u16,
        symbol: u16,
    ) -> (r: Result<Self, WorkspaceError>)
        ensures r.is_ok() ==> {
            &&& r.unwrap().valid_for(region)
            &&& r.unwrap().symbols == symbols
            &&& r.unwrap().storage == TreeStorageState::Single { symbol }
        },
    {
        let capacity = tree_region_symbols_exec(region);
        if symbols == 0 || symbols > capacity || symbol >= symbols {
            return Err(WorkspaceError::InvalidSymbol);
        }
        Ok(Self { symbols, storage: TreeStorageState::Single { symbol } })
    }

    pub(crate) fn canonical(
        region: TreeRegion,
        symbols: u16,
    ) -> (r: Result<Self, WorkspaceError>)
        ensures r.is_ok() ==> {
            &&& r.unwrap().valid_for(region)
            &&& r.unwrap().symbols == symbols
            &&& r.unwrap().storage == TreeStorageState::Canonical { initialized: 0 }
        },
    {
        let capacity = tree_region_symbols_exec(region);
        if symbols == 0 || symbols > capacity {
            return Err(WorkspaceError::InvalidSymbol);
        }
        Ok(Self { symbols, storage: TreeStorageState::Canonical { initialized: 0 } })
    }
}

pub(crate) open spec fn tree_metadata_region_offset(region: TreeRegion) -> nat {
    match region {
        TreeRegion::Literal => LITERAL_METADATA_OFFSET as nat,
        TreeRegion::Command => COMMAND_METADATA_OFFSET as nat,
        TreeRegion::Distance => DISTANCE_METADATA_OFFSET as nat,
        TreeRegion::BlockType => BLOCK_TYPE_METADATA_OFFSET as nat,
        TreeRegion::BlockLength => BLOCK_LENGTH_METADATA_OFFSET as nat,
        TreeRegion::TemporaryContext => TEMP_CONTEXT_METADATA_OFFSET as nat,
    }
}

pub(crate) open spec fn tree_metadata_at(
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
) -> nat {
    window_bytes as nat + tree_metadata_region_offset(region) + tree as nat * 4
}

pub(crate) open spec fn tree_metadata_descriptor(meta: TreeMetadata) -> nat {
    match meta.storage {
        TreeStorageState::Unused => 0,
        TreeStorageState::Single { symbol } => 0x8000nat + symbol as nat,
        TreeStorageState::Canonical { initialized } => initialized as nat,
    }
}

proof fn metadata_layout_is_bounded(region: TreeRegion)
    ensures tree_metadata_region_offset(region) + tree_region_count(region) * 4
        <= FIXED_SCRATCH_BYTES,
{
    fixed_layout_is_exact();
    match region {
        TreeRegion::Literal => {}
        TreeRegion::Command => {}
        TreeRegion::Distance => {}
        TreeRegion::BlockType => {}
        TreeRegion::BlockLength => {}
        TreeRegion::TemporaryContext => {}
    }
}

fn tree_metadata_offset(
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
) -> (r: Result<usize, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216 && tree < tree_region_count(region) ==> r.is_ok(),
        r.is_ok() ==> {
            &&& tree < tree_region_count(region)
            &&& r.unwrap() as nat == tree_metadata_at(window_bytes, region, tree)
            &&& r.unwrap() as nat + 4
                <= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let count = tree_region_count_exec(region);
    if tree >= count {
        return Err(WorkspaceError::InvalidTree);
    }
    let region_offset = match region {
        TreeRegion::Literal => LITERAL_METADATA_OFFSET,
        TreeRegion::Command => COMMAND_METADATA_OFFSET,
        TreeRegion::Distance => DISTANCE_METADATA_OFFSET,
        TreeRegion::BlockType => BLOCK_TYPE_METADATA_OFFSET,
        TreeRegion::BlockLength => BLOCK_LENGTH_METADATA_OFFSET,
        TreeRegion::TemporaryContext => TEMP_CONTEXT_METADATA_OFFSET,
    };
    proof {
        metadata_layout_is_bounded(region);
        assert(count as nat == tree_region_count(region));
        assert(tree as nat + 1 <= tree_region_count(region));
        assert(region_offset as nat == tree_metadata_region_offset(region));
        assert(region_offset as nat + tree as nat * 4 + 4
            <= FIXED_SCRATCH_BYTES as nat);
        assert(window_bytes as nat + region_offset as nat + tree as nat * 4
            <= u32::MAX);
    }
    Ok((window_bytes + region_offset + tree as u32 * TREE_METADATA_RECORD_BYTES) as usize)
}

#[verifier::bit_vector]
proof fn single_metadata_descriptor_is_exact(symbol: u16)
    requires symbol < 0x8000,
    ensures (0x8000u16 | symbol) as nat == 0x8000nat + symbol as nat,
{
}

#[verifier::bit_vector]
proof fn split_single_metadata_descriptor_is_exact(descriptor: u16)
    requires descriptor & 0x8000 != 0,
    ensures descriptor as nat == 0x8000nat + (descriptor & 0x7fff) as nat,
{
}

#[verifier::bit_vector]
proof fn metadata_descriptor_high_bit_is_exact(descriptor: u16)
    ensures
        (descriptor & 0x8000 != 0) == (0x8000nat <= descriptor as nat),
{
}

pub(crate) fn write_tree_metadata(
    workspace: &mut [u8],
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    meta: TreeMetadata,
) -> (r: Result<(), WorkspaceError>)
    requires meta.valid_for(region),
    ensures
        window_bytes <= 16_777_216
            && window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= old(workspace)@.len()
            && tree < tree_region_count(region) ==> r.is_ok(),
        r.is_ok() ==> {
            let at = tree_metadata_at(window_bytes, region, tree);
            let descriptor = tree_metadata_descriptor(meta);
            &&& tree < tree_region_count(region)
            &&& at + 4 <= old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at as int, (meta.symbols % 256) as u8)
                .update(at as int + 1, (meta.symbols / 256) as u8)
                .update(at as int + 2, (descriptor % 256) as u8)
                .update(at as int + 3, (descriptor / 256) as u8)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    let descriptor = match meta.storage {
        TreeStorageState::Unused => 0,
        TreeStorageState::Single { symbol } => {
            proof { single_metadata_descriptor_is_exact(symbol); }
            0x8000u16 | symbol
        }
        TreeStorageState::Canonical { initialized } => initialized,
    };
    let at = match tree_metadata_offset(window_bytes, region, tree) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = (meta.symbols % 256) as u8;
    workspace[at + 1] = (meta.symbols / 256) as u8;
    workspace[at + 2] = (descriptor % 256) as u8;
    workspace[at + 3] = (descriptor / 256) as u8;
    Ok(())
}

pub(crate) fn read_tree_metadata(
    workspace: &[u8],
    window_bytes: u32,
    region: TreeRegion,
    initialized_prefix: u16,
    tree: u16,
) -> (r: Result<TreeMetadata, MetadataReadError>)
    ensures
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && initialized_prefix <= tree_region_count(region)
            && tree < tree_region_count(region)
            && tree >= initialized_prefix
            ==> r == Err(MetadataReadError::Workspace(
                WorkspaceError::UninitializedRecord,
            )),
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && tree < initialized_prefix <= tree_region_count(region)
            ==> (r.is_ok() == {
                let at = tree_metadata_at(window_bytes, region, tree);
                let symbols = little_u16_at(workspace@, at);
                let descriptor = little_u16_at(workspace@, at + 2);
                &&& symbols <= tree_region_symbols(region)
                &&& if symbols == 0 {
                    descriptor == 0
                } else {
                    ||| descriptor <= symbols
                    ||| 0x8000 <= descriptor && descriptor - 0x8000 < symbols
                }
            }),
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && tree < initialized_prefix <= tree_region_count(region)
            && !{
                let at = tree_metadata_at(window_bytes, region, tree);
                let symbols = little_u16_at(workspace@, at);
                let descriptor = little_u16_at(workspace@, at + 2);
                &&& symbols <= tree_region_symbols(region)
                &&& if symbols == 0 {
                    descriptor == 0
                } else {
                    ||| descriptor <= symbols
                    ||| 0x8000 <= descriptor && descriptor - 0x8000 < symbols
                }
            }
            ==> r == Err(MetadataReadError::InvalidEncoding),
        r.is_ok() ==> {
        &&& tree < initialized_prefix <= tree_region_count(region)
        &&& r.unwrap().valid_for(region)
        &&& {
            let at = tree_metadata_at(window_bytes, region, tree);
            &&& at + 4 <= workspace@.len()
            &&& r.unwrap().symbols as nat == workspace@[at as int] as nat
                + 256 * workspace@[at as int + 1] as nat
            &&& tree_metadata_descriptor(r.unwrap())
                == workspace@[at as int + 2] as nat
                    + 256 * workspace@[at as int + 3] as nat
        }
    },
{
    let count = tree_region_count_exec(region);
    if initialized_prefix > count || tree >= count {
        return Err(MetadataReadError::Workspace(WorkspaceError::InvalidTree));
    }
    if tree >= initialized_prefix {
        return Err(MetadataReadError::Workspace(WorkspaceError::UninitializedRecord));
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(MetadataReadError::Workspace(WorkspaceError::WorkspaceTooSmall)),
    };
    if workspace.len() < required {
        return Err(MetadataReadError::Workspace(WorkspaceError::WorkspaceTooSmall));
    }
    let at = match tree_metadata_offset(window_bytes, region, tree) {
        Ok(value) => value,
        Err(error) => return Err(MetadataReadError::Workspace(error)),
    };
    let symbols_low = workspace[at];
    let symbols_high = workspace[at + 1];
    let descriptor_low = workspace[at + 2];
    let descriptor_high = workspace[at + 3];
    proof {
        join_tree_code_is_exact(symbols_low, symbols_high);
        join_tree_code_is_exact(descriptor_low, descriptor_high);
    }
    let symbols = symbols_low as u16 | ((symbols_high as u16) << 8);
    let descriptor = descriptor_low as u16 | ((descriptor_high as u16) << 8);
    proof { metadata_descriptor_high_bit_is_exact(descriptor); }
    let capacity = tree_region_symbols_exec(region);
    let storage = if symbols == 0 {
        if descriptor != 0 {
            return Err(MetadataReadError::InvalidEncoding);
        }
        TreeStorageState::Unused
    } else if symbols > capacity {
        return Err(MetadataReadError::InvalidEncoding);
    } else if descriptor & 0x8000 != 0 {
        proof { split_single_metadata_descriptor_is_exact(descriptor); }
        let symbol = descriptor & 0x7fff;
        if symbol >= symbols {
            return Err(MetadataReadError::InvalidEncoding);
        }
        TreeStorageState::Single { symbol }
    } else {
        if descriptor > symbols {
            return Err(MetadataReadError::InvalidEncoding);
        }
        TreeStorageState::Canonical { initialized: descriptor }
    };
    let meta = TreeMetadata { symbols, storage };
    proof {
        match storage {
            TreeStorageState::Single { symbol } => {
                single_metadata_descriptor_is_exact(symbol);
                assert(descriptor as nat == 0x8000nat + symbol as nat);
            }
            TreeStorageState::Unused => assert(descriptor == 0),
            TreeStorageState::Canonical { initialized } => assert(descriptor == initialized),
        }
        assert(meta.valid_for(region));
        assert(meta.symbols as nat == workspace@[at as int] as nat
            + 256 * workspace@[at as int + 1] as nat);
        assert(tree_metadata_descriptor(meta) == descriptor as nat);
    }
    Ok(meta)
}

pub(crate) open spec fn context_map_offset(kind: ContextMapKind) -> nat {
    match kind {
        ContextMapKind::Literal => LITERAL_CONTEXT_MAP_OFFSET as nat,
        ContextMapKind::Distance => DISTANCE_CONTEXT_MAP_OFFSET as nat,
    }
}

pub(crate) open spec fn context_map_capacity(kind: ContextMapKind) -> nat {
    match kind {
        ContextMapKind::Literal => LITERAL_CONTEXT_MAP_BYTES as nat,
        ContextMapKind::Distance => DISTANCE_CONTEXT_MAP_BYTES as nat,
    }
}

pub(crate) open spec fn context_entry_at(
    window_bytes: u32,
    kind: ContextMapKind,
    index: u16,
) -> nat {
    window_bytes as nat + context_map_offset(kind) + index as nat
}

pub(crate) open spec fn literal_context_entry_at(
    window_bytes: u32,
    block: u16,
    context: u8,
) -> nat {
    window_bytes as nat + LITERAL_CONTEXT_MAP_OFFSET as nat
        + block as nat * 64 + context as nat
}

pub(crate) open spec fn distance_context_entry_at(
    window_bytes: u32,
    block: u16,
    context: u8,
) -> nat {
    window_bytes as nat + DISTANCE_CONTEXT_MAP_OFFSET as nat
        + block as nat * 4 + context as nat
}

pub(crate) open spec fn context_mode_at(window_bytes: u32, index: u16) -> nat {
    window_bytes as nat + LITERAL_CONTEXT_MODES_OFFSET as nat + index as nat
}

fn context_entry_offset(
    window_bytes: u32,
    kind: ContextMapKind,
    index: u16,
) -> (r: Result<usize, WorkspaceError>)
    ensures
        window_bytes <= 16_777_216 && index < context_map_capacity(kind) ==> r.is_ok(),
        r.is_ok() ==> {
            &&& index < context_map_capacity(kind)
            &&& r.unwrap() as nat == context_entry_at(window_bytes, kind, index)
            &&& (r.unwrap() as nat) < window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let (base, capacity) = match kind {
        ContextMapKind::Literal => (LITERAL_CONTEXT_MAP_OFFSET, LITERAL_CONTEXT_MAP_BYTES),
        ContextMapKind::Distance => (DISTANCE_CONTEXT_MAP_OFFSET, DISTANCE_CONTEXT_MAP_BYTES),
    };
    if index as u32 >= capacity {
        return Err(WorkspaceError::InvalidSymbol);
    }
    proof {
        fixed_layout_is_exact();
        assert((base as nat) + (index as nat) < (FIXED_SCRATCH_BYTES as nat));
        assert(window_bytes as nat + base as nat + index as nat <= u32::MAX);
    }
    Ok((window_bytes + base + index as u32) as usize)
}

proof fn bitmap_update_preserves_context_map(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
    byte: u16,
    value: u8,
)
    requires
        active_len <= context_map_capacity(kind),
        byte < COVERAGE_BITMAP_BYTES,
        coverage_bitmap_at(window_bytes, byte) < before.len(),
        after == before.update(coverage_bitmap_at(window_bytes, byte) as int, value),
    ensures context_map_values(after, window_bytes, kind, active_len)
        == context_map_values(before, window_bytes, kind, active_len),
{
    fixed_layout_is_exact();
    assert(context_map_values(after, window_bytes, kind, active_len) =~=
        context_map_values(before, window_bytes, kind, active_len));
}

pub(crate) fn write_next_context_entry(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
    initialized: u16,
    value: u8,
    num_htrees: u16,
) -> (r: Result<u16, WorkspaceError>)
    requires
        active_len <= context_map_capacity(kind),
        initialized <= active_len,
        1 <= num_htrees <= 256,
        (value as int) < num_htrees,
    ensures
        r.is_ok() ==> {
            let at = context_entry_at(window_bytes, kind, initialized);
            &&& initialized < active_len
            &&& r.unwrap() == initialized + 1
            &&& at < old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@.update(at as int, value)
        },
        r.is_ok() ==> {
            (forall|i: int| 0 <= i < initialized ==> #[trigger]
                old(workspace)@[context_entry_at(window_bytes, kind, i as u16) as int]
                    < num_htrees)
            ==> forall|i: int| 0 <= i < r.unwrap() ==> #[trigger]
                final(workspace)@[
                    context_entry_at(window_bytes, kind, i as u16) as int
                ] < num_htrees
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if num_htrees == 0 || num_htrees > 256 || value as u16 >= num_htrees {
        return Err(WorkspaceError::InvalidSymbol);
    }
    if initialized >= active_len {
        return Err(WorkspaceError::InvalidSymbol);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    let at = match context_entry_offset(window_bytes, kind, initialized) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = value;
    proof {
        assert forall|i: int| 0 <= i < initialized implies
            #[trigger] workspace@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ] == old(workspace)@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ] by {
            assert(context_entry_at(window_bytes, kind, i as u16) != at as nat);
        }
    }
    Ok(initialized + 1)
}

pub(crate) fn read_context_entry(
    workspace: &[u8],
    window_bytes: u32,
    kind: ContextMapKind,
    initialized: u16,
    index: u16,
    num_htrees: u16,
) -> (r: Result<u8, WorkspaceError>)
    requires
        initialized <= context_map_capacity(kind),
        1 <= num_htrees <= 256,
        index < initialized ==> workspace@[context_entry_at(window_bytes, kind, index) as int]
            < num_htrees,
    ensures r.is_ok() ==> {
        let at = context_entry_at(window_bytes, kind, index);
        &&& index < initialized
        &&& at < workspace@.len()
        &&& r.unwrap() == workspace@[at as int]
        &&& (r.unwrap() as int) < num_htrees
    },
{
    if num_htrees == 0 || num_htrees > 256 {
        return Err(WorkspaceError::InvalidSymbol);
    }
    if index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    let at = match context_entry_offset(window_bytes, kind, index) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(workspace[at])
}

pub(crate) fn write_next_context_mode(
    workspace: &mut [u8],
    window_bytes: u32,
    initialized: u16,
    value: u8,
) -> (r: Result<u16, WorkspaceError>)
    requires initialized <= LITERAL_CONTEXT_MODES_BYTES, value < 4,
    ensures
        r.is_ok() ==> {
            let at = context_mode_at(window_bytes, initialized);
            &&& initialized < LITERAL_CONTEXT_MODES_BYTES
            &&& r.unwrap() == initialized + 1
            &&& at < old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@.update(at as int, value)
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if initialized >= LITERAL_CONTEXT_MODES_BYTES as u16 {
        return Err(WorkspaceError::InvalidSymbol);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let at = (window_bytes + LITERAL_CONTEXT_MODES_OFFSET + initialized as u32) as usize;
    workspace[at] = value;
    Ok(initialized + 1)
}

pub(crate) fn read_context_mode(
    workspace: &[u8],
    window_bytes: u32,
    initialized: u16,
    index: u16,
) -> (r: Result<u8, WorkspaceError>)
    requires
        initialized <= LITERAL_CONTEXT_MODES_BYTES,
        index < initialized ==> workspace@[context_mode_at(window_bytes, index) as int] < 4,
    ensures r.is_ok() ==> {
        let at = context_mode_at(window_bytes, index);
        &&& index < initialized
        &&& at < workspace@.len()
        &&& r.unwrap() == workspace@[at as int]
        &&& r.unwrap() < 4
    },
{
    if index >= initialized {
        return Err(WorkspaceError::UninitializedRecord);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let at = (window_bytes + LITERAL_CONTEXT_MODES_OFFSET + index as u32) as usize;
    Ok(workspace[at])
}

pub(crate) open spec fn simple_selector_count(selector: u8) -> nat {
    if selector <= 2 { selector as nat + 1 } else { 4 }
}

pub(crate) open spec fn simple_rank_length(selector: u8, rank: nat) -> u8 {
    if selector == 1 { 1 }
    else if selector == 2 { if rank == 0 { 1 } else { 2 } }
    else if selector == 3 { 2 }
    else if rank == 0 { 1 } else if rank == 1 { 2 } else { 3 }
}

pub(crate) open spec fn simple_rank_code(selector: u8, rank: nat) -> u16 {
    if selector == 1 { rank as u16 }
    else if selector == 2 { if rank == 0 { 0 } else { (rank + 1) as u16 } }
    else if selector == 3 { rank as u16 }
    else if rank == 0 { 0 } else if rank == 1 { 2 } else { (rank + 4) as u16 }
}

pub(crate) open spec fn simple_record_for_symbol(
    selector: u8,
    count: u8,
    symbols: Seq<u16>,
    symbol: u16,
) -> TreeRecord {
    if symbol == symbols[0] {
        TreeRecord {
            length: simple_rank_length(selector, 0),
            code: simple_rank_code(selector, 0),
        }
    } else if count > 1 && symbol == symbols[1] {
        TreeRecord {
            length: simple_rank_length(selector, 1),
            code: simple_rank_code(selector, 1),
        }
    } else if count > 2 && symbol == symbols[2] {
        TreeRecord {
            length: simple_rank_length(selector, 2),
            code: simple_rank_code(selector, 2),
        }
    } else if count > 3 && symbol == symbols[3] {
        TreeRecord {
            length: simple_rank_length(selector, 3),
            code: simple_rank_code(selector, 3),
        }
    } else {
        TreeRecord { length: 0, code: 0 }
    }
}

pub(crate) open spec fn simple_tree_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    alphabet_limit: u16,
    selector: u8,
    count: u8,
    symbols: Seq<u16>,
    initialized: nat,
) -> bool {
    &&& initialized <= alphabet_limit
    &&& forall|i: int| 0 <= i < initialized
        ==> #[trigger] workspace[
            tree_record_at(window_bytes, region, tree, i as u16) as int
        ] == simple_record_for_symbol(selector, count, symbols, i as u16).length
    &&& forall|i: int| 0 <= i < initialized
        ==> #[trigger] little_u16_at(
            workspace,
            tree_record_at(window_bytes, region, tree, i as u16) + 1,
        ) == simple_record_for_symbol(selector, count, symbols, i as u16).code
}

pub(crate) open spec fn selected_tree_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbols: u16,
) -> bool {
    &&& before.len() == after.len()
    &&& forall|i: int| 0 <= i < before.len() ==> {
        let start = tree_record_at(window_bytes, region, tree, 0);
        let end = start + symbols as nat * 3;
        !(start <= i < end) ==> #[trigger] after[i] == before[i]
    }
}

proof fn simple_tree_prefix_after_write(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    alphabet_limit: u16,
    selector: u8,
    count: u8,
    symbols: Seq<u16>,
    index: u16,
    record: TreeRecord,
)
    requires
        index < alphabet_limit,
        simple_tree_prefix(
            before,
            window_bytes,
            region,
            tree,
            alphabet_limit,
            selector,
            count,
            symbols,
            index as nat,
        ),
        record == simple_record_for_symbol(selector, count, symbols, index),
        {
            let at = tree_record_at(window_bytes, region, tree, index);
            &&& at + 3 <= before.len()
            &&& after == before
                .update(at as int, record.length)
                .update(at as int + 1, (record.code % 256) as u8)
                .update(at as int + 2, (record.code / 256) as u8)
        },
    ensures simple_tree_prefix(
        after,
        window_bytes,
        region,
        tree,
        alphabet_limit,
        selector,
        count,
        symbols,
        index as nat + 1,
    ),
{
    reveal(simple_tree_prefix);
    split_builder_u16_is_exact(record.code);
    assert(index as nat + 1 <= alphabet_limit);
    assert forall|i: int| 0 <= i < index as int + 1 implies
        #[trigger] after[tree_record_at(window_bytes, region, tree, i as u16) as int]
            == simple_record_for_symbol(selector, count, symbols, i as u16).length by {
        if i < index {
            assert(tree_record_at(window_bytes, region, tree, i as u16) + 3
                <= tree_record_at(window_bytes, region, tree, index));
            assert(before[tree_record_at(window_bytes, region, tree, i as u16) as int]
                == simple_record_for_symbol(selector, count, symbols, i as u16).length);
        } else {
            assert(i == index);
        }
    }
    assert forall|i: int| 0 <= i < index as int + 1 implies
        #[trigger] little_u16_at(
            after,
            tree_record_at(window_bytes, region, tree, i as u16) + 1,
        ) == simple_record_for_symbol(selector, count, symbols, i as u16).code by {
        if i < index {
            assert(tree_record_at(window_bytes, region, tree, i as u16) + 3
                <= tree_record_at(window_bytes, region, tree, index));
            assert(little_u16_at(
                before,
                tree_record_at(window_bytes, region, tree, i as u16) + 1,
            ) == simple_record_for_symbol(selector, count, symbols, i as u16).code);
        } else {
            assert(i == index);
        }
    }
}

proof fn selected_tree_frame_after_write(
    original: Seq<u8>,
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    symbols: u16,
    index: u16,
    record: TreeRecord,
)
    requires
        index < symbols,
        selected_tree_frame(original, before, window_bytes, region, tree, symbols),
        {
            let at = tree_record_at(window_bytes, region, tree, index);
            &&& at + 3 <= before.len()
            &&& after == before
                .update(at as int, record.length)
                .update(at as int + 1, (record.code % 256) as u8)
                .update(at as int + 2, (record.code / 256) as u8)
        },
    ensures selected_tree_frame(original, after, window_bytes, region, tree, symbols),
{
    reveal(selected_tree_frame);
}

fn simple_record_exec(
    selector: u8,
    count: u8,
    symbols: &[u16; 4],
    symbol: u16,
) -> (r: TreeRecord)
    requires 1 <= selector <= 4, count as nat == simple_selector_count(selector),
    ensures r == simple_record_for_symbol(selector, count, symbols@, symbol),
{
    if symbol == symbols[0] {
        if selector == 1 {
            TreeRecord { length: 1, code: 0 }
        } else if selector == 2 {
            TreeRecord { length: 1, code: 0 }
        } else if selector == 3 {
            TreeRecord { length: 2, code: 0 }
        } else {
            TreeRecord { length: 1, code: 0 }
        }
    } else if count > 1 && symbol == symbols[1] {
        if selector == 1 {
            TreeRecord { length: 1, code: 1 }
        } else if selector == 2 {
            TreeRecord { length: 2, code: 2 }
        } else if selector == 3 {
            TreeRecord { length: 2, code: 1 }
        } else {
            TreeRecord { length: 2, code: 2 }
        }
    } else if count > 2 && symbol == symbols[2] {
        if selector == 2 {
            TreeRecord { length: 2, code: 3 }
        } else if selector == 3 {
            TreeRecord { length: 2, code: 2 }
        } else {
            TreeRecord { length: 3, code: 6 }
        }
    } else if count > 3 && symbol == symbols[3] {
        if selector == 3 {
            TreeRecord { length: 2, code: 3 }
        } else {
            TreeRecord { length: 3, code: 7 }
        }
    } else {
        TreeRecord { length: 0, code: 0 }
    }
}

pub(crate) fn install_simple_tree(
    workspace: &mut [u8],
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    alphabet_limit: u16,
    selector: u8,
    count: u8,
    symbols: [u16; 4],
) -> (r: Result<TreeMetadata, WorkspaceError>)
    ensures r.is_ok() ==> {
        &&& r.unwrap().valid_for(region)
        &&& r.unwrap().symbols == alphabet_limit
        &&& (tree as nat) < tree_region_count(region)
        &&& (alphabet_limit as nat) <= tree_region_symbols(region)
        &&& if selector == 0 {
            &&& count == 1
            &&& r.unwrap().storage == TreeStorageState::Single { symbol: symbols[0] }
            &&& final(workspace)@ == old(workspace)@
        } else {
            &&& 1 <= selector <= 4
            &&& count as nat == simple_selector_count(selector)
            &&& r.unwrap().storage == TreeStorageState::Canonical {
                initialized: alphabet_limit,
            }
            &&& simple_tree_prefix(
                final(workspace)@,
                window_bytes,
                region,
                tree,
                alphabet_limit,
                selector,
                count,
                symbols@,
                alphabet_limit as nat,
            )
            &&& selected_tree_frame(
                old(workspace)@,
                final(workspace)@,
                window_bytes,
                region,
                tree,
                alphabet_limit,
            )
        }
    },
    r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    let capacity = tree_region_symbols_exec(region);
    if alphabet_limit == 0 || alphabet_limit > capacity || tree >= tree_region_count_exec(region) {
        return Err(WorkspaceError::InvalidSymbol);
    }
    let expected = if selector <= 2 { selector + 1 } else { 4 };
    if selector > 4 || count != expected {
        return Err(WorkspaceError::InvalidCodeLength);
    }
    let mut i: u8 = 0;
    while i < count
        invariant i <= count <= 4,
        decreases count - i,
    {
        if symbols[i as usize] >= alphabet_limit {
            return Err(WorkspaceError::InvalidSymbol);
        }
        let mut j: u8 = 0;
        while j < i
            invariant j <= i < count <= 4,
            decreases i - j,
        {
            if symbols[j as usize] == symbols[i as usize] {
                return Err(WorkspaceError::InvalidSymbol);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    if selector == 0 {
        return TreeMetadata::single(region, alphabet_limit, symbols[0]);
    }
    let mut meta = match TreeMetadata::canonical(region, alphabet_limit) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let ghost before_workspace = workspace@;
    let mut symbol: u16 = 0;
    while symbol < alphabet_limit
        invariant
            symbol <= alphabet_limit <= tree_region_symbols(region),
            window_bytes <= 16_777_216,
            workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            tree < tree_region_count(region),
            1 <= selector <= 4,
            count as nat == simple_selector_count(selector),
            meta.valid_for(region),
            meta.symbols == alphabet_limit,
            meta.storage == (TreeStorageState::Canonical { initialized: symbol }),
            simple_tree_prefix(
                workspace@,
                window_bytes,
                region,
                tree,
                alphabet_limit,
                selector,
                count,
                symbols@,
                symbol as nat,
            ),
            selected_tree_frame(
                before_workspace,
                workspace@,
                window_bytes,
                region,
                tree,
                alphabet_limit,
            ),
        decreases alphabet_limit - symbol,
    {
        let record = simple_record_exec(selector, count, &symbols, symbol);
        let ghost before_write = workspace@;
        match write_next_tree_record(
            workspace,
            window_bytes,
            region,
            tree,
            &mut meta,
            record,
        ) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        proof {
            simple_tree_prefix_after_write(
                before_write,
                workspace@,
                window_bytes,
                region,
                tree,
                alphabet_limit,
                selector,
                count,
                symbols@,
                symbol,
                record,
            );
            selected_tree_frame_after_write(
                before_workspace,
                before_write,
                workspace@,
                window_bytes,
                region,
                tree,
                alphabet_limit,
                symbol,
                record,
            );
        }
        symbol = symbol + 1;
    }
    Ok(meta)
}

pub(crate) open spec fn context_map_values(
    workspace: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
) -> Seq<u8> {
    Seq::new(active_len as nat, |i: int| {
        workspace[(window_bytes as nat + context_map_offset(kind) + i as nat) as int]
    })
}

spec fn context_map_suffix_matches(
    workspace: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    ranks: Seq<u8>,
    start: nat,
) -> bool {
    forall|i: int| start <= i < ranks.len()
        ==> #[trigger] workspace[
            context_entry_at(window_bytes, kind, i as u16) as int
        ] == ranks[i]
}

proof fn context_map_suffix_index(
    workspace: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    ranks: Seq<u8>,
    start: nat,
    index: int,
)
    requires
        context_map_suffix_matches(workspace, window_bytes, kind, ranks, start),
        start <= index < ranks.len(),
    ensures workspace[context_entry_at(window_bytes, kind, index as u16) as int]
        == ranks[index],
{
    reveal(context_map_suffix_matches);
}

pub(crate) open spec fn value_seen(values: Seq<u8>, prefix: nat, value: nat) -> bool {
    exists|i: int| 0 <= i < prefix && values[i] as nat == value
}

pub(crate) open spec fn context_tree_coverage(values: Seq<u8>, num_htrees: u16) -> bool {
    forall|tree: int| 0 <= tree < num_htrees
        ==> #[trigger] value_seen(values, values.len(), tree as nat)
}

pub(crate) open spec fn byte_has_bit(value: u8, bit: nat) -> bool {
    if bit == 0 { value % 2 == 1 }
    else if bit == 1 { (value / 2) % 2 == 1 }
    else if bit == 2 { (value / 4) % 2 == 1 }
    else if bit == 3 { (value / 8) % 2 == 1 }
    else if bit == 4 { (value / 16) % 2 == 1 }
    else if bit == 5 { (value / 32) % 2 == 1 }
    else if bit == 6 { (value / 64) % 2 == 1 }
    else if bit == 7 { (value / 128) % 2 == 1 }
    else { false }
}

pub(crate) open spec fn coverage_bitmap_at(window_bytes: u32, byte: u16) -> nat {
    window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat + byte as nat
}

pub(crate) open spec fn coverage_bitmap_represents(
    workspace: Seq<u8>,
    window_bytes: u32,
    values: Seq<u8>,
    prefix: nat,
) -> bool {
    forall|tree: int| 0 <= tree < 256 ==>
        #[trigger] byte_has_bit(
            workspace[coverage_bitmap_at(window_bytes, (tree / 8) as u16) as int],
            (tree % 8) as nat,
        ) == value_seen(values, prefix, tree as nat)
}

pub(crate) open spec fn coverage_bitmap_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
) -> bool {
    &&& before.len() == after.len()
    &&& forall|i: int| 0 <= i < before.len()
        && !(window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat
            <= i < window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat + 32)
        ==> #[trigger] after[i] == before[i]
}

proof fn value_seen_step(values: Seq<u8>, prefix: nat, tree: nat)
    requires prefix < values.len(),
    ensures value_seen(values, prefix + 1, tree)
        == (value_seen(values, prefix, tree) || values[prefix as int] as nat == tree),
{
    if value_seen(values, prefix + 1, tree) {
        let witness = choose|i: int| 0 <= i < prefix + 1 && values[i] as nat == tree;
        if witness < prefix {
            assert(value_seen(values, prefix, tree));
        } else {
            assert(witness == prefix);
        }
    }
}

#[verifier::bit_vector]
proof fn set_coverage_bit(value: u8, bit: u8)
    requires bit < 8,
    ensures byte_has_bit(value | (1u8 << bit), bit as nat),
{
}

#[verifier::bit_vector]
proof fn set_coverage_bit_preserves(value: u8, bit: u8, other: u8)
    requires bit < 8, other < 8, bit != other,
    ensures byte_has_bit(value | (1u8 << bit), other as nat)
        == byte_has_bit(value, other as nat),
{
}

#[verifier::bit_vector]
proof fn coverage_bit_exec_matches(value: u8, bit: u8)
    requires bit < 8,
    ensures ((value & (1u8 << bit)) != 0) == byte_has_bit(value, bit as nat),
{
}

pub(crate) fn check_context_tree_coverage(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
    num_htrees: u16,
) -> (r: Result<(bool, u64), WorkspaceError>)
    requires
        active_len <= context_map_capacity(kind),
        1 <= num_htrees <= 256,
        window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= old(workspace)@.len(),
        forall|i: int| 0 <= i < active_len
            ==> #[trigger] old(workspace)@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ]
                < num_htrees,
    ensures r.is_ok() ==> {
        let values = context_map_values(old(workspace)@, window_bytes, kind, active_len);
        &&& r.unwrap().0 == context_tree_coverage(values, num_htrees)
        &&& r.unwrap().1 == 32u64 + 3u64 * active_len as u64 + num_htrees as u64
        &&& coverage_bitmap_represents(
            final(workspace)@,
            window_bytes,
            values,
            active_len as nat,
        )
        &&& context_map_values(final(workspace)@, window_bytes, kind, active_len)
            == values
        &&& coverage_bitmap_frame(old(workspace)@, final(workspace)@, window_bytes)
    },
    r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let ghost original_workspace = workspace@;
    let ghost values = context_map_values(original_workspace, window_bytes, kind, active_len);
    let bitmap_base_u32 = match window_bytes.checked_add(BUILDER_CODE_LENGTHS_OFFSET) {
        Some(value) => value,
        None => return Err(WorkspaceError::InvalidWindowBits),
    };
    proof {
        assert(bitmap_base_u32 as nat
            == window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat);
        assert(bitmap_base_u32 as nat + COVERAGE_BITMAP_BYTES as nat
            <= workspace@.len());
        assert(coverage_bitmap_frame(original_workspace, workspace@, window_bytes));
    }
    let bitmap_base = bitmap_base_u32 as usize;
    let mut cleared: u16 = 0;
    while cleared < COVERAGE_BITMAP_BYTES
        invariant
            cleared <= COVERAGE_BITMAP_BYTES,
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            bitmap_base as nat
                == window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat,
            bitmap_base + COVERAGE_BITMAP_BYTES as usize <= workspace@.len(),
            forall|byte: int| 0 <= byte < cleared
                ==> #[trigger] workspace@[
                    coverage_bitmap_at(window_bytes, byte as u16) as int
                ] == 0,
            coverage_bitmap_frame(original_workspace, workspace@, window_bytes),
        decreases COVERAGE_BITMAP_BYTES - cleared,
    {
        let at = bitmap_base + cleared as usize;
        workspace[at] = 0;
        cleared = cleared + 1;
    }
    proof {
        assert forall|tree: int| 0 <= tree < 256 implies
            #[trigger] byte_has_bit(
                workspace@[
                    coverage_bitmap_at(window_bytes, (tree / 8) as u16) as int
                ],
                (tree % 8) as nat,
            ) == false by {}
        assert(coverage_bitmap_represents(workspace@, window_bytes, values, 0));
    }
    let mut index: u16 = 0;
    while index < active_len
        invariant
            index <= active_len,
            active_len <= context_map_capacity(kind),
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= workspace@.len(),
            bitmap_base as nat
                == window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat,
            bitmap_base + COVERAGE_BITMAP_BYTES as usize <= workspace@.len(),
            context_map_values(workspace@, window_bytes, kind, active_len) == values,
            coverage_bitmap_represents(workspace@, window_bytes, values, index as nat),
            coverage_bitmap_frame(original_workspace, workspace@, window_bytes),
        decreases active_len - index,
    {
        let map_at = match context_entry_offset(window_bytes, kind, index) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let value = workspace[map_at];
        proof {
            assert(value == values[index as int]);
        }
        let byte = value / 8;
        let bit = value % 8;
        let bitmap_at = bitmap_base + byte as usize;
        let old_bitmap = workspace[bitmap_at];
        let ghost before_bitmap = workspace@;
        workspace[bitmap_at] = old_bitmap | (1u8 << bit);
        proof {
            bitmap_update_preserves_context_map(
                before_bitmap,
                workspace@,
                window_bytes,
                kind,
                active_len,
                byte as u16,
                old_bitmap | (1u8 << bit),
            );
            set_coverage_bit(old_bitmap, bit);
            assert(context_map_values(workspace@, window_bytes, kind, active_len) == values);
            assert forall|tree: int| 0 <= tree < 256 implies
                #[trigger] byte_has_bit(
                    workspace@[
                        coverage_bitmap_at(window_bytes, (tree / 8) as u16) as int
                    ],
                    (tree % 8) as nat,
                ) == value_seen(values, index as nat + 1, tree as nat) by {
                value_seen_step(values, index as nat, tree as nat);
                if tree != value {
                    if tree / 8 == value as int / 8 {
                        set_coverage_bit_preserves(old_bitmap, bit, (tree % 8) as u8);
                    } else {
                        assert(coverage_bitmap_at(window_bytes, (tree / 8) as u16)
                            != coverage_bitmap_at(window_bytes, byte as u16));
                        assert(workspace@[
                            coverage_bitmap_at(window_bytes, (tree / 8) as u16) as int
                        ] == before_bitmap[
                            coverage_bitmap_at(window_bytes, (tree / 8) as u16) as int
                        ]);
                    }
                } else {
                    assert(tree as nat == value as nat);
                }
            }
        }
        index = index + 1;
    }
    let mut complete = true;
    let mut tree: u16 = 0;
    while tree < num_htrees
        invariant
            tree <= num_htrees <= 256,
            bitmap_base as nat
                == window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat,
            bitmap_base + COVERAGE_BITMAP_BYTES as usize <= workspace@.len(),
            complete ==> (forall|t: int| 0 <= t < tree
                ==> #[trigger] value_seen(values, active_len as nat, t as nat)),
            !complete ==> (exists|t: int| 0 <= t < tree
                && !#[trigger] value_seen(values, active_len as nat, t as nat)),
            coverage_bitmap_represents(workspace@, window_bytes, values, active_len as nat),
        decreases num_htrees - tree,
    {
        let ghost old_tree = tree;
        let ghost old_complete = complete;
        let byte = tree / 8;
        let bit = (tree % 8) as u8;
        let bitmap_at = bitmap_base + byte as usize;
        let present = workspace[bitmap_at] & (1u8 << bit) != 0;
        proof {
            assert(bitmap_at as nat == coverage_bitmap_at(window_bytes, byte));
            assert(byte as nat == tree as nat / 8);
            assert(bit as nat == tree as nat % 8);
            reveal(coverage_bitmap_represents);
            assert(byte_has_bit(
                workspace@[
                    coverage_bitmap_at(
                        window_bytes,
                        ((tree as int) / 8) as u16,
                    ) as int
                ],
                ((tree as int) % 8) as nat,
            ) == value_seen(values, active_len as nat, tree as nat));
            coverage_bit_exec_matches(workspace@[bitmap_at as int], bit);
            assert(byte_has_bit(
                workspace@[coverage_bitmap_at(window_bytes, byte) as int],
                bit as nat,
            ) == value_seen(values, active_len as nat, tree as nat));
            assert(present == value_seen(values, active_len as nat, tree as nat));
        }
        complete = complete && present;
        tree = tree + 1;
        proof {
            assert(complete == (old_complete
                && value_seen(values, active_len as nat, old_tree as nat)));
            if complete {
                assert forall|t: int| 0 <= t < tree implies
                    #[trigger] value_seen(values, active_len as nat, t as nat) by {
                    if t < old_tree {
                        assert(old_complete);
                    } else {
                        assert(t == old_tree);
                    }
                }
            } else if old_complete {
                assert(!value_seen(values, active_len as nat, old_tree as nat));
                assert(0 <= (old_tree as int) < (tree as int));
                assert(exists|t: int| 0 <= t < tree
                    && !#[trigger] value_seen(values, active_len as nat, t as nat)) by {
                    let witness = old_tree as int;
                    assert(0 <= witness < tree);
                    assert(!value_seen(values, active_len as nat, witness as nat));
                }
            } else {
                let missing = choose|t: int| 0 <= t < old_tree
                    && !#[trigger] value_seen(values, active_len as nat, t as nat);
                assert(0 <= missing < tree);
                assert(!value_seen(values, active_len as nat, missing as nat));
                assert(exists|t: int| 0 <= t < tree
                    && !#[trigger] value_seen(values, active_len as nat, t as nat));
                }
        }
    }
    proof {
        reveal(context_tree_coverage);
        assert(complete == context_tree_coverage(values, num_htrees));
    }
    Ok((complete, 32u64 + 3u64 * active_len as u64 + num_htrees as u64))
}

pub(crate) open spec fn mtf_list_at(window_bytes: u32, index: u16) -> nat {
    window_bytes as nat + MTF_LIST_OFFSET as nat + index as nat
}

pub(crate) open spec fn mtf_scratch_at(window_bytes: u32) -> nat {
    window_bytes as nat + MTF_OFFSET as nat + 3
}

pub(crate) open spec fn mtf_list_values(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> Seq<u8> {
    Seq::new(256, |i: int| workspace[mtf_list_at(window_bytes, i as u16) as int])
}

proof fn mtf_list_values_index(workspace: Seq<u8>, window_bytes: u32, index: u16)
    requires
        index < 256,
        window_bytes as nat + MTF_LIST_OFFSET as nat + 256 <= workspace.len(),
    ensures mtf_list_values(workspace, window_bytes)[index as int]
        == workspace[mtf_list_at(window_bytes, index) as int],
{
}

proof fn context_map_values_index(
    workspace: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
    index: u16,
)
    requires
        index < active_len,
        window_bytes as nat + context_map_offset(kind) + active_len as nat
            <= workspace.len(),
    ensures context_map_values(workspace, window_bytes, kind, active_len)[index as int]
        == workspace[context_entry_at(window_bytes, kind, index) as int],
{
}

pub(crate) open spec fn mtf_identity() -> Seq<u8> {
    Seq::new(256, |i: int| i as u8)
}

pub(crate) open spec fn mtf_move_front(list: Seq<u8>, rank: u8) -> Seq<u8> {
    Seq::new(256, |i: int|
        if i == 0 { list[rank as int] }
        else if i <= rank { list[i - 1] }
        else { list[i] })
}

pub(crate) open spec fn mtf_output_values(ranks: Seq<u8>, list: Seq<u8>) -> Seq<u8>
    decreases ranks.len(),
{
    if ranks.len() == 0 {
        Seq::empty()
    } else {
        seq![list[ranks[0] as int]]
            + mtf_output_values(ranks.skip(1), mtf_move_front(list, ranks[0]))
    }
}

pub(crate) open spec fn mtf_final_list(ranks: Seq<u8>, list: Seq<u8>) -> Seq<u8>
    decreases ranks.len(),
{
    if ranks.len() == 0 {
        list
    } else {
        mtf_final_list(ranks.skip(1), mtf_move_front(list, ranks[0]))
    }
}

pub(crate) open spec fn mtf_prefix_or(ranks: Seq<u8>, prefix: nat) -> u8
    decreases prefix,
{
    if prefix == 0 { 0 }
    else { mtf_prefix_or(ranks, (prefix - 1) as nat) | ranks[prefix as int - 1] }
}

pub(crate) open spec fn mtf_rank_or(ranks: Seq<u8>) -> u8 {
    mtf_prefix_or(ranks, ranks.len())
}

pub(crate) open spec fn mtf_rank_work(ranks: Seq<u8>) -> nat
    decreases ranks.len(),
{
    if ranks.len() == 0 {
        0
    } else {
        2 * ranks[0] as nat + 6 + mtf_rank_work(ranks.skip(1))
    }
}

pub(crate) open spec fn mtf_list_distinct(list: Seq<u8>) -> bool {
    &&& list.len() == 256
    &&& forall|i: int, j: int| 0 <= i < j < 256 ==> list[i] != list[j]
}

pub(crate) open spec fn mtf_reusable(list: Seq<u8>, upper_bound: u8) -> bool {
    &&& upper_bound <= 63
    &&& mtf_list_distinct(list)
    &&& forall|i: int| 4 * (upper_bound as int + 1) <= i < 256
        ==> #[trigger] list[i] == i as u8
}

pub(crate) open spec fn mtf_workspace_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
) -> bool {
    &&& before.len() == after.len()
    &&& forall|i: int| 0 <= i < before.len() ==> {
        let map_start = window_bytes as nat + context_map_offset(kind);
        let map_end = map_start + active_len as nat;
        let mtf_start = mtf_scratch_at(window_bytes);
        let mtf_end = window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat;
        !(map_start <= i < map_end || mtf_start <= i < mtf_end)
            ==> #[trigger] after[i] == before[i]
    }
}

proof fn mtf_identity_distinct()
    ensures mtf_list_distinct(mtf_identity()),
{
    reveal(mtf_list_distinct);
}

proof fn mtf_move_front_preserves_distinct(list: Seq<u8>, rank: u8)
    requires mtf_list_distinct(list),
    ensures mtf_list_distinct(mtf_move_front(list, rank)),
{
    reveal(mtf_list_distinct);
    assert forall|i: int, j: int| 0 <= i < j < 256 implies
        mtf_move_front(list, rank)[i] != mtf_move_front(list, rank)[j] by {
        if i == 0 {
            if j <= rank {
                assert(j - 1 < rank);
            } else {
                assert(rank < j);
            }
        } else if i <= rank {
            if j <= rank {
                assert(i - 1 < j - 1);
            } else {
                assert(i - 1 < j);
            }
        }
    }
}

proof fn mtf_prefix_or_contains(ranks: Seq<u8>, prefix: nat, index: int)
    requires 0 <= index < prefix <= ranks.len(),
    ensures (ranks[index] | mtf_prefix_or(ranks, prefix)) == mtf_prefix_or(ranks, prefix),
    decreases prefix,
{
    if index < prefix - 1 {
        mtf_prefix_or_contains(ranks, (prefix - 1) as nat, index);
        mtf_or_absorb_append(
            ranks[index],
            mtf_prefix_or(ranks, (prefix - 1) as nat),
            ranks[prefix as int - 1],
        );
    } else {
        assert(index == prefix - 1);
        mtf_or_last_absorbs(
            ranks[index],
            mtf_prefix_or(ranks, (prefix - 1) as nat),
        );
    }
    reveal_with_fuel(mtf_prefix_or, 2);
}

#[verifier::bit_vector]
proof fn mtf_or_absorb_append(value: u8, prefix: u8, last: u8)
    requires value | prefix == prefix,
    ensures value | (prefix | last) == prefix | last,
{
}

#[verifier::bit_vector]
proof fn mtf_or_last_absorbs(last: u8, prefix: u8)
    ensures last | (prefix | last) == prefix | last,
{
}

proof fn mtf_or_contains_rank(ranks: Seq<u8>, index: int)
    requires 0 <= index < ranks.len(),
    ensures (ranks[index] | mtf_rank_or(ranks)) == mtf_rank_or(ranks),
{
    mtf_prefix_or_contains(ranks, ranks.len(), index);
}

#[verifier::bit_vector]
proof fn mtf_or_head_absorbs(head: u8, tail: u8)
    ensures head | (head | tail) == head | tail,
{
}

#[verifier::bit_vector]
proof fn mtf_or_absorb_through_head(value: u8, head: u8, tail: u8)
    requires value | tail == tail,
    ensures value | (head | tail) == head | tail,
{
}

#[verifier::bit_vector]
proof fn mtf_or_is_at_least(value: u8, combined: u8)
    requires value | combined == combined,
    ensures value <= combined,
{
}

spec fn mtf_region_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
) -> bool {
    &&& before.len() == after.len()
    &&& forall|i: int| 0 <= i < before.len()
        && !(mtf_scratch_at(window_bytes) <= i
            < window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat)
        ==> #[trigger] after[i] == before[i]
}

#[verifier::bit_vector]
proof fn mtf_list_offset_fits_u32(window_bytes: u32, index: u16)
    requires window_bytes <= 16_777_216, index < 256,
    ensures window_bytes as nat + MTF_LIST_OFFSET as nat + index as nat <= u32::MAX,
{
}

proof fn mtf_region_frame_after_update(
    original: Seq<u8>,
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    at: int,
    value: u8,
)
    requires
        mtf_region_frame(original, before, window_bytes),
        mtf_scratch_at(window_bytes) <= at
            < window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat,
        0 <= at < before.len(),
        after == before.update(at, value),
    ensures mtf_region_frame(original, after, window_bytes),
{
    reveal(mtf_region_frame);
}

proof fn mtf_workspace_frame_after_update(
    original: Seq<u8>,
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
    at: int,
    value: u8,
)
    requires
        mtf_workspace_frame(original, before, window_bytes, kind, active_len),
        0 <= at < before.len(),
        {
            let map_start = window_bytes as nat + context_map_offset(kind);
            let map_end = map_start + active_len as nat;
            let mtf_start = mtf_scratch_at(window_bytes);
            let mtf_end = window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat;
            &&& map_start <= at < map_end || mtf_start <= at < mtf_end
        },
        after == before.update(at, value),
    ensures mtf_workspace_frame(original, after, window_bytes, kind, active_len),
{
    reveal(mtf_workspace_frame);
}

proof fn mtf_workspace_frame_after_mtf_region(
    original: Seq<u8>,
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
)
    requires
        mtf_workspace_frame(original, before, window_bytes, kind, active_len),
        mtf_region_frame(before, after, window_bytes),
    ensures mtf_workspace_frame(original, after, window_bytes, kind, active_len),
{
    reveal(mtf_workspace_frame);
    reveal(mtf_region_frame);
}

fn mtf_move_rank(
    workspace: &mut [u8],
    window_bytes: u32,
    rank: u8,
) -> (r: u8)
    requires
        window_bytes <= 16_777_216,
        window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= old(workspace)@.len(),
    ensures
        r == mtf_list_values(old(workspace)@, window_bytes)[rank as int],
        final(workspace)@[mtf_scratch_at(window_bytes) as int] == r,
        mtf_list_values(final(workspace)@, window_bytes)
            == mtf_move_front(mtf_list_values(old(workspace)@, window_bytes), rank),
        mtf_region_frame(old(workspace)@, final(workspace)@, window_bytes),
{
    let ghost before = workspace@;
    let ghost old_list = mtf_list_values(before, window_bytes);
    let list_base = (window_bytes + MTF_LIST_OFFSET) as usize;
    let scratch = (window_bytes + MTF_OFFSET + 3) as usize;
    proof {
        fixed_layout_is_exact();
        assert(scratch + 1 == list_base);
        assert(list_base as nat == window_bytes as nat + MTF_LIST_OFFSET as nat);
        assert(list_base as nat + 256
            == window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat);
        assert(list_base + 256 <= workspace@.len());
        assert(window_bytes as nat + MTF_LIST_OFFSET as nat + 256 <= before.len());
        assert(mtf_region_frame(before, workspace@, window_bytes));
        mtf_list_values_index(before, window_bytes, rank as u16);
    }
    let value = workspace[list_base + rank as usize];
    let ghost before_scratch = workspace@;
    workspace[scratch] = value;
    proof {
        mtf_region_frame_after_update(
            before,
            before_scratch,
            workspace@,
            window_bytes,
            scratch as int,
            value,
        );
    }
    let mut cursor: u16 = rank as u16;
    while cursor > 0
        invariant
            cursor <= rank,
            window_bytes <= 16_777_216,
            workspace@.len() == before.len(),
            scratch + 1 == list_base,
            list_base as nat == window_bytes as nat + MTF_LIST_OFFSET as nat,
            list_base as nat + 256
                == window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat,
            list_base + 256 <= workspace@.len(),
            workspace@[scratch as int] == value,
            value == old_list[rank as int],
            forall|i: int| 0 <= i <= cursor
                ==> #[trigger] workspace@[(list_base + i) as int] == old_list[i],
            forall|i: int| cursor < i <= rank
                ==> #[trigger] workspace@[(list_base + i) as int] == old_list[i - 1],
            forall|i: int| rank < i < 256
                ==> #[trigger] workspace@[(list_base + i) as int] == old_list[i],
            mtf_region_frame(before, workspace@, window_bytes),
        decreases cursor,
    {
        let ghost old_cursor = cursor;
        let ghost before_write = workspace@;
        let source_index = (cursor - 1) as usize;
        proof {
            assert(0 <= old_cursor as int - 1 <= cursor);
            assert(source_index as int == old_cursor as int - 1);
            assert(source_index < 256);
        }
        proof {
            mtf_list_offset_fits_u32(window_bytes, source_index as u16);
        }
        let source_at = (window_bytes + MTF_LIST_OFFSET + source_index as u32) as usize;
        proof {
            assert(source_at == list_base + source_index);
            assert(source_at < workspace@.len());
        }
        let source = workspace[source_at];
        proof {
            assert(source_at == list_base + source_index);
            assert(before_write[source_at as int]
                == old_list[source_index as int]);
        }
        workspace[list_base + cursor as usize] = source;
        cursor = cursor - 1;
        proof {
            assert(source == old_list[old_cursor as int - 1]);
            assert(workspace@[scratch as int] == value);
            assert forall|i: int| cursor < i <= rank implies
                #[trigger] workspace@[(list_base + i) as int] == old_list[i - 1] by {
                if i == old_cursor {
                    assert(workspace@[(list_base + i) as int] == source);
                } else {
                    assert(before_write[(list_base + i) as int] == old_list[i - 1]);
                }
            }
            let dest_at = (list_base + old_cursor as usize) as int;
            let mtf_end = window_bytes as int + MTF_OFFSET as int + MTF_BYTES as int;
            assert((mtf_scratch_at(window_bytes) as int) <= dest_at);
            assert(dest_at < mtf_end);
            mtf_region_frame_after_update(
                before,
                before_write,
                workspace@,
                window_bytes,
                (list_base + old_cursor as usize) as int,
                source,
            );
        }
    }
    let front = workspace[scratch];
    let ghost before_front = workspace@;
    workspace[list_base] = front;
    proof {
        mtf_region_frame_after_update(
            before,
            before_front,
            workspace@,
            window_bytes,
            list_base as int,
            front,
        );
        assert(mtf_list_values(workspace@, window_bytes) =~= mtf_move_front(old_list, rank));
    }
    value
}

proof fn mtf_append_one(ranks: Seq<u8>, list: Seq<u8>, rank: u8)
    ensures
        mtf_final_list(ranks + seq![rank], list)
            == mtf_move_front(mtf_final_list(ranks, list), rank),
        mtf_output_values(ranks + seq![rank], list)
            == mtf_output_values(ranks, list)
                + seq![mtf_final_list(ranks, list)[rank as int]],
        mtf_rank_work(ranks + seq![rank]) == mtf_rank_work(ranks) + 2 * rank as nat + 6,
    decreases ranks.len(),
{
    if ranks.len() > 0 {
        mtf_append_one(ranks.skip(1), mtf_move_front(list, ranks[0]), rank);
        assert((ranks + seq![rank]).skip(1) =~= ranks.skip(1) + seq![rank]);
        reveal_with_fuel(mtf_final_list, 2);
        reveal_with_fuel(mtf_output_values, 2);
        reveal_with_fuel(mtf_rank_work, 2);
    } else {
        assert(ranks =~= Seq::<u8>::empty());
        reveal_with_fuel(mtf_final_list, 2);
        reveal_with_fuel(mtf_output_values, 2);
        reveal_with_fuel(mtf_rank_work, 2);
    }
}

#[verifier::bit_vector]
proof fn mtf_or_append_associative(head: u8, tail: u8, last: u8)
    ensures head | (tail | last) == (head | tail) | last,
{
}

proof fn mtf_final_list_distinct(ranks: Seq<u8>, list: Seq<u8>)
    requires mtf_list_distinct(list),
    ensures mtf_list_distinct(mtf_final_list(ranks, list)),
    decreases ranks.len(),
{
    if ranks.len() > 0 {
        mtf_move_front_preserves_distinct(list, ranks[0]);
        mtf_final_list_distinct(ranks.skip(1), mtf_move_front(list, ranks[0]));
    }
}

proof fn mtf_move_front_preserves_suffix(list: Seq<u8>, rank: u8, start: nat)
    requires list.len() == 256, (rank as nat) < start <= 256,
    ensures forall|i: int| start <= i < 256
        ==> #[trigger] mtf_move_front(list, rank)[i] == list[i],
{
}

proof fn mtf_final_list_preserves_suffix(ranks: Seq<u8>, list: Seq<u8>, start: nat)
    requires
        list.len() == 256,
        start <= 256,
        forall|j: int| 0 <= j < ranks.len() ==> (ranks[j] as nat) < start,
    ensures forall|i: int| start <= i < 256
        ==> #[trigger] mtf_final_list(ranks, list)[i] == list[i],
    decreases ranks.len(),
{
    if ranks.len() > 0 {
        mtf_move_front_preserves_suffix(list, ranks[0], start);
        assert forall|j: int| 0 <= j < ranks.skip(1).len()
            implies (ranks.skip(1)[j] as nat) < start by {}
        mtf_final_list_preserves_suffix(ranks.skip(1), mtf_move_front(list, ranks[0]), start);
        reveal_with_fuel(mtf_final_list, 2);
        assert forall|i: int| start <= i < 256 implies
            #[trigger] mtf_final_list(ranks, list)[i] == list[i] by {
            assert(mtf_final_list(
                ranks.skip(1),
                mtf_move_front(list, ranks[0]),
            )[i] == mtf_move_front(list, ranks[0])[i]);
            assert(mtf_move_front(list, ranks[0])[i] == list[i]);
        }
    } else {
        reveal_with_fuel(mtf_final_list, 2);
    }
}

#[verifier::bit_vector]
proof fn mtf_rank_below_returned_boundary(rank: u8, combined: u8)
    requires rank | combined == combined,
    ensures (rank as nat) < 4 * ((combined >> 2) as nat + 1),
{
}

#[verifier::bit_vector]
proof fn mtf_returned_bound_is_valid(combined: u8)
    ensures (combined >> 2) <= 63,
{
}

spec fn mtf_prefix_bounded(list: Seq<u8>, num_htrees: u16) -> bool {
    &&& list.len() == 256
    &&& 1 <= num_htrees <= 256
    &&& forall|i: int| 0 <= i < num_htrees ==> list[i] < num_htrees
}

proof fn mtf_identity_prefix_bounded(num_htrees: u16)
    requires 1 <= num_htrees <= 256,
    ensures mtf_prefix_bounded(mtf_identity(), num_htrees),
{
    reveal(mtf_prefix_bounded);
}

proof fn mtf_move_front_prefix_bounded(list: Seq<u8>, rank: u8, num_htrees: u16)
    requires mtf_prefix_bounded(list, num_htrees), rank < num_htrees,
    ensures mtf_prefix_bounded(mtf_move_front(list, rank), num_htrees),
{
    reveal(mtf_prefix_bounded);
    assert forall|i: int| 0 <= i < num_htrees implies
        #[trigger] mtf_move_front(list, rank)[i] < num_htrees by {
        if i == 0 {
        } else if i <= rank {
            assert(0 <= i - 1 < num_htrees);
        }
    }
}

proof fn mtf_output_stays_bounded(ranks: Seq<u8>, list: Seq<u8>, num_htrees: u16)
    requires
        mtf_prefix_bounded(list, num_htrees),
        forall|i: int| 0 <= i < ranks.len() ==> ranks[i] < num_htrees,
    ensures
        forall|i: int| 0 <= i < mtf_output_values(ranks, list).len()
            ==> #[trigger] mtf_output_values(ranks, list)[i] < num_htrees,
        mtf_prefix_bounded(mtf_final_list(ranks, list), num_htrees),
    decreases ranks.len(),
{
    if ranks.len() > 0 {
        mtf_move_front_prefix_bounded(list, ranks[0], num_htrees);
        assert forall|i: int| 0 <= i < ranks.skip(1).len()
            implies ranks.skip(1)[i] < num_htrees by {}
        mtf_output_stays_bounded(
            ranks.skip(1),
            mtf_move_front(list, ranks[0]),
            num_htrees,
        );
        reveal_with_fuel(mtf_output_values, 2);
        reveal_with_fuel(mtf_final_list, 2);
        assert(list[ranks[0] as int] < num_htrees);
        assert forall|i: int| 0 <= i < mtf_output_values(ranks, list).len()
            implies #[trigger] mtf_output_values(ranks, list)[i] < num_htrees by {
            if i > 0 {
                assert(mtf_output_values(ranks, list)[i]
                    == mtf_output_values(
                        ranks.skip(1),
                        mtf_move_front(list, ranks[0]),
                    )[i - 1]);
            }
        }
    }
}

pub(crate) fn inverse_mtf_context_map(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: ContextMapKind,
    active_len: u16,
    num_htrees: u16,
    mtf_upper_bound: u8,
) -> (r: Result<(u8, u64), WorkspaceError>)
    requires
        active_len <= context_map_capacity(kind),
        1 <= num_htrees <= 256,
        window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= old(workspace)@.len(),
        forall|i: int| 0 <= i < active_len
            ==> #[trigger] old(workspace)@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ] < num_htrees,
        mtf_upper_bound <= 63,
        mtf_upper_bound == 63
            || mtf_reusable(mtf_list_values(old(workspace)@, window_bytes), mtf_upper_bound),
    ensures
        r.is_ok() ==> {
            let ranks = context_map_values(old(workspace)@, window_bytes, kind, active_len);
            let next_bound = mtf_rank_or(ranks) >> 2;
            &&& r.unwrap().0 == next_bound
            &&& r.unwrap().1 as nat
                == 4 * (mtf_upper_bound as nat + 1) + mtf_rank_work(ranks)
            &&& context_map_values(final(workspace)@, window_bytes, kind, active_len)
                == mtf_output_values(ranks, mtf_identity())
            &&& forall|i: int| 0 <= i < active_len
                ==> #[trigger] final(workspace)@[
                    context_entry_at(window_bytes, kind, i as u16) as int
                ] < num_htrees
            &&& mtf_list_values(final(workspace)@, window_bytes)
                == mtf_final_list(ranks, mtf_identity())
            &&& mtf_reusable(
                mtf_list_values(final(workspace)@, window_bytes),
                next_bound,
            )
            &&& mtf_workspace_frame(
                old(workspace)@,
                final(workspace)@,
                window_bytes,
                kind,
                active_len,
            )
        },
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let ghost original_workspace = workspace@;
    let ghost ranks = context_map_values(original_workspace, window_bytes, kind, active_len);
    let list_base = (window_bytes + MTF_LIST_OFFSET) as usize;
    let init_limit: u16 = 4 * (mtf_upper_bound as u16 + 1);
    proof {
        assert(mtf_upper_bound <= 63);
        assert(init_limit as nat == 4 * (mtf_upper_bound as nat + 1));
        assert(init_limit <= 256);
        fixed_layout_is_exact();
        assert(list_base as nat == window_bytes as nat + MTF_LIST_OFFSET as nat);
        assert(list_base as nat + 256
            == window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat);
        assert(list_base + 256 <= workspace@.len());
        if mtf_upper_bound < 63 {
            reveal(mtf_reusable);
            reveal(mtf_list_values);
            assert forall|i: int| init_limit <= i < 256 implies
                #[trigger] workspace@[(list_base + i) as int] == i as u8 by {
                mtf_list_values_index(original_workspace, window_bytes, i as u16);
            }
        } else {
            assert(init_limit == 256);
        }
        assert(mtf_workspace_frame(
            original_workspace,
            workspace@,
            window_bytes,
            kind,
            active_len,
        ));
        assert(mtf_region_frame(original_workspace, workspace@, window_bytes));
    }
    let mut init: u16 = 0;
    while init < init_limit
        invariant
            init <= init_limit <= 256,
            init_limit == 4 * (mtf_upper_bound as u16 + 1),
            mtf_upper_bound <= 63,
            workspace@.len() == original_workspace.len(),
            list_base + 256 <= workspace@.len(),
            list_base as nat == window_bytes as nat + MTF_LIST_OFFSET as nat,
            list_base as nat + 256
                == window_bytes as nat + MTF_OFFSET as nat + MTF_BYTES as nat,
            window_bytes <= 16_777_216,
            window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= workspace@.len(),
            forall|i: int| 0 <= i < init
                ==> #[trigger] workspace@[(list_base + i) as int] == i as u8,
            forall|i: int| init_limit <= i < 256
                ==> #[trigger] workspace@[(list_base + i) as int] == i as u8,
            mtf_workspace_frame(
                original_workspace,
                workspace@,
                window_bytes,
                kind,
                active_len,
            ),
            mtf_region_frame(original_workspace, workspace@, window_bytes),
        decreases init_limit - init,
    {
        let ghost before_init_write = workspace@;
        workspace[list_base + init as usize] = init as u8;
        init = init + 1;
        proof {
            let dest_at = (list_base + init as usize - 1) as int;
            let mtf_end = window_bytes as int + MTF_OFFSET as int + MTF_BYTES as int;
            assert((mtf_scratch_at(window_bytes) as int) <= dest_at);
            assert(dest_at < mtf_end);
            mtf_region_frame_after_update(
                original_workspace,
                before_init_write,
                workspace@,
                window_bytes,
                (list_base + init as usize - 1) as int,
                (init - 1) as u8,
            );
            mtf_workspace_frame_after_update(
                original_workspace,
                before_init_write,
                workspace@,
                window_bytes,
                kind,
                active_len,
                (list_base + init as usize - 1) as int,
                (init - 1) as u8,
            );
        }
    }
    proof {
        assert(mtf_list_values(workspace@, window_bytes) =~= mtf_identity());
        mtf_identity_distinct();
        assert(ranks.len() == active_len);
        assert forall|i: int| 0 <= i < active_len implies
            #[trigger] workspace@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ] == ranks[i] by {
            context_map_values_index(original_workspace, window_bytes, kind, active_len, i as u16);
            assert(workspace@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ] == original_workspace[
                context_entry_at(window_bytes, kind, i as u16) as int
            ]);
        }
        assert(context_map_suffix_matches(
            workspace@,
            window_bytes,
            kind,
            ranks,
            0,
        ));
    }
    let ghost initialized_workspace = workspace@;
    let mut index: u16 = 0;
    let mut rank_or: u8 = 0;
    let mut work: u64 = init_limit as u64;
    while index < active_len
        invariant
            index <= active_len,
            active_len <= context_map_capacity(kind),
            ranks.len() == active_len,
            init_limit <= 256,
            workspace@.len() == original_workspace.len(),
            window_bytes <= 16_777_216,
            window_bytes as nat + FIXED_SCRATCH_BYTES as nat <= workspace@.len(),
            context_map_values(workspace@, window_bytes, kind, index)
                == mtf_output_values(ranks.take(index as int), mtf_identity()),
            context_map_suffix_matches(
                workspace@,
                window_bytes,
                kind,
                ranks,
                index as nat,
            ),
            mtf_list_values(workspace@, window_bytes)
                == mtf_final_list(ranks.take(index as int), mtf_identity()),
            rank_or == mtf_prefix_or(ranks, index as nat),
            work as nat == init_limit as nat + mtf_rank_work(ranks.take(index as int)),
            work <= init_limit as u64 + 516 * index as u64,
            work <= 8_454_400,
            mtf_workspace_frame(
                original_workspace,
                workspace@,
                window_bytes,
                kind,
                active_len,
            ),
        decreases active_len - index,
    {
        let ghost old_index = index;
        let ghost before_move = workspace@;
        let map_at = match context_entry_offset(window_bytes, kind, index) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let rank = workspace[map_at];
        proof {
            assert(index < active_len);
            assert((index as int) < ranks.len());
            context_map_values_index(original_workspace, window_bytes, kind, active_len, index);
            reveal(context_map_suffix_matches);
            context_map_suffix_index(
                workspace@,
                window_bytes,
                kind,
                ranks,
                index as nat,
                index as int,
            );
            assert(workspace@[
                context_entry_at(window_bytes, kind, index) as int
            ] == ranks[index as int]);
            assert(map_at as nat == context_entry_at(window_bytes, kind, index));
            assert(rank == ranks[index as int]);
        }
        let value = mtf_move_rank(workspace, window_bytes, rank);
        let ghost after_move = workspace@;
        proof {
            mtf_workspace_frame_after_mtf_region(
                original_workspace,
                before_move,
                after_move,
                window_bytes,
                kind,
                active_len,
            );
        }
        workspace[map_at] = value;
        proof {
            mtf_workspace_frame_after_update(
                original_workspace,
                after_move,
                workspace@,
                window_bytes,
                kind,
                active_len,
                map_at as int,
                value,
            );
            assert(context_map_suffix_matches(
                workspace@,
                window_bytes,
                kind,
                ranks,
                index as nat + 1,
            ));
        }
        rank_or = rank_or | rank;
        work = work + 2 * rank as u64 + 6;
        index = index + 1;
        proof {
            assert(old_index < ranks.len());
            mtf_append_one(ranks.take(old_index as int), mtf_identity(), rank);
            assert(ranks.take(index as int).len() == index);
            assert(ranks.take(index as int)
                =~= ranks.take(old_index as int) + seq![rank]);
            assert(context_map_values(workspace@, window_bytes, kind, index)
                == mtf_output_values(ranks.take(index as int), mtf_identity()));
            assert(mtf_list_values(workspace@, window_bytes)
                == mtf_final_list(ranks.take(index as int), mtf_identity()));
            reveal_with_fuel(mtf_prefix_or, 2);
            assert(rank_or == mtf_prefix_or(ranks, index as nat));
            assert(work as nat
                == init_limit as nat + mtf_rank_work(ranks.take(index as int)));
            assert(work <= init_limit as u64 + 516 * index as u64);
            assert(init_limit <= 256);
            assert(active_len <= 16_384);
            assert(work <= 8_454_400);
            assert(mtf_workspace_frame(
                original_workspace,
                before_move,
                window_bytes,
                kind,
                active_len,
            ));
        }
    }
    let next_bound = rank_or >> 2;
    proof {
        assert(ranks.take(index as int) =~= ranks);
        assert(index as nat == ranks.len());
        assert(rank_or == mtf_rank_or(ranks));
        mtf_identity_prefix_bounded(num_htrees);
        assert forall|i: int| 0 <= i < ranks.len() implies ranks[i] < num_htrees by {
            context_map_values_index(
                original_workspace,
                window_bytes,
                kind,
                active_len,
                i as u16,
            );
        }
        mtf_output_stays_bounded(ranks, mtf_identity(), num_htrees);
        mtf_final_list_distinct(ranks, mtf_identity());
        mtf_returned_bound_is_valid(rank_or);
        assert(next_bound <= 63);
        assert forall|j: int| 0 <= j < ranks.len() implies
            (ranks[j] as nat) < 4 * (next_bound as nat + 1) by {
            mtf_or_contains_rank(ranks, j);
            mtf_rank_below_returned_boundary(ranks[j], mtf_rank_or(ranks));
        }
        mtf_final_list_preserves_suffix(
            ranks,
            mtf_identity(),
            4 * (next_bound as nat + 1),
        );
        assert(mtf_reusable(mtf_list_values(workspace@, window_bytes), next_bound));
        assert forall|i: int| 0 <= i < active_len implies
            #[trigger] workspace@[
                context_entry_at(window_bytes, kind, i as u16) as int
            ] < num_htrees by {
            context_map_values_index(workspace@, window_bytes, kind, active_len, i as u16);
            assert(context_map_values(workspace@, window_bytes, kind, active_len)[i]
                == mtf_output_values(ranks, mtf_identity())[i]);
        }
    }
    Ok((next_bound, work))
}

pub(crate) fn write_next_tree_record(
    workspace: &mut [u8],
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    meta: &mut TreeMetadata,
    record: TreeRecord,
) -> (r: Result<(), WorkspaceError>)
    requires old(meta).valid_for(region),
    ensures
    window_bytes <= 16_777_216
        && old(workspace)@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        ==> builder_next_code_byte_sequence(final(workspace)@, window_bytes)
            == builder_next_code_byte_sequence(old(workspace)@, window_bytes),
    window_bytes <= 16_777_216
        && old(workspace)@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        ==> builder_count_byte_sequence(final(workspace)@, window_bytes)
            == builder_count_byte_sequence(old(workspace)@, window_bytes),
    window_bytes <= 16_777_216
        && old(workspace)@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        ==> builder_length_sequence(
            final(workspace)@,
            window_bytes,
            BUILDER_CODE_LENGTHS,
        ) == builder_length_sequence(
            old(workspace)@,
            window_bytes,
            BUILDER_CODE_LENGTHS,
        ),
    window_bytes <= 16_777_216
        && old(workspace)@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        && tree < tree_region_count(region)
        && record.length <= MAX_BITS
        && match old(meta).storage {
            TreeStorageState::Canonical { initialized } => initialized < old(meta).symbols,
            _ => false,
        }
        ==> r.is_ok(),
    r.is_ok() ==> {
        &&& final(meta).valid_for(region)
        &&& final(meta).symbols == old(meta).symbols
        &&& match old(meta).storage {
            TreeStorageState::Canonical { initialized } => {
                let at = tree_record_at(window_bytes, region, tree, initialized);
                let low = (record.code % 256) as u8;
                let high = (record.code / 256) as u8;
                &&& final(meta).storage == TreeStorageState::Canonical {
                    initialized: (initialized as int + 1) as u16,
                }
                &&& at + 3 <= old(workspace)@.len()
                &&& final(workspace)@ == old(workspace)@
                    .update(at as int, record.length)
                    .update(at as int + 1, low)
                    .update(at as int + 2, high)
            },
            _ => false,
        }
    },
    r.is_err() ==> {
        &&& final(workspace)@ == old(workspace)@
        &&& *final(meta) == *old(meta)
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if record.length > MAX_BITS {
        return Err(WorkspaceError::InvalidCodeLength);
    }
    let initialized = match meta.storage {
        TreeStorageState::Canonical { initialized } => initialized,
        _ => return Err(WorkspaceError::UninitializedRecord),
    };
    if initialized >= meta.symbols {
        return Err(WorkspaceError::InvalidSymbol);
    }
    let at = match tree_record_offset(window_bytes, region, tree, initialized) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let ghost before_workspace = workspace@;
    workspace[at] = record.length;
    workspace[at + 1] = (record.code % 256) as u8;
    workspace[at + 2] = (record.code / 256) as u8;
    meta.storage = TreeStorageState::Canonical { initialized: initialized + 1 };
    proof {
        tree_record_outside_builder_code_lengths(
            window_bytes,
            region,
            tree,
            initialized,
        );
        tree_record_outside_builder_bookkeeping(
            window_bytes,
            region,
            tree,
            initialized,
        );
        assert(builder_length_sequence(
            workspace@,
            window_bytes,
            BUILDER_CODE_LENGTHS,
        ) =~= builder_length_sequence(
            before_workspace,
            window_bytes,
            BUILDER_CODE_LENGTHS,
        ));
        assert(builder_count_byte_sequence(workspace@, window_bytes)
            =~= builder_count_byte_sequence(before_workspace, window_bytes));
        assert(builder_next_code_byte_sequence(workspace@, window_bytes)
            =~= builder_next_code_byte_sequence(before_workspace, window_bytes));
    }
    Ok(())
}

pub(crate) fn read_tree_record(
    workspace: &[u8],
    window_bytes: u32,
    region: TreeRegion,
    tree: u16,
    meta: &TreeMetadata,
    symbol: u16,
) -> (r: Result<TreeRecord, WorkspaceError>)
    requires meta.valid_for(region),
    ensures
    window_bytes <= 16_777_216
        && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
        && tree < tree_region_count(region)
        && symbol < meta.symbols
        && match meta.storage {
            TreeStorageState::Single { symbol: only } => symbol == only,
            TreeStorageState::Canonical { initialized } => symbol < initialized,
            TreeStorageState::Unused => false,
        }
        ==> r.is_ok(),
    r.is_ok() ==> {
        &&& symbol < meta.symbols
        &&& match meta.storage {
            TreeStorageState::Single { symbol: only } => {
                &&& symbol == only
                &&& r.unwrap() == TreeRecord { length: 0, code: 0 }
            },
            TreeStorageState::Canonical { initialized } => {
                let at = tree_record_at(window_bytes, region, tree, symbol);
                &&& symbol < initialized
                &&& at + 3 <= workspace@.len()
                &&& r.unwrap().length == workspace@[at as int]
                &&& r.unwrap().code as nat == workspace@[at as int + 1] as nat
                    + 256 * workspace@[at as int + 2] as nat
            },
            TreeStorageState::Unused => false,
        }
    },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    if symbol >= meta.symbols {
        return Err(WorkspaceError::InvalidSymbol);
    }
    match meta.storage {
        TreeStorageState::Unused => Err(WorkspaceError::UninitializedRecord),
        TreeStorageState::Single { symbol: only } => {
            if symbol != only {
                Err(WorkspaceError::InvalidSymbol)
            } else {
                Ok(TreeRecord { length: 0, code: 0 })
            }
        }
        TreeStorageState::Canonical { initialized } => {
            if symbol >= initialized {
                return Err(WorkspaceError::UninitializedRecord);
            }
            let at = match tree_record_offset(window_bytes, region, tree, symbol) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let _low = workspace[at + 1];
            let _high = workspace[at + 2];
            proof { join_tree_code_is_exact(_low, _high); }
            Ok(TreeRecord {
                length: workspace[at],
                code: workspace[at + 1] as u16 | ((workspace[at + 2] as u16) << 8),
            })
        }
    }
}

#[verifier::rlimit(1000)]
pub(crate) fn install_builder_canonical_tree(
    workspace: &mut [u8],
    window_bytes: u32,
    lengths_initialized: u16,
    region: TreeRegion,
    tree: u16,
    meta: &mut TreeMetadata,
) -> (r: Result<(), WorkspaceError>)
    requires old(meta).valid_for(region),
    ensures
        canonical_installer_frame(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            region,
            tree,
            old(meta).symbols,
        ),
        (tree as nat) >= tree_region_count(region)
            ==> final(workspace)@ == old(workspace)@,
        r.is_ok() ==> {
            let lengths = builder_length_sequence(
                old(workspace)@,
                window_bytes,
                old(meta).symbols,
            );
            &&& valid_builder_lengths(lengths)
            &&& (tree as nat) < tree_region_count(region)
            &&& (old(meta).symbols as nat) <= tree_region_symbols(region)
            &&& lengths_initialized == old(meta).symbols
            &&& final(meta).valid_for(region)
            &&& final(meta).symbols == old(meta).symbols
            &&& final(meta).storage == TreeStorageState::Canonical {
                initialized: old(meta).symbols,
            }
            &&& canonical_tree_installed(
                final(workspace)@,
                window_bytes,
                region,
                tree,
                lengths,
            )
            &&& canonical_installer_frame(
                old(workspace)@,
                final(workspace)@,
                window_bytes,
                region,
                tree,
                old(meta).symbols,
            )
        },
{
    if window_bytes > 16_777_216 {
        return Err(WorkspaceError::InvalidWindowBits);
    }
    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(WorkspaceError::WorkspaceTooSmall),
    };
    if workspace.len() < required {
        return Err(WorkspaceError::WorkspaceTooSmall);
    }
    proof {
        assert(required as nat == window_bytes as nat + FIXED_SCRATCH_BYTES as nat);
        assert(workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat);
    }
    if tree >= tree_region_count_exec(region) {
        return Err(WorkspaceError::InvalidTree);
    }
    let symbols = meta.symbols;
    let initialized = match meta.storage {
        TreeStorageState::Canonical { initialized } => initialized,
        _ => return Err(WorkspaceError::UninitializedRecord),
    };
    if initialized != 0 || symbols == 0 || lengths_initialized != symbols
        || symbols > BUILDER_CODE_LENGTHS
    {
        return Err(WorkspaceError::InvalidSymbol);
    }

    let ghost original_workspace = workspace@;
    let ghost lengths = builder_length_sequence(original_workspace, window_bytes, symbols);
    let ghost full_lengths = builder_length_sequence(
        original_workspace,
        window_bytes,
        BUILDER_CODE_LENGTHS,
    );
    let mut symbol: u16 = 0;
    let mut space: u32 = CODE_SPACE;
    let mut nonzero: u16 = 0;
    let ghost mut used: nat = 0;
    while symbol < symbols
        invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
            workspace@ == original_workspace,
            original_workspace.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            symbols == meta.symbols,
            meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
            symbol <= symbols <= BUILDER_CODE_LENGTHS,
            lengths.len() == symbols,
            lengths =~= builder_length_sequence(original_workspace, window_bytes, symbols),
            space as nat + used == CODE_SPACE,
            used == used_space(lengths.take(symbol as int)),
            nonzero as nat == nonzero_count(lengths.take(symbol as int)),
            nonzero <= symbol,
            forall|i: int| 0 <= i < symbol ==> lengths[i] <= MAX_BITS,
        decreases symbols - symbol,
    {
        let length = match read_builder_code_length(
            workspace,
            window_bytes,
            lengths_initialized,
            symbol,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        proof {
            builder_length_sequence_index(
                original_workspace,
                window_bytes,
                symbols,
                symbol,
            );
            assert(lengths =~= builder_length_sequence(
                original_workspace,
                window_bytes,
                symbols,
            ));
            assert(lengths[symbol as int]
                == builder_length_sequence(
                    original_workspace,
                    window_bytes,
                    symbols,
                )[symbol as int]);
            assert(builder_entry_at(
                window_bytes,
                BUILDER_CODE_LENGTHS_OFFSET,
                symbol,
                1,
            ) == window_bytes as nat + BUILDER_CODE_LENGTHS_OFFSET as nat
                + symbol as nat);
            assert(lengths[symbol as int]
                == original_workspace[(window_bytes as nat
                    + BUILDER_CODE_LENGTHS_OFFSET as nat
                    + symbol as nat) as int]);
            assert(length == lengths[symbol as int]);
            used_space_step(lengths, symbol as int);
            nonzero_step(lengths, symbol as int);
        }
        if length > MAX_BITS {
            return Err(WorkspaceError::InvalidCodeLength);
        }
        if length != 0 {
            let amount = weight(length);
            if amount > space {
                return Err(WorkspaceError::InvalidCodeLength);
            }
            space = space - amount;
            nonzero = nonzero + 1;
            proof { used = used + code_weight(length); }
        }
        symbol = symbol + 1;
    }
    proof {
        assert(lengths.take(symbol as int) =~= lengths);
    }
    if nonzero < 2 || space != 0 {
        return Err(WorkspaceError::InvalidCodeLength);
    }
    proof {
        assert(valid_builder_lengths(lengths));
        reveal(canonical_installer_frame);
        assert(canonical_installer_frame(
            original_workspace,
            workspace@,
            window_bytes,
            region,
            tree,
            symbols,
        ));
    }

    let mut count_initialized: u16 = 0;
    while count_initialized < BUILDER_COUNTS
        invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
            count_initialized <= BUILDER_COUNTS,
            symbols <= BUILDER_CODE_LENGTHS,
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            original_workspace.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                == full_lengths,
            full_lengths =~= builder_length_sequence(
                original_workspace,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
            lengths =~= builder_length_sequence(original_workspace, window_bytes, symbols),
            builder_counts_prefix(
                workspace@,
                window_bytes,
                lengths,
                count_initialized as nat,
            ),
            canonical_installer_frame(
                original_workspace,
                workspace@,
                window_bytes,
                region,
                tree,
                symbols,
            ),
            symbols == meta.symbols,
            meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
        decreases BUILDER_COUNTS - count_initialized,
    {
        let length = count_initialized as u8;
        let mut scan: u16 = 0;
        let mut count: u16 = 0;
        while scan < symbols
            invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
                scan <= symbols <= BUILDER_CODE_LENGTHS,
                count <= scan,
                count as nat == count_length(
                    lengths.take(scan as int),
                    count_initialized as u8,
                ),
                count_initialized < BUILDER_COUNTS,
                length == count_initialized as u8,
                window_bytes <= 16_777_216,
                workspace@.len() == original_workspace.len(),
                original_workspace.len()
                    >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
                builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                    == full_lengths,
                full_lengths =~= builder_length_sequence(
                    original_workspace,
                    window_bytes,
                    BUILDER_CODE_LENGTHS,
                ),
                lengths =~= builder_length_sequence(
                    original_workspace,
                    window_bytes,
                    symbols,
                ),
                builder_counts_prefix(
                    workspace@,
                    window_bytes,
                    lengths,
                    count_initialized as nat,
                ),
                canonical_installer_frame(
                    original_workspace,
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    symbols,
                ),
                symbols == meta.symbols,
                meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
            decreases symbols - scan,
        {
            let ghost old_scan = scan;
            let ghost old_count = count;
            let value = match read_builder_code_length(
                workspace,
                window_bytes,
                lengths_initialized,
                scan,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            proof {
                builder_length_matches_snapshot(
                    workspace@,
                    original_workspace,
                    window_bytes,
                    symbols,
                    scan,
                );
                assert(value == lengths[scan as int]);
                count_step(lengths, scan as int, count_initialized as u8);
            }
            if value == length {
                count = count + 1;
            }
            proof {
                assert(count as nat == old_count as nat
                    + if lengths[old_scan as int] == count_initialized as u8 {
                        1nat
                    } else {
                        0nat
                    });
            }
            scan = scan + 1;
        }
        proof {
            assert(scan == symbols);
            assert(lengths.len() == symbols);
            assert(lengths.take(scan as int) =~= lengths);
            assert(count as nat
                == count_length(lengths, count_initialized as u8));
        }
        let ghost before_count_write = workspace@;
        let ghost old_count_initialized = count_initialized;
        count_initialized = match write_next_builder_count(
            workspace,
            window_bytes,
            count_initialized,
            count,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        proof {
            assert(count_initialized == old_count_initialized + 1);
            assert(builder_counts_prefix(
                before_count_write,
                window_bytes,
                lengths,
                old_count_initialized as nat,
            ));
            builder_counts_prefix_after_write(
                before_count_write,
                workspace@,
                window_bytes,
                lengths,
                old_count_initialized,
                count,
            );
            assert(builder_counts_prefix(
                workspace@,
                window_bytes,
                lengths,
                count_initialized as nat,
            ));
        }
    }

    let ghost count_snapshot = workspace@;
    proof {
        assert(builder_counts_prefix(
            count_snapshot,
            window_bytes,
            lengths,
            BUILDER_COUNTS as nat,
        ));
    }
    let mut chain_initialized: u16 = 0;
    while chain_initialized < BUILDER_SYMBOL_CHAIN_ENTRIES
        invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
            chain_initialized <= BUILDER_SYMBOL_CHAIN_ENTRIES,
            symbols <= BUILDER_CODE_LENGTHS,
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            original_workspace.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                == full_lengths,
            builder_count_byte_sequence(workspace@, window_bytes)
                == builder_count_byte_sequence(count_snapshot, window_bytes),
            count_snapshot.len() == original_workspace.len(),
            builder_counts_prefix(
                count_snapshot,
                window_bytes,
                lengths,
                BUILDER_COUNTS as nat,
            ),
            canonical_installer_frame(
                original_workspace,
                workspace@,
                window_bytes,
                region,
                tree,
                symbols,
            ),
            symbols == meta.symbols,
            meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
        decreases BUILDER_SYMBOL_CHAIN_ENTRIES - chain_initialized,
    {
        chain_initialized = match write_next_builder_symbol_chain(
            workspace,
            window_bytes,
            chain_initialized,
            u16::MAX,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
    }

    let mut chain_length: u16 = 1;
    while chain_length <= MAX_BITS as u16
        invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
            1 <= chain_length <= MAX_BITS as u16 + 1,
            symbols <= BUILDER_CODE_LENGTHS,
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            original_workspace.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                == full_lengths,
            builder_count_byte_sequence(workspace@, window_bytes)
                == builder_count_byte_sequence(count_snapshot, window_bytes),
            count_snapshot.len() == original_workspace.len(),
            builder_counts_prefix(
                count_snapshot,
                window_bytes,
                lengths,
                BUILDER_COUNTS as nat,
            ),
            canonical_installer_frame(
                original_workspace,
                workspace@,
                window_bytes,
                region,
                tree,
                symbols,
            ),
            symbols == meta.symbols,
            meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
        decreases MAX_BITS as u16 + 1 - chain_length,
    {
        let mut previous: u16 = chain_length;
        let mut scan: u16 = 0;
        while scan < symbols
            invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
                scan <= symbols <= BUILDER_CODE_LENGTHS,
                1 <= chain_length <= MAX_BITS as u16,
                previous < BUILDER_SYMBOL_CHAIN_ENTRIES,
                window_bytes <= 16_777_216,
                workspace@.len() == original_workspace.len(),
                original_workspace.len()
                    >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
                builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                    == full_lengths,
                builder_count_byte_sequence(workspace@, window_bytes)
                    == builder_count_byte_sequence(count_snapshot, window_bytes),
                count_snapshot.len() == original_workspace.len(),
                builder_counts_prefix(
                    count_snapshot,
                    window_bytes,
                    lengths,
                    BUILDER_COUNTS as nat,
                ),
                canonical_installer_frame(
                    original_workspace,
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    symbols,
                ),
                symbols == meta.symbols,
                meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
            decreases symbols - scan,
        {
            let value = match read_builder_code_length(
                workspace,
                window_bytes,
                lengths_initialized,
                scan,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if value as u16 == chain_length {
                match write_builder_symbol_chain_at(
                    workspace,
                    window_bytes,
                    chain_initialized,
                    previous,
                    scan,
                ) {
                    Ok(()) => {}
                    Err(error) => return Err(error),
                }
                previous = BUILDER_COUNTS + scan;
            }
            scan = scan + 1;
        }
        chain_length = chain_length + 1;
    }

    let mut next_initialized: u16 = 0;
    let ghost before_first_next = workspace@;
    next_initialized = match write_next_builder_next_code(
        workspace,
        window_bytes,
        next_initialized,
        0,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    proof {
        reveal(first_code);
        builder_next_prefix_after_write(
            before_first_next,
            workspace@,
            window_bytes,
            lengths,
            0,
            0,
        );
        assert(builder_next_prefix(workspace@, window_bytes, lengths, 1));
    }
    let mut code: u64 = 0;
    while next_initialized < BUILDER_NEXT_CODES
        invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
            1 <= next_initialized <= BUILDER_NEXT_CODES,
            code <= u32::MAX as u64,
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            original_workspace.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                == full_lengths,
            builder_count_byte_sequence(workspace@, window_bytes)
                == builder_count_byte_sequence(count_snapshot, window_bytes),
            count_snapshot.len() == original_workspace.len(),
            builder_counts_prefix(
                count_snapshot,
                window_bytes,
                lengths,
                BUILDER_COUNTS as nat,
            ),
            builder_next_prefix(
                workspace@,
                window_bytes,
                lengths,
                next_initialized as nat,
            ),
            canonical_installer_frame(
                original_workspace,
                workspace@,
                window_bytes,
                region,
                tree,
                symbols,
            ),
            code as nat == first_code(
                lengths,
                (next_initialized - 1) as nat,
            ),
            symbols == meta.symbols,
            meta.storage == (TreeStorageState::Canonical { initialized: 0 }),
        decreases BUILDER_NEXT_CODES - next_initialized,
    {
        let ghost old_next_initialized = next_initialized;
        if next_initialized > 1 {
            let previous_count = match read_builder_count(
                workspace,
                window_bytes,
                count_initialized,
                next_initialized - 1,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            proof {
                builder_count_matches_snapshot(
                    workspace@,
                    count_snapshot,
                    window_bytes,
                    (next_initialized - 1) as u16,
                );
                reveal(builder_counts_prefix);
                assert(previous_count as nat == builder_count_at(
                    workspace@,
                    window_bytes,
                    (next_initialized - 1) as int,
                ));
                assert(builder_count_at(
                    count_snapshot,
                    window_bytes,
                    (next_initialized - 1) as int,
                ) == count_length(
                    lengths,
                    (next_initialized - 1) as u8,
                ));
                assert(previous_count as nat == count_length(
                    lengths,
                    (next_initialized - 1) as u8,
                ));
            }
            let expanded = (code + previous_count as u64) * 2;
            if expanded > u32::MAX as u64 {
                return Err(WorkspaceError::InvalidCodeLength);
            }
            code = expanded;
            proof {
                reveal(first_code);
                assert(code as nat == first_code(lengths, next_initialized as nat));
            }
        } else {
            proof {
                assert(next_initialized == 1);
                reveal(first_code);
                assert(code as nat == first_code(lengths, next_initialized as nat));
            }
        }
        let ghost before_next_write = workspace@;
        next_initialized = match write_next_builder_next_code(
            workspace,
            window_bytes,
            next_initialized,
            code as u32,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        proof {
            assert(next_initialized == old_next_initialized + 1);
            builder_next_prefix_after_write(
                before_next_write,
                workspace@,
                window_bytes,
                lengths,
                old_next_initialized,
                code as u32,
            );
        }
    }

    let ghost next_snapshot = workspace@;
    proof {
        assert(next_initialized == BUILDER_NEXT_CODES);
        assert(builder_next_prefix(
            next_snapshot,
            window_bytes,
            lengths,
            BUILDER_NEXT_CODES as nat,
        ));
    }
    symbol = 0;
    while symbol < symbols
        invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
            symbol <= symbols <= BUILDER_CODE_LENGTHS,
            window_bytes <= 16_777_216,
            workspace@.len() == original_workspace.len(),
            original_workspace.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
            builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                == full_lengths,
            lengths =~= builder_length_sequence(original_workspace, window_bytes, symbols),
            builder_next_code_byte_sequence(workspace@, window_bytes)
                == builder_next_code_byte_sequence(next_snapshot, window_bytes),
            next_snapshot.len() == original_workspace.len(),
            builder_next_prefix(
                next_snapshot,
                window_bytes,
                lengths,
                BUILDER_NEXT_CODES as nat,
            ),
            canonical_tree_prefix(
                workspace@,
                window_bytes,
                region,
                tree,
                lengths,
                symbol as nat,
            ),
            canonical_installer_frame(
                original_workspace,
                workspace@,
                window_bytes,
                region,
                tree,
                symbols,
            ),
            full_lengths =~= builder_length_sequence(
                original_workspace,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ),
            lengths.len() == symbols,
            symbols == meta.symbols,
            meta.valid_for(region),
            meta.storage == (TreeStorageState::Canonical { initialized: symbol }),
        decreases symbols - symbol,
    {
        let length = match read_builder_code_length(
            workspace,
            window_bytes,
            lengths_initialized,
            symbol,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        proof {
            builder_length_matches_snapshot(
                workspace@,
                original_workspace,
                window_bytes,
                symbols,
                symbol,
            );
            assert(length == lengths[symbol as int]);
        }
        let mut record = TreeRecord { length, code: 0 };
        if length != 0 {
            let base = match read_builder_next_code(
                workspace,
                window_bytes,
                next_initialized,
                length as u16,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let mut scan: u16 = 0;
            let mut rank: u16 = 0;
            while scan < symbol
                invariant
            original_workspace == old(workspace)@,
            symbols == old(meta).symbols,
            (tree as nat) < tree_region_count(region),
                    scan <= symbol < symbols <= BUILDER_CODE_LENGTHS,
                    rank <= scan,
                    rank as nat == count_length(
                        lengths.take(scan as int),
                        length,
                    ),
                    length == lengths[symbol as int],
                    lengths.len() == symbols,
                    workspace@.len() == original_workspace.len(),
                    original_workspace.len()
                        >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat,
                    builder_length_sequence(workspace@, window_bytes, BUILDER_CODE_LENGTHS)
                        == full_lengths,
                    full_lengths =~= builder_length_sequence(
                        original_workspace,
                        window_bytes,
                        BUILDER_CODE_LENGTHS,
                    ),
                    canonical_installer_frame(
                        original_workspace,
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        symbols,
                    ),
                    lengths =~= builder_length_sequence(
                        original_workspace,
                        window_bytes,
                        symbols,
                    ),
                decreases symbol - scan,
            {
                let ghost old_scan = scan;
                let ghost old_rank = rank;
                let value = match read_builder_code_length(
                    workspace,
                    window_bytes,
                    lengths_initialized,
                    scan,
                ) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                proof {
                    builder_length_matches_snapshot(
                        workspace@,
                        original_workspace,
                        window_bytes,
                        symbols,
                        scan,
                    );
                    assert(value == lengths[scan as int]);
                    count_step(lengths, scan as int, length);
                }
                if value == length {
                    rank = rank + 1;
                }
                proof {
                    assert(rank as nat == old_rank as nat
                        + if lengths[old_scan as int] == length { 1nat } else { 0nat });
                }
                scan = scan + 1;
            }
            proof {
                builder_next_code_matches_snapshot(
                    workspace@,
                    next_snapshot,
                    window_bytes,
                    length as u16,
                );
                reveal(builder_next_prefix);
                assert(base as nat == first_code(lengths, length as nat));
                assert(rank as nat == count_length(
                    lengths.take(symbol as int),
                    length,
                ));
                assert(base as nat + rank as nat
                    == canonical_code(lengths, symbol as int));
            }
            let combined = base as u64 + rank as u64;
            if combined > u16::MAX as u64 {
                return Err(WorkspaceError::InvalidCodeLength);
            }
            record.code = combined as u16;
            proof {
                assert(record.code as nat == canonical_code(lengths, symbol as int));
            }
        } else {
            proof {
                assert(record.code == 0);
            }
        }
        let ghost before_tree_write = workspace@;
        match write_next_tree_record(workspace, window_bytes, region, tree, meta, record) {
            Ok(()) => {
                proof {
                    assert(builder_length_sequence(
                        workspace@,
                        window_bytes,
                        BUILDER_CODE_LENGTHS,
                    ) == builder_length_sequence(
                        before_tree_write,
                        window_bytes,
                        BUILDER_CODE_LENGTHS,
                    ));
                    canonical_tree_prefix_after_write(
                        before_tree_write,
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        lengths,
                        symbol,
                        record,
                    );
                }
            }
            Err(error) => return Err(error),
        }
        proof {
            assert(builder_length_sequence(
                workspace@,
                window_bytes,
                BUILDER_CODE_LENGTHS,
            ) == full_lengths);
            assert(builder_next_code_byte_sequence(workspace@, window_bytes)
                == builder_next_code_byte_sequence(next_snapshot, window_bytes));
        }
        symbol = symbol + 1;
    }
    Ok(())
}

pub(crate) fn write_next_temp_context_tree_record(
    workspace: &mut [u8],
    window_bytes: u32,
    meta: &mut TreeMetadata,
    record: TreeRecord,
) -> (r: Result<(), WorkspaceError>)
    requires old(meta).valid_for(TreeRegion::TemporaryContext),
    ensures
        window_bytes <= 16_777_216
            && old(workspace)@.len()
                >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && record.length <= MAX_BITS
            && match old(meta).storage {
                TreeStorageState::Canonical { initialized } => initialized < old(meta).symbols,
                _ => false,
            }
            ==> r.is_ok(),
        r.is_ok() ==> {
            &&& final(meta).valid_for(TreeRegion::TemporaryContext)
            &&& final(meta).symbols == old(meta).symbols
            &&& match old(meta).storage {
                TreeStorageState::Canonical { initialized } => {
                    let at = tree_record_at(
                        window_bytes,
                        TreeRegion::TemporaryContext,
                        0,
                        initialized,
                    );
                    let low = (record.code % 256) as u8;
                    let high = (record.code / 256) as u8;
                    &&& final(meta).storage == TreeStorageState::Canonical {
                        initialized: (initialized as int + 1) as u16,
                    }
                    &&& at + 3 <= old(workspace)@.len()
                    &&& final(workspace)@ == old(workspace)@
                        .update(at as int, record.length)
                        .update(at as int + 1, low)
                        .update(at as int + 2, high)
                },
                _ => false,
            }
        },
        r.is_err() ==> {
            &&& final(workspace)@ == old(workspace)@
            &&& *final(meta) == *old(meta)
        },
{
    write_next_tree_record(
        workspace,
        window_bytes,
        TreeRegion::TemporaryContext,
        0,
        meta,
        record,
    )
}

pub(crate) fn read_temp_context_tree_record(
    workspace: &[u8],
    window_bytes: u32,
    meta: &TreeMetadata,
    symbol: u16,
) -> (r: Result<TreeRecord, WorkspaceError>)
    requires meta.valid_for(TreeRegion::TemporaryContext),
    ensures
        window_bytes <= 16_777_216
            && workspace@.len() >= window_bytes as nat + FIXED_SCRATCH_BYTES as nat
            && symbol < meta.symbols
            && match meta.storage {
                TreeStorageState::Single { symbol: only } => symbol == only,
                TreeStorageState::Canonical { initialized } => symbol < initialized,
                TreeStorageState::Unused => false,
            }
            ==> r.is_ok(),
        r.is_ok() ==> {
        &&& symbol < meta.symbols
        &&& match meta.storage {
            TreeStorageState::Single { symbol: only } => {
                &&& symbol == only
                &&& r.unwrap() == TreeRecord { length: 0, code: 0 }
            },
            TreeStorageState::Canonical { initialized } => {
                let at = tree_record_at(
                    window_bytes,
                    TreeRegion::TemporaryContext,
                    0,
                    symbol,
                );
                &&& symbol < initialized
                &&& at + 3 <= workspace@.len()
                &&& r.unwrap().length == workspace@[at as int]
                &&& r.unwrap().code as nat == workspace@[at as int + 1] as nat
                    + 256 * workspace@[at as int + 2] as nat
            },
            TreeStorageState::Unused => false,
        }
    },
{
    read_tree_record(
        workspace,
        window_bytes,
        TreeRegion::TemporaryContext,
        0,
        meta,
        symbol,
    )
}

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_codes_match_small_independent_examples() {
        let code = PrefixCode::from_lengths(&[1, 2, 3, 3]).unwrap();
        assert_eq!(code.codes[..4], [0, 2, 6, 7]);
        assert_eq!(code.decode_exact(0, 1), Some(0));
        assert_eq!(code.decode_exact(2, 2), Some(1));
        assert_eq!(code.decode_exact(6, 3), Some(2));
        assert_eq!(code.decode_exact(7, 3), Some(3));
        assert_eq!(code.decode_exact(1, 3), None);
    }

    #[test]
    fn malformed_code_spaces_are_rejected() {
        assert_eq!(
            PrefixCode::from_lengths(&[]),
            Err(PrefixError::EmptyAlphabet)
        );
        assert_eq!(
            PrefixCode::from_lengths(&[16, 1]),
            Err(PrefixError::InvalidCodeLength)
        );
        assert_eq!(
            PrefixCode::from_lengths(&[1]),
            Err(PrefixError::DegenerateAlphabet)
        );
        assert_eq!(
            PrefixCode::from_lengths(&[1, 1, 1]),
            Err(PrefixError::Oversubscribed)
        );
        assert_eq!(
            PrefixCode::from_lengths(&[2, 2]),
            Err(PrefixError::Incomplete)
        );
    }

    #[test]
    fn full_block_type_alphabet_is_bounded() {
        let mut lengths = [8u8; 258];
        // 256 complete eight-bit codes plus two unused symbols.
        lengths[256] = 0;
        lengths[257] = 0;
        let code = PrefixCode::from_lengths(&lengths).unwrap();
        assert_eq!(code.symbols, 258);
        assert_eq!(code.decode_exact(255, 8), Some(255));
    }

    #[test]
    fn block_length_ranges_match_rfc_table() {
        assert_eq!(decode_block_length(0, 0), Ok(1));
        assert_eq!(decode_block_length(0, 3), Ok(4));
        assert_eq!(decode_block_length(24, 8191), Ok(16_624));
        assert_eq!(decode_block_length(25, 0), Ok(16_625));
        assert_eq!(decode_block_length(25, (1 << 24) - 1), Ok(16_793_840));
        assert_eq!(
            decode_block_length(26, 0),
            Err(PrefixError::InvalidBlockLengthSymbol)
        );
        assert_eq!(
            decode_block_length(0, 4),
            Err(PrefixError::InvalidBlockLengthSuffix)
        );
    }

    #[test]
    fn b3_workspace_layout_is_exact_and_bounded() {
        assert_eq!(
            required_workspace_bytes(9),
            Err(WorkspaceError::InvalidWindowBits)
        );
        assert_eq!(
            required_workspace_bytes(25),
            Err(WorkspaceError::InvalidWindowBits)
        );
        assert_eq!(required_workspace_bytes(10), Ok(1_177_584));
        assert_eq!(required_workspace_bytes(24), Ok(17_953_776));

        let window = 1u32 << 10;
        for region in [
            TreeRegion::Literal,
            TreeRegion::Command,
            TreeRegion::Distance,
            TreeRegion::BlockType,
            TreeRegion::BlockLength,
            TreeRegion::TemporaryContext,
        ] {
            let trees = tree_region_count_exec(region);
            let symbols = tree_region_symbols_exec(region);
            let first = tree_record_offset(window, region, 0, 0).unwrap();
            let last = tree_record_offset(window, region, trees - 1, symbols - 1).unwrap();
            assert_eq!(
                first,
                window as usize + tree_region_offset_exec(region) as usize
            );
            assert_eq!(last + 3, first + trees as usize * symbols as usize * 3);
            assert!(last + 3 <= required_workspace_bytes(10).unwrap() as usize);
        }

        assert_eq!(BUILDER_CODE_LENGTHS_OFFSET, BUILDER_OFFSET);
        assert_eq!(BUILDER_CODE_LENGTHS_OFFSET + 704, BUILDER_COUNTS_OFFSET);
        assert_eq!(BUILDER_COUNTS_OFFSET + 32, BUILDER_NEXT_CODES_OFFSET);
        assert_eq!(BUILDER_NEXT_CODES_OFFSET + 64, BUILDER_SYMBOL_CHAIN_OFFSET);
        assert_eq!(
            BUILDER_SYMBOL_CHAIN_OFFSET + 1_440,
            TEMP_CONTEXT_TREE_OFFSET
        );
        assert_eq!(TEMP_CONTEXT_TREE_OFFSET + 816, MTF_OFFSET);
    }

    #[test]
    fn b3_builder_accessors_use_exact_regions_and_track_initialization() {
        let window = 1u32 << 10;
        let required = required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];
        let base = window as usize;

        assert_eq!(
            read_builder_code_length(&workspace, window, 0, 0),
            Err(WorkspaceError::UninitializedRecord)
        );
        assert_eq!(
            write_next_builder_code_length(&mut workspace, window, BUILDER_CODE_LENGTHS - 1, 15,),
            Ok(BUILDER_CODE_LENGTHS)
        );
        assert_eq!(
            read_builder_code_length(
                &workspace,
                window,
                BUILDER_CODE_LENGTHS,
                BUILDER_CODE_LENGTHS - 1,
            ),
            Ok(15)
        );
        assert_eq!(workspace[base + BUILDER_COUNTS_OFFSET as usize], 0xa5);

        assert_eq!(
            write_next_builder_count(&mut workspace, window, BUILDER_COUNTS - 1, 0x1234),
            Ok(BUILDER_COUNTS)
        );
        assert_eq!(
            read_builder_count(&workspace, window, BUILDER_COUNTS, BUILDER_COUNTS - 1,),
            Ok(0x1234)
        );
        assert_eq!(workspace[base + BUILDER_NEXT_CODES_OFFSET as usize], 0xa5);

        assert_eq!(
            write_next_builder_next_code(
                &mut workspace,
                window,
                BUILDER_NEXT_CODES - 1,
                0x89ab_cdef,
            ),
            Ok(BUILDER_NEXT_CODES)
        );
        assert_eq!(
            read_builder_next_code(
                &workspace,
                window,
                BUILDER_NEXT_CODES,
                BUILDER_NEXT_CODES - 1,
            ),
            Ok(0x89ab_cdef)
        );
        assert_eq!(workspace[base + BUILDER_SYMBOL_CHAIN_OFFSET as usize], 0xa5);

        assert_eq!(
            write_next_builder_symbol_chain(
                &mut workspace,
                window,
                BUILDER_SYMBOL_CHAIN_ENTRIES - 1,
                0xbeef,
            ),
            Ok(BUILDER_SYMBOL_CHAIN_ENTRIES)
        );
        assert_eq!(
            read_builder_symbol_chain(
                &workspace,
                window,
                BUILDER_SYMBOL_CHAIN_ENTRIES,
                BUILDER_SYMBOL_CHAIN_ENTRIES - 1,
            ),
            Ok(0xbeef)
        );
        assert_eq!(workspace[base + TEMP_CONTEXT_TREE_OFFSET as usize], 0xa5);

        let mut temp_meta = TreeMetadata {
            symbols: TEMP_CONTEXT_SYMBOLS,
            storage: TreeStorageState::Canonical {
                initialized: TEMP_CONTEXT_SYMBOLS - 1,
            },
        };
        assert_eq!(
            write_next_temp_context_tree_record(
                &mut workspace,
                window,
                &mut temp_meta,
                TreeRecord {
                    length: 15,
                    code: 0x4321,
                },
            ),
            Ok(())
        );
        assert_eq!(
            read_temp_context_tree_record(&workspace, window, &temp_meta, TEMP_CONTEXT_SYMBOLS - 1,),
            Ok(TreeRecord {
                length: 15,
                code: 0x4321,
            })
        );
        assert_eq!(workspace[base + MTF_OFFSET as usize], 0xa5);
    }

    #[test]
    fn b3_builder_errors_preserve_workspace() {
        let window = 1u32 << 10;
        let required = required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0x3cu8; required];
        let before = workspace.clone();

        assert_eq!(
            write_next_builder_code_length(&mut workspace, window, BUILDER_CODE_LENGTHS, 1,),
            Err(WorkspaceError::InvalidSymbol)
        );
        assert_eq!(workspace, before);
        assert_eq!(
            read_builder_count(&workspace, window, 0, 0),
            Err(WorkspaceError::UninitializedRecord)
        );
        assert_eq!(
            read_builder_next_code(&workspace, window, BUILDER_NEXT_CODES + 1, 0),
            Err(WorkspaceError::InvalidSymbol)
        );
        assert_eq!(
            read_builder_symbol_chain(
                &workspace,
                window,
                BUILDER_SYMBOL_CHAIN_ENTRIES,
                BUILDER_SYMBOL_CHAIN_ENTRIES,
            ),
            Err(WorkspaceError::InvalidSymbol)
        );
    }

    #[test]
    fn b3_tree_records_never_read_uninitialized_workspace() {
        let window = 1u32 << 10;
        let required = required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];
        let mut meta = TreeMetadata::canonical(TreeRegion::Literal, 2).unwrap();

        assert_eq!(
            read_tree_record(&workspace, window, TreeRegion::Literal, 0, &meta, 0),
            Err(WorkspaceError::UninitializedRecord)
        );
        write_next_tree_record(
            &mut workspace,
            window,
            TreeRegion::Literal,
            0,
            &mut meta,
            TreeRecord { length: 1, code: 0 },
        )
        .unwrap();
        write_next_tree_record(
            &mut workspace,
            window,
            TreeRegion::Literal,
            0,
            &mut meta,
            TreeRecord { length: 1, code: 1 },
        )
        .unwrap();
        assert_eq!(
            read_tree_record(&workspace, window, TreeRegion::Literal, 0, &meta, 0),
            Ok(TreeRecord { length: 1, code: 0 })
        );
        assert_eq!(
            read_tree_record(&workspace, window, TreeRegion::Literal, 0, &meta, 1),
            Ok(TreeRecord { length: 1, code: 1 })
        );
        assert_eq!(workspace[window as usize + 6], 0xa5);

        let single = TreeMetadata::single(TreeRegion::Literal, 256, 19).unwrap();
        let first = read_tree_record(&workspace, window, TreeRegion::Literal, 1, &single, 19);
        workspace.fill(0x5a);
        let second = read_tree_record(&workspace, window, TreeRegion::Literal, 1, &single, 19);
        assert_eq!(first, Ok(TreeRecord { length: 0, code: 0 }));
        assert_eq!(first, second);

        let mut too_small = vec![0u8; required - 1];
        let mut small_meta = TreeMetadata::canonical(TreeRegion::Literal, 1).unwrap();
        assert_eq!(
            write_next_tree_record(
                &mut too_small,
                window,
                TreeRegion::Literal,
                0,
                &mut small_meta,
                TreeRecord { length: 1, code: 0 },
            ),
            Err(WorkspaceError::WorkspaceTooSmall)
        );
    }

    #[test]
    fn b3_canonical_tree_records_accept_unused_zero_lengths() {
        let window = 1u32 << 10;
        let required = required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0x96u8; required];
        let mut canonical = TreeMetadata::canonical(TreeRegion::Literal, 2).unwrap();

        assert_eq!(
            write_next_tree_record(
                &mut workspace,
                window,
                TreeRegion::Literal,
                0,
                &mut canonical,
                TreeRecord { length: 0, code: 0 },
            ),
            Ok(())
        );
        assert_eq!(
            read_tree_record(&workspace, window, TreeRegion::Literal, 0, &canonical, 0,),
            Ok(TreeRecord { length: 0, code: 0 })
        );
        assert_eq!(
            canonical.storage,
            TreeStorageState::Canonical { initialized: 1 }
        );

        let single = TreeMetadata::single(TreeRegion::Literal, 2, 0).unwrap();
        assert_ne!(canonical.storage, single.storage);

        let before = workspace.clone();
        let before_meta = canonical;
        assert_eq!(
            write_next_tree_record(
                &mut workspace,
                window,
                TreeRegion::Literal,
                0,
                &mut canonical,
                TreeRecord {
                    length: MAX_BITS + 1,
                    code: 0,
                },
            ),
            Err(WorkspaceError::InvalidCodeLength)
        );
        assert_eq!(workspace, before);
        assert_eq!(canonical, before_meta);
    }

    #[test]
    fn b3_builder_installs_sparse_canonical_records_and_frames_tree() {
        let window = 1u32 << 10;
        let required = required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];
        let mut initialized = 0u16;
        for length in [1u8, 1, 0, 0] {
            initialized =
                write_next_builder_code_length(&mut workspace, window, initialized, length)
                    .unwrap();
        }

        let tree = 1u16;
        let first = tree_record_offset(window, TreeRegion::Literal, tree, 0).unwrap();
        let before_tree = workspace[first - 1];
        let after_tree = workspace[first + 4 * 3];
        let mut meta = TreeMetadata::canonical(TreeRegion::Literal, 4).unwrap();
        install_builder_canonical_tree(
            &mut workspace,
            window,
            initialized,
            TreeRegion::Literal,
            tree,
            &mut meta,
        )
        .unwrap();

        assert_eq!(meta.storage, TreeStorageState::Canonical { initialized: 4 });
        for (symbol, expected) in [
            TreeRecord { length: 1, code: 0 },
            TreeRecord { length: 1, code: 1 },
            TreeRecord { length: 0, code: 0 },
            TreeRecord { length: 0, code: 0 },
        ]
        .into_iter()
        .enumerate()
        {
            assert_eq!(
                read_tree_record(
                    &workspace,
                    window,
                    TreeRegion::Literal,
                    tree,
                    &meta,
                    symbol as u16,
                ),
                Ok(expected),
            );
        }
        assert_eq!(workspace[first - 1], before_tree);
        assert_eq!(workspace[first + 4 * 3], after_tree);
    }

    #[test]
    fn b3b_inverse_mtf_is_atomic_reusable_and_exactly_charged() {
        let window = 1u32 << 10;
        let required = required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];

        let ranks = [2u8, 0, 1, 1];
        let mut initialized = 0u16;
        for rank in ranks {
            initialized = write_next_context_entry(
                &mut workspace,
                window,
                ContextMapKind::Distance,
                ranks.len() as u16,
                initialized,
                rank,
                4,
            )
            .unwrap();
        }
        let map_start = context_entry_offset(window, ContextMapKind::Distance, 0).unwrap();
        let before_map = workspace[map_start..map_start + ranks.len()].to_vec();
        let outside_map = workspace[map_start + ranks.len()];

        let (next_bound, work) = inverse_mtf_context_map(
            &mut workspace,
            window,
            ContextMapKind::Distance,
            ranks.len() as u16,
            4,
            63,
        )
        .unwrap();
        assert_eq!(before_map, ranks);
        assert_eq!(next_bound, 0);
        assert_eq!(work, 4 * 64 + (2 * 2 + 6) + 6 + (2 + 6) + (2 + 6));
        assert_eq!(
            &workspace[map_start..map_start + ranks.len()],
            &[2, 2, 0, 2],
        );
        assert_eq!(workspace[map_start + ranks.len()], outside_map);

        let list_start = (window + MTF_LIST_OFFSET) as usize;
        assert_eq!(&workspace[list_start..list_start + 4], &[2, 0, 1, 3]);
        for i in 4..256 {
            assert_eq!(workspace[list_start + i], i as u8);
        }

        let second_ranks = [3u8, 0];
        initialized = 0;
        for rank in second_ranks {
            initialized = write_next_context_entry(
                &mut workspace,
                window,
                ContextMapKind::Distance,
                second_ranks.len() as u16,
                initialized,
                rank,
                4,
            )
            .unwrap();
        }
        let (second_bound, second_work) = inverse_mtf_context_map(
            &mut workspace,
            window,
            ContextMapKind::Distance,
            second_ranks.len() as u16,
            4,
            next_bound,
        )
        .unwrap();
        assert_eq!(second_bound, 0);
        assert_eq!(second_work, 4 + (2 * 3 + 6) + 6);
        assert_eq!(&workspace[map_start..map_start + 2], &[3, 3]);
        assert_eq!(&workspace[list_start..list_start + 4], &[3, 0, 1, 2]);
        for i in 4..256 {
            assert_eq!(workspace[list_start + i], i as u8);
        }
    }
}
