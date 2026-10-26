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

pub(crate) closed spec fn canonical_installer_frame(
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
            TreeStorageState::Canonical { initialized } => initialized <= self.symbols,
        }
    }

    pub(crate) fn unused() -> (r: Self)
        ensures r.symbols == 0, r.storage == TreeStorageState::Unused,
    {
        Self { symbols: 0, storage: TreeStorageState::Unused }
    }

    pub(crate) fn single(
        region: TreeRegion,
        symbols: u16,
        symbol: u16,
    ) -> (r: Result<Self, WorkspaceError>)
        ensures r.is_ok() ==> r.unwrap().valid_for(region),
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
        ensures r.is_ok() ==> r.unwrap().valid_for(region),
    {
        let capacity = tree_region_symbols_exec(region);
        if symbols == 0 || symbols > capacity {
            return Err(WorkspaceError::InvalidSymbol);
        }
        Ok(Self { symbols, storage: TreeStorageState::Canonical { initialized: 0 } })
    }
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
        r.is_ok() ==> {
            let lengths = builder_length_sequence(
                old(workspace)@,
                window_bytes,
                old(meta).symbols,
            );
            &&& valid_builder_lengths(lengths)
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
}
