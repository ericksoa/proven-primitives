//! Private canonical prefix-code foundation for Brotli B2.
//!
//! The implementation deliberately uses bounded straight-line scans instead
//! of speculative lookup tables. It validates the complete 15-bit code space,
//! constructs RFC-style canonical codes and resolves only exact code/length
//! pairs. Full stream code-length decoding remains a later integration step.

#![allow(dead_code)]

use vstd::prelude::*;

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
}
