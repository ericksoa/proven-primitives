//! RFC 4648 standard-alphabet Base64 with canonical padding.

use crate::{copy_bytes, Error};
#[cfg(verus_keep_ghost)]
use crate::{
    extend_written, prepend, prepend_assoc, prepend_empty, prepend_finish, written, written_empty,
};
use vstd::prelude::*;

verus! {

pub open spec fn symbol(v: u8) -> u8 {
    if v < 26 { (b'A' + v) as u8 }
    else if v < 52 { (b'a' + v - 26) as u8 }
    else if v < 62 { (b'0' + v - 52) as u8 }
    else if v == 62 { b'+' } else { b'/' }
}

const ENCODE_TABLE: [u8; 64] = [
    65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
    81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102,
    103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
    119, 120, 121, 122, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 43, 47,
];

fn to_symbol(v: u8) -> (r: u8)
    requires v < 64,
    ensures r == symbol(v),
{
    ENCODE_TABLE[v as usize]
}

pub open spec fn value(c: u8) -> Option<u8> {
    if b'A' <= c <= b'Z' { Some((c - b'A') as u8) }
    else if b'a' <= c <= b'z' { Some((c - b'a' + 26) as u8) }
    else if b'0' <= c <= b'9' { Some((c - b'0' + 52) as u8) }
    else if c == b'+' { Some(62) }
    else if c == b'/' { Some(63) } else { None }
}

const DECODE_TABLE: [u8; 256] = [
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 62, 255, 255, 255, 63,
    52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 255, 255, 255,
    255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 255, 255, 255, 255, 255,
    255, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
];

fn from_symbol(c: u8) -> (r: Option<u8>)
    ensures r == value(c), r.is_some() ==> r.unwrap() < 64,
{
    let decoded = DECODE_TABLE[c as usize];
    if decoded == 255 { None } else { Some(decoded) }
}

/// RFC 4648's 24-bit group, split into four six-bit digits and padded.
pub open spec fn quantum(s: Seq<u8>) -> Seq<u8> {
    if 1 <= s.len() <= 3 {
        let a = s[0];
        let b = if s.len() > 1 { s[1] } else { 0u8 };
        let c = if s.len() > 2 { s[2] } else { 0u8 };
        seq![symbol(a / 4), symbol(((a % 4) * 16 + b / 16) as u8),
            if s.len() > 1 { symbol(((b % 16) * 4 + c / 64) as u8) } else { b'=' },
            if s.len() > 2 { symbol(c % 64) } else { b'=' }]
    } else { Seq::empty() }
}

pub open spec fn encoded(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 { Seq::empty() }
    else {
        let n = if s.len() < 3 { s.len() as int } else { 3int };
        quantum(s.take(n)) + encoded(s.skip(n))
    }
}

/// Mathematical size, without machine-integer wrapping. Together with the
/// checked encoded_length and encode_into contracts, this excludes undersized
/// successful writes caused by the CVE-2017-1000430 sizing failure class.
proof fn encoded_size_is_four_per_group(bytes: Seq<u8>)
    ensures encoded(bytes).len() == 4 * ((bytes.len() + 2) / 3),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let n = if bytes.len() < 3 { bytes.len() as int } else { 3int };
        encoded_size_is_four_per_group(bytes.skip(n));
        assert(quantum(bytes.take(n)).len() == 4);
        assert((bytes.len() + 2) / 3 == 1 + (bytes.len() - n + 2) / 3);
    }
}

pub proof fn encoded_concat(a: Seq<u8>, b: Seq<u8>)
    requires a.len() % 3 == 0,
    ensures encoded(a + b) == encoded(a) + encoded(b),
    decreases a.len(),
{
    if a.len() > 0 {
        encoded_concat(a.skip(3), b);
        assert((a + b).take(3) =~= a.take(3));
        assert((a + b).skip(3) =~= a.skip(3) + b);
        assert(quantum(a.take(3)) + (encoded(a.skip(3)) + encoded(b))
            =~= (quantum(a.take(3)) + encoded(a.skip(3))) + encoded(b));
    } else { assert(a =~= Seq::<u8>::empty()); }
}

pub proof fn encoded_step(s: Seq<u8>, i: int, n: int)
    requires 0 <= i < s.len(), i % 3 == 0,
        n == if s.len() - i < 3 { s.len() - i } else { 3int },
    ensures encoded(s.take(i + n)) == encoded(s.take(i)) + quantum(s.subrange(i, i + n)),
        encoded(s.take(i + n)).len() == encoded(s.take(i)).len() + 4,
        encoded(s.take(i + n)).len() <= encoded(s).len(),
{
    encoded_concat(s.take(i), s.subrange(i, i + n));
    assert(s.take(i) + s.subrange(i, i + n) =~= s.take(i + n));
    assert(s.subrange(i, i + n).skip(n) =~= Seq::<u8>::empty());
    assert(s.subrange(i, i + n).take(n) =~= s.subrange(i, i + n));
    reveal_with_fuel(encoded, 2);
    assert(encoded(s.subrange(i, i + n)) == quantum(s.subrange(i, i + n)));
    if i + n < s.len() {
        encoded_concat(s.take(i + n), s.skip(i + n));
        assert(s.take(i + n) + s.skip(i + n) =~= s);
    } else { assert(s.take(i + n) =~= s); }
}

fn make_quantum(input: &[u8], i: usize) -> (r: (usize, [u8; 4]))
    requires i < input.len(),
    ensures 1 <= r.0 <= 3, i + r.0 <= input.len(),
        r.0 == if input.len() - i < 3 { input.len() - i } else { 3int },
        r.1@ == quantum(input@.subrange(i as int, i as int + r.0 as int)),
{
    let n = if input.len() - i < 3 { input.len() - i } else { 3usize };
    let a = input[i];
    let b = if n > 1 { input[i + 1] } else { 0u8 };
    let c = if n > 2 { input[i + 2] } else { 0u8 };
    let q = [to_symbol(a / 4), to_symbol((a % 4) * 16 + b / 16),
        if n > 1 { to_symbol((b % 16) * 4 + c / 64) } else { b'=' },
        if n > 2 { to_symbol(c % 64) } else { b'=' }];
    proof { assert(q@ =~= quantum(input@.subrange(i as int, i as int + n as int))); }
    (n, q)
}

#[verifier::bit_vector]
proof fn encode_batch_bits(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, packed: u64)
    requires packed == ((a as u64) << 40) | ((b as u64) << 32)
        | ((c as u64) << 24) | ((d as u64) << 16) | ((e as u64) << 8) | f as u64,
    ensures packed < 0x1_0000_0000_0000u64,
        ((packed >> 42) & 63) < 64, ((packed >> 42) & 63) as u8 == a / 4,
        ((packed >> 36) & 63) < 64, ((packed >> 36) & 63) as u8 == (a % 4) * 16 + b / 16,
        ((packed >> 30) & 63) < 64, ((packed >> 30) & 63) as u8 == (b % 16) * 4 + c / 64,
        ((packed >> 24) & 63) < 64, ((packed >> 24) & 63) as u8 == c % 64,
        ((packed >> 18) & 63) < 64, ((packed >> 18) & 63) as u8 == d / 4,
        ((packed >> 12) & 63) < 64, ((packed >> 12) & 63) as u8 == (d % 4) * 16 + e / 16,
        ((packed >> 6) & 63) < 64, ((packed >> 6) & 63) as u8 == (e % 16) * 4 + f / 64,
        (packed & 63) < 64, (packed & 63) as u8 == f % 64,
{}

// Two complete groups, packed explicitly so host endianness is irrelevant.
fn make_batch(input: &[u8], i: usize) -> (r: [u8; 8])
    requires i <= input.len(), input.len() - i >= 6,
    ensures r@ == quantum(input@.subrange(i as int, i as int + 3))
        + quantum(input@.subrange(i as int + 3, i as int + 6)),
{
    let a = input[i];
    let b = input[i + 1];
    let c = input[i + 2];
    let d = input[i + 3];
    let e = input[i + 4];
    let f = input[i + 5];
    let packed = ((a as u64) << 40) | ((b as u64) << 32)
        | ((c as u64) << 24) | ((d as u64) << 16)
        | ((e as u64) << 8) | f as u64;
    proof { encode_batch_bits(a, b, c, d, e, f, packed); }
    let v0 = ((packed >> 42) & 63) as u8;
    let v1 = ((packed >> 36) & 63) as u8;
    let v2 = ((packed >> 30) & 63) as u8;
    let v3 = ((packed >> 24) & 63) as u8;
    let v4 = ((packed >> 18) & 63) as u8;
    let v5 = ((packed >> 12) & 63) as u8;
    let v6 = ((packed >> 6) & 63) as u8;
    let v7 = (packed & 63) as u8;
    let bytes = [to_symbol(v0), to_symbol(v1), to_symbol(v2), to_symbol(v3),
        to_symbol(v4), to_symbol(v5), to_symbol(v6), to_symbol(v7)];
    proof {
        assert(bytes@ =~= quantum(input@.subrange(i as int, i as int + 3))
            + quantum(input@.subrange(i as int + 3, i as int + 6)));
    }
    bytes
}

pub open spec fn unquantum(s: Seq<u8>) -> Option<Seq<u8>> {
    if s.len() != 4 { None }
    else {
        match (value(s[0]), value(s[1])) {
            (Some(a), Some(b)) => {
                let x = ((a as int) * 4 + b as int / 16) as u8;
                if s[2] == b'=' {
                    if s[3] == b'=' && b % 16 == 0 { Some(seq![x]) } else { None }
                } else {
                    match value(s[2]) {
                        None => None,
                        Some(c) => {
                            let y = (((b as int) % 16) * 16 + c as int / 4) as u8;
                            if s[3] == b'=' {
                                if c % 4 == 0 { Some(seq![x, y]) } else { None }
                            } else {
                                match value(s[3]) {
                                    Some(d) => Some(seq![x, y, (((c as int) % 4) * 64 + d as int) as u8]),
                                    None => None,
                                }
                            }
                        }
                    }
                }
            }
            _ => None,
        }
    }
}

pub open spec fn first(s: Seq<u8>) -> Option<Seq<u8>> {
    if s.len() < 4 || (s.len() > 4 && (s[2] == b'=' || s[3] == b'=')) { None }
    else { unquantum(s.take(4)) }
}

pub open spec fn decoded(s: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 { Some(Seq::empty()) }
    else if s.len() < 4 { None }
    else {
        match first(s) {
            None => None,
            Some(bytes) => prepend(bytes, decoded(s.skip(4))),
        }
    }
}

fn read_quantum(input: &[u8], i: usize) -> (r: Option<(usize, [u8; 3])>)
    requires i < input.len(),
    ensures match r {
        None => first(input@.skip(i as int)) == None,
        Some((n, bytes)) => 1 <= n <= 3 && i + 4 <= input.len()
            && first(input@.skip(i as int)) == Some(bytes@.take(n as int)),
    },
{
    if input.len() - i < 4 { return None; }
    if input.len() - i > 4 && (input[i + 2] == b'=' || input[i + 3] == b'=') { return None; }
    let a = match from_symbol(input[i]) { Some(v) => v, None => return None };
    let b = match from_symbol(input[i + 1]) { Some(v) => v, None => return None };
    let x = a * 4 + b / 16;
    if input[i + 2] == b'=' {
        if input[i + 3] != b'=' || b % 16 != 0 { return None; }
        Some((1, [x, 0, 0]))
    } else {
        let c = match from_symbol(input[i + 2]) { Some(v) => v, None => return None };
        let y = (b % 16) * 16 + c / 4;
        if input[i + 3] == b'=' {
            if c % 4 != 0 { return None; }
            Some((2, [x, y, 0]))
        } else {
            let d = match from_symbol(input[i + 3]) { Some(v) => v, None => return None };
            Some((3, [x, y, (c % 4) * 64 + d]))
        }
    }
}

proof fn batch_table_matches(c: u8)
    requires value(c).is_some(),
    ensures DECODE_TABLE@[c as int] == value(c).unwrap(), DECODE_TABLE@[c as int] < 64,
{}

#[verifier::bit_vector]
proof fn decode_batch_bits(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, packed: u64)
    requires a < 64, b < 64, c < 64, d < 64, e < 64, f < 64, g < 64, h < 64,
        packed == ((a as u64) << 42) | ((b as u64) << 36) | ((c as u64) << 30)
            | ((d as u64) << 24) | ((e as u64) << 18) | ((f as u64) << 12)
            | ((g as u64) << 6) | h as u64,
    ensures packed < 0x1_0000_0000_0000u64,
        ((packed >> 40) & 255) < 256, ((packed >> 40) & 255) as u8 == a * 4 + b / 16,
        ((packed >> 32) & 255) < 256, ((packed >> 32) & 255) as u8 == (b % 16) * 16 + c / 4,
        ((packed >> 24) & 255) < 256, ((packed >> 24) & 255) as u8 == (c % 4) * 64 + d,
        ((packed >> 16) & 255) < 256, ((packed >> 16) & 255) as u8 == e * 4 + f / 16,
        ((packed >> 8) & 255) < 256, ((packed >> 8) & 255) as u8 == (f % 16) * 16 + g / 4,
        (packed & 255) < 256, (packed & 255) as u8 == (g % 4) * 64 + h,
{}

fn read_batch(input: &[u8], i: usize) -> (r: [u8; 6])
    requires i <= input.len(), input.len() - i >= 12,
        decoded(input@.skip(i as int)).is_some(),
    ensures first(input@.skip(i as int)).is_some(),
        first(input@.skip(i as int)).unwrap().len() == 3,
        first(input@.skip(i as int + 4)).is_some(),
        first(input@.skip(i as int + 4)).unwrap().len() == 3,
        r@ == first(input@.skip(i as int)).unwrap()
            + first(input@.skip(i as int + 4)).unwrap(),
{
    proof {
        assert(input@.skip(i as int).skip(4) =~= input@.skip(i as int + 4));
        assert(decoded(input@.skip(i as int + 4)).is_some());
        assert(first(input@.skip(i as int)).unwrap().len() == 3);
        assert(first(input@.skip(i as int + 4)).unwrap().len() == 3);
        batch_table_matches(input@[i as int + 0]);
        batch_table_matches(input@[i as int + 1]);
        batch_table_matches(input@[i as int + 2]);
        batch_table_matches(input@[i as int + 3]);
        batch_table_matches(input@[i as int + 4]);
        batch_table_matches(input@[i as int + 5]);
        batch_table_matches(input@[i as int + 6]);
        batch_table_matches(input@[i as int + 7]);
    }
    let a = DECODE_TABLE[input[i] as usize];
    let b = DECODE_TABLE[input[i + 1] as usize];
    let c = DECODE_TABLE[input[i + 2] as usize];
    let d = DECODE_TABLE[input[i + 3] as usize];
    let e = DECODE_TABLE[input[i + 4] as usize];
    let f = DECODE_TABLE[input[i + 5] as usize];
    let g = DECODE_TABLE[input[i + 6] as usize];
    let h = DECODE_TABLE[input[i + 7] as usize];
    let packed = ((a as u64) << 42) | ((b as u64) << 36) | ((c as u64) << 30)
        | ((d as u64) << 24) | ((e as u64) << 18) | ((f as u64) << 12)
        | ((g as u64) << 6) | h as u64;
    proof { decode_batch_bits(a, b, c, d, e, f, g, h, packed); }
    let x0 = ((packed >> 40) & 255) as u8;
    let bytes = [x0, ((packed >> 32) & 255) as u8, ((packed >> 24) & 255) as u8,
        ((packed >> 16) & 255) as u8, ((packed >> 8) & 255) as u8, (packed & 255) as u8];
    proof {
        assert(bytes@ =~= first(input@.skip(i as int)).unwrap()
            + first(input@.skip(i as int + 4)).unwrap());
    }
    bytes
}

pub proof fn decoded_step(s: Seq<u8>, i: int, bytes: Seq<u8>)
    requires 0 <= i < s.len(), first(s.skip(i)) == Some(bytes),
    ensures i + 4 <= s.len(), decoded(s.skip(i)) == prepend(bytes, decoded(s.skip(i + 4))),
{
    assert(s.skip(i).skip(4) =~= s.skip(i + 4));
}

fn encoded_length(input: &[u8], capacity: usize) -> (r: Result<usize, Error>)
    ensures r == if encoded(input@).len() <= capacity { Ok(encoded(input@).len() as usize) }
        else { Err(Error::OutputTooSmall) },
{
    // Avoid computing input.len() + 2 in machine arithmetic.
    let quotient = input.len() / 3;
    let groups = if input.len() % 3 == 0 { quotient } else { quotient + 1 };
    proof {
        encoded_size_is_four_per_group(input@);
        assert(groups as int == (input@.len() + 2) / 3);
    }
    if groups > capacity / 4 { Err(Error::OutputTooSmall) }
    else { Ok(groups * 4) }
}

pub fn encode_into(input: &[u8], output: &mut [u8]) -> (r: Result<usize, Error>)
    ensures match r {
        Ok(n) => n == encoded(input@).len() && written(old(output)@, final(output)@, encoded(input@)),
        Err(e) => e == Error::OutputTooSmall && encoded(input@).len() > old(output)@.len()
            && final(output)@ == old(output)@,
    },
{
    let n = match encoded_length(input, output.len()) { Ok(n) => n, Err(e) => return Err(e) };
    let ghost before = output@;
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof { assert(input@.take(0) =~= Seq::<u8>::empty()); written_empty(before); }
    while input.len() - i >= 6
        invariant i <= input.len(), i % 3 == 0, j <= n <= output.len(),
            n == encoded(input@).len(), j == encoded(input@.take(i as int)).len(),
            written(before, output@, encoded(input@.take(i as int))),
        decreases input.len() - i,
    {
        let bytes = make_batch(input, i);
        proof {
            encoded_step(input@, i as int, 3);
            encoded_step(input@, i as int + 3, 3);
            assert(encoded(input@.take(i as int + 6))
                =~= encoded(input@.take(i as int)) + bytes@);
        }
        let ghost current = output@;
        let ghost prefix = encoded(input@.take(i as int));
        copy_bytes(&bytes, output, j);
        proof { extend_written(before, current, output@, prefix, bytes@); }
        i = i + 6;
        j = j + 8;
    }
    while i < input.len()
        invariant i <= input.len(), i % 3 == 0 || i == input.len(), j <= n <= output.len(),
            n == encoded(input@).len(), j == encoded(input@.take(i as int)).len(),
            written(before, output@, encoded(input@.take(i as int))),
        decreases input.len() - i,
    {
        let (amount, bytes) = make_quantum(input, i);
        proof { encoded_step(input@, i as int, amount as int); }
        let ghost current = output@;
        let ghost prefix = encoded(input@.take(i as int));
        copy_bytes(&bytes, output, j);
        proof { extend_written(before, current, output@, prefix, bytes@); }
        i = i + amount;
        j = j + 4;
    }
    proof { assert(input@.take(i as int) =~= input@); }
    Ok(n)
}

proof fn validation_table_matches(c: u8)
    ensures (DECODE_TABLE@[c as int] < 64) == value(c).is_some(),
        value(c).is_some() ==> DECODE_TABLE@[c as int] == value(c).unwrap(),
{}

#[verifier::bit_vector]
proof fn validation_or_bits(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, combined: u8)
    requires combined == a | b | c | d | e | f | g | h,
    ensures (combined < 64) == (a < 64 && b < 64 && c < 64 && d < 64
        && e < 64 && f < 64 && g < 64 && h < 64),
{}

fn valid_batch(input: &[u8], i: usize) -> (r: bool)
    requires i <= input.len(), input.len() - i >= 12,
    ensures r == (first(input@.skip(i as int)).is_some()
        && first(input@.skip(i as int + 4)).is_some()),
        r ==> first(input@.skip(i as int)).unwrap().len() == 3,
        r ==> first(input@.skip(i as int + 4)).unwrap().len() == 3,
{
    let a = DECODE_TABLE[input[i] as usize];
    let b = DECODE_TABLE[input[i + 1] as usize];
    let c = DECODE_TABLE[input[i + 2] as usize];
    let d = DECODE_TABLE[input[i + 3] as usize];
    let e = DECODE_TABLE[input[i + 4] as usize];
    let f = DECODE_TABLE[input[i + 5] as usize];
    let g = DECODE_TABLE[input[i + 6] as usize];
    let h = DECODE_TABLE[input[i + 7] as usize];
    let combined = a | b | c | d | e | f | g | h;
    proof {
        validation_or_bits(a, b, c, d, e, f, g, h, combined);
        validation_table_matches(input@[i as int]);
        validation_table_matches(input@[i as int + 1]);
        validation_table_matches(input@[i as int + 2]);
        validation_table_matches(input@[i as int + 3]);
        validation_table_matches(input@[i as int + 4]);
        validation_table_matches(input@[i as int + 5]);
        validation_table_matches(input@[i as int + 6]);
        validation_table_matches(input@[i as int + 7]);
    }
    combined < 64
}

fn decoded_length(input: &[u8], capacity: usize) -> (r: Result<usize, Error>)
    ensures r == match decoded(input@) {
        None => Err(Error::InvalidInput),
        Some(bytes) => if bytes.len() <= capacity { Ok(bytes.len() as usize) } else { Err(Error::OutputTooSmall) },
    },
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    let mut small = false;
    let ghost mut prefix: Seq<u8> = Seq::empty();
    let ghost mut validation_work: nat = 0;
    proof { assert(input@.skip(0) =~= input@); prepend_empty(decoded(input@)); }
    while input.len() - i >= 12
        invariant i <= input.len(), count <= capacity,
            validation_work == 8 * i,
            !small ==> count == prefix.len(), small ==> prefix.len() > capacity,
            decoded(input@) == prepend(prefix, decoded(input@.skip(i as int))),
        decreases input.len() - i,
    {
        proof {
            validation_work = validation_work + 64;
            assert(validation_work <= 8 * input.len() + 32);
        }
        if !valid_batch(input, i) {
            proof {
                if first(input@.skip(i as int)).is_some() {
                    assert(decoded(input@.skip(i as int + 4)) == None);
                    assert(input@.skip(i as int).skip(4) =~= input@.skip(i as int + 4));
                }
                assert(decoded(input@.skip(i as int)) == None);
            }
            return Err(Error::InvalidInput);
        }
        proof {
            let a = first(input@.skip(i as int)).unwrap();
            let b = first(input@.skip(i as int + 4)).unwrap();
            decoded_step(input@, i as int, a);
            decoded_step(input@, i as int + 4, b);
            prepend_assoc(a, b, decoded(input@.skip(i as int + 8)));
            prepend_assoc(prefix, a + b, decoded(input@.skip(i as int + 8)));
            prefix = prefix + a + b;
        }
        if !small {
            if 6 > capacity - count { small = true; } else { count = count + 6; }
        }
        i = i + 8;
    }
    while i < input.len()
        invariant i <= input.len(), count <= capacity,
            validation_work == 8 * i,
            !small ==> count == prefix.len(), small ==> prefix.len() > capacity,
            decoded(input@) == prepend(prefix, decoded(input@.skip(i as int))),
        decreases input.len() - i,
    {
        proof {
            validation_work = validation_work + 32;
            assert(validation_work <= 8 * input.len() + 32);
        }
        let (amount, _bytes) = match read_quantum(input, i) {
            None => return Err(Error::InvalidInput),
            Some(pair) => pair,
        };
        proof {
            decoded_step(input@, i as int, _bytes@.take(amount as int));
            prepend_assoc(prefix, _bytes@.take(amount as int), decoded(input@.skip(i as int + 4)));
            prefix = prefix + _bytes@.take(amount as int);
        }
        if !small {
            if amount > capacity - count { small = true; } else { count = count + amount; }
        }
        i = i + 4;
    }
    proof { assert(input@.skip(i as int) =~= Seq::<u8>::empty()); prepend_finish(prefix); }
    proof { assert(validation_work <= 8 * input.len() + 32); }
    if small { Err(Error::OutputTooSmall) } else { Ok(count) }
}

pub fn decode_into(input: &[u8], output: &mut [u8]) -> (r: Result<usize, Error>)
    ensures match decoded(input@) {
        None => r == Err(Error::InvalidInput) && final(output)@ == old(output)@,
        Some(bytes) => if bytes.len() > old(output)@.len() {
            r == Err(Error::OutputTooSmall) && final(output)@ == old(output)@
        } else { r == Ok(bytes.len() as usize) && written(old(output)@, final(output)@, bytes) },
    },
{
    let n = match decoded_length(input, output.len()) { Ok(n) => n, Err(e) => return Err(e) };
    let ghost before = output@;
    let ghost mut prefix: Seq<u8> = Seq::empty();
    let mut i: usize = 0;
    let mut j: usize = 0;
    let ghost mut decode_work: nat = 8 * input.len() as nat + 32;
    proof { written_empty(before); assert(input@.skip(0) =~= input@); prepend_empty(decoded(input@)); }
    while input.len() - i >= 12
        invariant i <= input.len(), j <= n <= output.len(), prefix.len() == j,
            decode_work == 8 * input.len() + 4 * j + 32,
            decoded(input@).is_some(), decoded(input@).unwrap().len() == n,
            decoded(input@) == prepend(prefix, decoded(input@.skip(i as int))),
            written(before, output@, prefix),
        decreases input.len() - i,
    {
        proof { assert(decoded(input@.skip(i as int)).is_some()); }
        let bytes = read_batch(input, i);
        proof {
            let first_bytes = first(input@.skip(i as int)).unwrap();
            let second_bytes = first(input@.skip(i as int + 4)).unwrap();
            decoded_step(input@, i as int, first_bytes);
            decoded_step(input@, i as int + 4, second_bytes);
            prepend_assoc(first_bytes, second_bytes, decoded(input@.skip(i as int + 8)));
            prepend_assoc(prefix, bytes@, decoded(input@.skip(i as int + 8)));
            match decoded(input@.skip(i as int + 8)) {
                None => { assert(false); }
                Some(rest) => { assert(n == prefix.len() + 6 + rest.len()); }
            }
        }
        let ghost current = output@;
        copy_bytes(&bytes, output, j);
        proof {
            extend_written(before, current, output@, prefix, bytes@);
            prefix = prefix + bytes@;
            decode_work = decode_work + 24;
        }
        i = i + 8;
        j = j + 6;
    }
    while i < input.len()
        invariant i <= input.len(), j <= n <= output.len(), prefix.len() == j,
            decode_work == 8 * input.len() + 4 * j + 32,
            decoded(input@).is_some(), decoded(input@).unwrap().len() == n,
            decoded(input@) == prepend(prefix, decoded(input@.skip(i as int))),
            written(before, output@, prefix),
        decreases input.len() - i,
    {
        let (amount, bytes) = match read_quantum(input, i) {
            None => { proof { assert(false); } return Err(Error::InvalidInput); }
            Some(pair) => pair,
        };
        proof {
            decoded_step(input@, i as int, bytes@.take(amount as int));
            prepend_assoc(prefix, bytes@.take(amount as int), decoded(input@.skip(i as int + 4)));
            match decoded(input@.skip(i as int + 4)) {
                None => { assert(false); }
                Some(rest) => { assert(n == prefix.len() + amount + rest.len()); }
            }
        }
        let group = &bytes[..amount];
        let ghost current = output@;
        copy_bytes(group, output, j);
        proof {
            extend_written(before, current, output@, prefix, group@);
            prefix = prefix + group@;
            decode_work = decode_work + 4 * amount as nat;
        }
        i = i + 4;
        j = j + amount;
    }
    proof { assert(input@.skip(i as int) =~= Seq::<u8>::empty()); prepend_finish(prefix); }
    proof { assert(decode_work == 8 * input.len() + 4 * n + 32); }
    Ok(n)
}

pub proof fn symbol_inverse(v: u8)
    requires v < 64,
    ensures value(symbol(v)) == Some(v), symbol(v) != b'=',
{}

pub proof fn value_inverse(c: u8)
    requires value(c).is_some(),
    ensures symbol(value(c).unwrap()) == c, value(c).unwrap() < 64,
{}

pub proof fn quantum_round_trip(bytes: Seq<u8>)
    requires 1 <= bytes.len() <= 3,
    ensures unquantum(quantum(bytes)) == Some(bytes),
{
    let a = bytes[0];
    let b = if bytes.len() > 1 { bytes[1] } else { 0u8 };
    let c = if bytes.len() > 2 { bytes[2] } else { 0u8 };
    symbol_inverse(a / 4);
    symbol_inverse(((a % 4) * 16 + b / 16) as u8);
    if bytes.len() > 1 { symbol_inverse(((b % 16) * 4 + c / 64) as u8); }
    if bytes.len() > 2 { symbol_inverse(c % 64); }
    if bytes.len() == 1 { assert(bytes =~= seq![a]); }
    else if bytes.len() == 2 { assert(bytes =~= seq![a, b]); }
    else { assert(bytes =~= seq![a, b, c]); }
}

pub proof fn quantum_canonical(s: Seq<u8>)
    requires s.len() == 4, unquantum(s).is_some(),
    ensures quantum(unquantum(s).unwrap()) == s,
{
    value_inverse(s[0]);
    value_inverse(s[1]);
    if s[2] != b'=' { value_inverse(s[2]); }
    if s[3] != b'=' { value_inverse(s[3]); }
    assert(quantum(unquantum(s).unwrap()) =~= s);
}

pub proof fn round_trip(bytes: Seq<u8>)
    ensures decoded(encoded(bytes)) == Some(bytes),
    decreases bytes.len(),
{
    if bytes.len() == 0 { assert(bytes =~= Seq::<u8>::empty()); }
    else {
        let n = if bytes.len() < 3 { bytes.len() as int } else { 3int };
        let group = bytes.take(n);
        let tail = bytes.skip(n);
        round_trip(tail);
        quantum_round_trip(group);
        let q = quantum(group);
        assert((q + encoded(tail)).take(4) =~= q);
        assert((q + encoded(tail)).skip(4) =~= encoded(tail));
        if n < 3 { assert(tail =~= Seq::<u8>::empty()); }
        else {
            symbol_inverse(((group[1] % 16) * 4 + group[2] / 64) as u8);
            symbol_inverse(group[2] % 64);
        }
        assert(group + tail =~= bytes);
    }
}

pub proof fn canonical_round_trip(text: Seq<u8>)
    requires decoded(text).is_some(),
    ensures encoded(decoded(text).unwrap()) == text,
    decreases text.len(),
{
    if text.len() == 0 { assert(text =~= Seq::<u8>::empty()); }
    else {
        let q = text.take(4);
        let tail = text.skip(4);
        let group = first(text).unwrap();
        assert(group == unquantum(q).unwrap());
        assert(decoded(text) == Some(group + decoded(tail).unwrap()));
        quantum_canonical(q);
        canonical_round_trip(tail);
        assert(1 <= group.len() <= 3);
        assert(group.skip(group.len() as int) =~= Seq::<u8>::empty());
        assert(group.take(group.len() as int) =~= group);
        reveal_with_fuel(encoded, 2);
        assert(encoded(group) == quantum(group));
        if tail.len() > 0 {
            encoded_concat(group, decoded(tail).unwrap());
        } else {
            assert(tail =~= Seq::<u8>::empty());
            assert(group + Seq::<u8>::empty() =~= group);
            assert(group.skip(group.len() as int) =~= Seq::<u8>::empty());
            assert(group.take(group.len() as int) =~= group);
            reveal_with_fuel(encoded, 2);
            assert(encoded(group) == quantum(group));
        }
        assert(q + tail =~= text);
    }
}

// Checked security corollaries of the existing deterministic output contracts.
proof fn encoded_prefix_is_independent_of_previous_output(
    input: Seq<u8>, before_a: Seq<u8>, after_a: Seq<u8>, before_b: Seq<u8>, after_b: Seq<u8>,
)
    requires written(before_a, after_a, encoded(input)), written(before_b, after_b, encoded(input)),
    ensures after_a.take(encoded(input).len() as int) == after_b.take(encoded(input).len() as int),
{}

proof fn decoded_prefix_is_independent_of_previous_output(
    input: Seq<u8>, before_a: Seq<u8>, after_a: Seq<u8>, before_b: Seq<u8>, after_b: Seq<u8>,
)
    requires decoded(input).is_some(),
        written(before_a, after_a, decoded(input).unwrap()),
        written(before_b, after_b, decoded(input).unwrap()),
    ensures after_a.take(decoded(input).unwrap().len() as int)
        == after_b.take(decoded(input).unwrap().len() as int),
{}

pub(crate) proof fn decoded_length_bound(text: Seq<u8>)
    requires decoded(text).is_some(),
    ensures text.len() % 4 == 0, decoded(text).unwrap().len() <= 3 * (text.len() / 4),
    decreases text.len(),
{
    if text.len() > 0 {
        assert(text.len() >= 4);
        assert(first(text).is_some());
        assert(1 <= first(text).unwrap().len() <= 3);
        assert(decoded(text.skip(4)).is_some());
        decoded_length_bound(text.skip(4));
        assert(decoded(text).unwrap().len()
            == first(text).unwrap().len() + decoded(text.skip(4)).unwrap().len());
    }
}

}
