//! RFC 3986 URI-component byte escaping and strict percent decoding.

use crate::Error;
#[cfg(verus_keep_ghost)]
use crate::{
    append_written, prepend, prepend_assoc, prepend_empty, prepend_finish, written, written_empty,
};
use vstd::prelude::*;

verus! {

pub open spec fn unreserved(b: u8) -> bool {
    (b'A' <= b <= b'Z') || (b'a' <= b <= b'z') || (b'0' <= b <= b'9')
        || b == b'-' || b == b'.' || b == b'_' || b == b'~'
}

fn is_unreserved(b: u8) -> (r: bool)
    ensures r == unreserved(b),
{
    (b'A' <= b && b <= b'Z') || (b'a' <= b && b <= b'z')
        || (b'0' <= b && b <= b'9') || b == b'-' || b == b'.' || b == b'_'
        || b == b'~'
}

pub open spec fn hex(n: u8) -> u8 {
    if n < 10 { (b'0' + n) as u8 } else { (b'A' + n - 10) as u8 }
}

fn hex_digit(n: u8) -> (r: u8)
    requires n < 16,
    ensures r == hex(n),
{
    if n < 10 { b'0' + n } else { b'A' + (n - 10) }
}

pub open spec fn hex_value(b: u8) -> Option<u8> {
    if b'0' <= b <= b'9' { Some((b - b'0') as u8) }
    else if b'A' <= b <= b'F' { Some((b - b'A' + 10) as u8) }
    else if b'a' <= b <= b'f' { Some((b - b'a' + 10) as u8) }
    else { None }
}

fn from_hex(b: u8) -> (r: Option<u8>)
    ensures r == hex_value(b), r.is_some() ==> r.unwrap() < 16,
{
    if b'0' <= b && b <= b'9' { Some(b - b'0') }
    else if b'A' <= b && b <= b'F' { Some(b - b'A' + 10) }
    else if b'a' <= b && b <= b'f' { Some(b - b'a' + 10) }
    else { None }
}

pub open spec fn escaped(b: u8) -> Seq<u8> {
    if unreserved(b) { seq![b] } else { seq![b'%', hex(b / 16), hex(b % 16)] }
}

/// Declarative concatenation of independently escaped bytes.
pub open spec fn encoded(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 { Seq::empty() } else { escaped(s[0]) + encoded(s.skip(1)) }
}

pub proof fn encoded_concat(a: Seq<u8>, b: Seq<u8>)
    ensures encoded(a + b) == encoded(a) + encoded(b),
    decreases a.len(),
{
    if a.len() > 0 {
        encoded_concat(a.skip(1), b);
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert(escaped(a[0]) + (encoded(a.skip(1)) + encoded(b))
            =~= (escaped(a[0]) + encoded(a.skip(1))) + encoded(b));
    } else { assert(a =~= Seq::<u8>::empty()); }
}

pub proof fn encoded_step(s: Seq<u8>, i: int)
    requires 0 <= i < s.len(),
    ensures encoded(s.take(i + 1)) == encoded(s.take(i)) + escaped(s[i]),
{
    encoded_concat(s.take(i), seq![s[i]]);
    assert(s.take(i + 1) =~= s.take(i) + seq![s[i]]);
    assert(seq![s[i]].skip(1) =~= Seq::<u8>::empty());
    reveal_with_fuel(encoded, 2);
    assert(encoded(seq![s[i]]) == escaped(s[i]));
}

pub proof fn encoded_prefix_bound(s: Seq<u8>, i: int)
    requires 0 <= i <= s.len(),
    ensures encoded(s.take(i)).len() <= encoded(s).len(),
{
    encoded_concat(s.take(i), s.skip(i));
    assert(s.take(i) + s.skip(i) =~= s);
}

pub open spec fn first(s: Seq<u8>) -> Option<(u8, int)> {
    if s.len() == 0 { None }
    else if s[0] != b'%' { Some((s[0], 1)) }
    else if s.len() < 3 { None }
    else {
        match (hex_value(s[1]), hex_value(s[2])) {
            (Some(h), Some(l)) => Some((((h as int) * 16 + l as int) as u8, 3)),
            _ => None,
        }
    }
}

/// A byte grammar: one literal or one complete %HH escape, followed by a parse.
pub open spec fn decoded(s: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 { Some(Seq::empty()) }
    else {
        match first(s) {
            Some((b, n)) => {
                if 0 < n <= s.len() { prepend(seq![b], decoded(s.skip(n))) }
                else { None }
            }
            None => None,
        }
    }
}

fn read_token(input: &[u8], i: usize) -> (r: Option<(u8, usize)>)
    requires i < input.len(),
    ensures match r {
        Some((b, next)) => i < next <= input.len()
            && first(input@.skip(i as int)) == Some((b, next as int - i as int)),
        None => first(input@.skip(i as int)) == None,
    },
{
    let b = input[i];
    if b != b'%' { return Some((b, i + 1)); }
    if input.len() - i < 3 { return None; }
    match (from_hex(input[i + 1]), from_hex(input[i + 2])) {
        (Some(h), Some(l)) => Some((h * 16 + l, i + 3)),
        _ => None,
    }
}

pub proof fn decoded_step(s: Seq<u8>, i: int, b: u8, next: int)
    requires 0 <= i < next <= s.len(), first(s.skip(i)) == Some((b, next - i)),
    ensures decoded(s.skip(i)) == prepend(seq![b], decoded(s.skip(next))),
{
    assert(s.skip(i).skip(next - i) =~= s.skip(next));
}

fn encoded_length(input: &[u8], capacity: usize) -> (r: Result<usize, Error>)
    ensures r == if encoded(input@).len() <= capacity {
        Ok(encoded(input@).len() as usize)
    } else { Err(Error::OutputTooSmall) },
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    let mut small = false;
    while i < input.len()
        invariant i <= input.len(), count <= capacity,
            !small ==> count == encoded(input@.take(i as int)).len(),
            small ==> encoded(input@.take(i as int)).len() > capacity,
        decreases input.len() - i,
    {
        let width: usize = if is_unreserved(input[i]) { 1 } else { 3 };
        proof { encoded_step(input@, i as int); }
        if !small {
            if width > capacity - count { small = true; }
            else { count = count + width; }
        }
        i = i + 1;
    }
    proof { assert(input@.take(i as int) =~= input@); }
    if small { Err(Error::OutputTooSmall) } else { Ok(count) }
}

pub fn encode_into(input: &[u8], output: &mut [u8]) -> (r: Result<usize, Error>)
    ensures match r {
        Ok(n) => n == encoded(input@).len()
            && written(old(output)@, final(output)@, encoded(input@)),
        Err(e) => e == Error::OutputTooSmall
            && encoded(input@).len() > old(output)@.len() && final(output)@ == old(output)@,
    },
{
    let n = match encoded_length(input, output.len()) {
        Ok(n) => n,
        Err(e) => return Err(e),
    };
    let ghost before = output@;
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        assert(input@.take(0) =~= Seq::<u8>::empty());
        written_empty(before);
    }
    while i < input.len()
        invariant i <= input.len(), j <= n <= output.len(), output@.len() == before.len(),
            n == encoded(input@).len(),
            j == encoded(input@.take(i as int)).len(),
            written(before, output@, encoded(input@.take(i as int))),
        decreases input.len() - i,
    {
        let b = input[i];
        let ghost prefix = encoded(input@.take(i as int));
        proof {
            encoded_step(input@, i as int);
            encoded_prefix_bound(input@, i as int + 1);
        }
        if is_unreserved(b) {
            let ghost current = output@;
            output[j] = b;
            proof {
                append_written(before, current, prefix, b);
                assert(prefix.push(b) =~= prefix + escaped(b));
            }
            j = j + 1;
        } else {
            let h = hex_digit(b / 16);
            let l = hex_digit(b % 16);
            let ghost current = output@;
            output[j] = b'%';
            proof { append_written(before, current, prefix, b'%'); }
            let ghost current = output@;
            output[j + 1] = h;
            proof { append_written(before, current, prefix.push(b'%'), h); }
            let ghost current = output@;
            output[j + 2] = l;
            proof { append_written(before, current, prefix.push(b'%').push(h), l); }
            proof { assert(prefix.push(b'%').push(h).push(l) =~= prefix + escaped(b)); }
            j = j + 3;
        }
        i = i + 1;
    }
    proof { assert(input@.take(i as int) =~= input@); }
    Ok(n)
}

fn decoded_length(input: &[u8], capacity: usize) -> (r: Result<usize, Error>)
    ensures r == match decoded(input@) {
        None => Err(Error::InvalidInput),
        Some(bytes) => if bytes.len() <= capacity { Ok(bytes.len() as usize) }
            else { Err(Error::OutputTooSmall) },
    },
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    let mut small = false;
    let ghost mut prefix: Seq<u8> = Seq::empty();
    let ghost mut validation_work: nat = 0;
    proof {
        assert(input@.skip(0) =~= input@);
        prepend_empty(decoded(input@));
    }
    while i < input.len()
        invariant i <= input.len(), count <= capacity,
            validation_work == 8 * i,
            !small ==> count == prefix.len(), small ==> prefix.len() > capacity,
            decoded(input@) == prepend(prefix, decoded(input@.skip(i as int))),
        decreases input.len() - i,
    {
        let (_b, next) = match read_token(input, i) {
            None => {
                proof {
                    validation_work = 8 * input.len() as nat + 16;
                    assert(validation_work <= 8 * input.len() + 16);
                }
                return Err(Error::InvalidInput);
            }
            Some(pair) => pair,
        };
        proof {
            validation_work = validation_work + 8 * (next - i) as nat;
            decoded_step(input@, i as int, _b, next as int);
            prepend_assoc(prefix, seq![_b], decoded(input@.skip(next as int)));
            assert(prefix + seq![_b] =~= prefix.push(_b));
            prefix = prefix.push(_b);
        }
        if !small {
            if count == capacity { small = true; } else { count = count + 1; }
        }
        i = next;
    }
    proof {
        assert(input@.skip(i as int) =~= Seq::<u8>::empty());
        prepend_finish(prefix);
        assert(validation_work <= 8 * input.len() + 16);
    }
    if small { Err(Error::OutputTooSmall) } else { Ok(count) }
}

pub fn decode_into(input: &[u8], output: &mut [u8]) -> (r: Result<usize, Error>)
    ensures match decoded(input@) {
        None => r == Err(Error::InvalidInput) && final(output)@ == old(output)@,
        Some(bytes) => {
            if bytes.len() > old(output)@.len() {
                r == Err(Error::OutputTooSmall) && final(output)@ == old(output)@
            } else {
                r == Ok(bytes.len() as usize) && written(old(output)@, final(output)@, bytes)
            }
        }
    },
{
    let n = match decoded_length(input, output.len()) {
        Ok(n) => n,
        Err(e) => return Err(e),
    };
    let ghost before = output@;
    let ghost mut prefix: Seq<u8> = Seq::empty();
    let mut i: usize = 0;
    let mut j: usize = 0;
    let ghost mut decode_work: nat = 8 * input.len() as nat + 16;
    proof {
        written_empty(before);
        assert(input@.skip(0) =~= input@);
        prepend_empty(decoded(input@));
    }
    while i < input.len()
        invariant i <= input.len(), j <= n <= output.len(), prefix.len() == j,
            decode_work == 8 * input.len() + 4 * j + 16,
            output@.len() == before.len(),
            decoded(input@).is_some(), decoded(input@).unwrap().len() == n,
            decoded(input@) == prepend(prefix, decoded(input@.skip(i as int))),
            written(before, output@, prefix),
        decreases input.len() - i,
    {
        let (b, next) = match read_token(input, i) {
            None => { proof { assert(false); } return Err(Error::InvalidInput); }
            Some(pair) => pair,
        };
        proof {
            decoded_step(input@, i as int, b, next as int);
            prepend_assoc(prefix, seq![b], decoded(input@.skip(next as int)));
            match decoded(input@.skip(next as int)) {
                None => { assert(false); }
                Some(rest) => { assert(n == prefix.len() + 1 + rest.len()); }
            }
        }
        let ghost current = output@;
        output[j] = b;
        proof {
            append_written(before, current, prefix, b);
            assert(prefix + seq![b] =~= prefix.push(b));
            prefix = prefix.push(b);
            decode_work = decode_work + 4;
        }
        i = next;
        j = j + 1;
    }
    proof {
        assert(input@.skip(i as int) =~= Seq::<u8>::empty());
        prepend_finish(prefix);
        assert(decode_work == 8 * input.len() + 4 * n + 16);
    }
    Ok(n)
}

pub proof fn hex_inverse(n: u8)
    requires n < 16,
    ensures hex_value(hex(n)) == Some(n),
{}

pub proof fn escaped_token(b: u8, tail: Seq<u8>)
    ensures first(escaped(b) + tail) == Some((b, escaped(b).len() as int)),
{
    if !unreserved(b) {
        hex_inverse(b / 16);
        hex_inverse(b % 16);
        assert((b as int / 16) * 16 + (b as int % 16) == b as int);
    }
}

/// Every byte sequence survives encoding followed by strict decoding.
pub proof fn round_trip(bytes: Seq<u8>)
    ensures decoded(encoded(bytes)) == Some(bytes),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let b = bytes[0];
        let tail = bytes.skip(1);
        round_trip(tail);
        escaped_token(b, encoded(tail));
        assert((escaped(b) + encoded(tail)).skip(escaped(b).len() as int) =~= encoded(tail));
        assert(seq![b] + tail =~= bytes);
    } else { assert(bytes =~= Seq::<u8>::empty()); }
}

// Checked byte-observation and expansion corollaries; no new runtime behavior.
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

proof fn encoded_length_bounds(input: Seq<u8>)
    ensures input.len() <= encoded(input).len() <= 3 * input.len(),
    decreases input.len(),
{
    if input.len() > 0 {
        encoded_length_bounds(input.skip(1));
        assert(1 <= escaped(input[0]).len() <= 3);
    }
}

pub(crate) proof fn decoded_length_bound(input: Seq<u8>)
    requires decoded(input).is_some(),
    ensures decoded(input).unwrap().len() <= input.len(),
    decreases input.len(),
{
    if input.len() > 0 {
        assert(first(input).is_some());
        let (byte, next) = first(input).unwrap();
        assert(0 < next <= input.len());
        assert(decoded(input.skip(next)).is_some());
        decoded_length_bound(input.skip(next));
        assert(decoded(input).unwrap().len() == 1 + decoded(input.skip(next)).unwrap().len());
    }
}

}
