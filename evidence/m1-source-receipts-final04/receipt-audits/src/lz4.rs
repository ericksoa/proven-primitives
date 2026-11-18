//! Independent raw LZ4 block decompression into a caller-provided destination.

#[cfg(verus_keep_ghost)]
use crate::{append_written, extend_written, written, written_empty};
use crate::{copy_bytes, Error};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_mod_sub_multiples_vanish, lemma_small_mod};
use vstd::prelude::*;

verus! {

pub open spec fn add_length(n: nat, rest: Option<(nat, int)>) -> Option<(nat, int)> {
    match rest { None => None, Some((m, next)) => Some((n + m, next)) }
}

pub proof fn add_length_assoc(a: nat, b: nat, rest: Option<(nat, int)>)
    ensures add_length(a, add_length(b, rest)) == add_length(a + b, rest),
{}

/// Zero or more 255 extension bytes, terminated by a byte below 255.
pub open spec fn extension(input: Seq<u8>, at: int) -> Option<(nat, int)>
    decreases if 0 <= at <= input.len() { input.len() - at } else { 0int },
{
    if at < 0 || at >= input.len() { None }
    else if input[at] < 255 { Some((input[at] as nat, at + 1)) }
    else { add_length(255, extension(input, at + 1)) }
}

pub open spec fn length_field(input: Seq<u8>, at: int, base: u8) -> Option<(nat, int)> {
    if base < 15 { Some((base as nat, at)) }
    else { add_length(15, extension(input, at)) }
}

fn read_length(input: &[u8], start: usize, base: u8) -> (r: Option<(u128, usize)>)
    requires start <= input.len(), base <= 15,
    ensures match r {
        None => length_field(input@, start as int, base) == None,
        Some((n, next)) => {
            &&& length_field(input@, start as int, base) == Some((n as nat, next as int))
            &&& start <= next <= input.len()
            &&& n as int <= 15 + 255 * (next as int - start as int)
            &&& (base < 15 ==> next == start)
            &&& (base == 15 ==> next > start)
        }
    },
{
    if base < 15 { return Some((base as u128, start)); }
    let mut at = start;
    let mut length: u128 = 15;
    let ghost mut byte_work: nat = 0;
    while at < input.len()
        invariant start <= at <= input.len(), input.len() as int <= u64::MAX as int,
            byte_work == at - start,
            length as int <= 15 + 255 * (at as int - start as int),
            length_field(input@, start as int, base) == add_length(length as nat, extension(input@, at as int)),
        decreases input.len() - at,
    {
        let byte = input[at];
        proof {
            if byte == 255 { add_length_assoc(length as nat, 255, extension(input@, at as int + 1)); }
        }
        at = at + 1;
        proof { byte_work = byte_work + 1; assert(byte_work <= input.len() - start); }
        length = length + byte as u128;
        if byte < 255 { return Some((length, at)); }
    }
    None
}

/// (literal start, literal count, next token, offset, match count, final).
pub open spec fn segment(input: Seq<u8>, at: int, produced: nat, had_match: bool, last_match: nat)
    -> Option<(int, nat, int, nat, nat, bool)>
{
    if at < 0 || at >= input.len() { None }
    else {
        match length_field(input, at + 1, input[at] / 16) {
            None => None,
            Some((literals, start)) => {
                if start < at + 1 || start > input.len() || literals > input.len() - start { None }
                else {
                    let end = start + literals;
                    if end == input.len() {
                        if had_match && (literals < 5 || last_match + literals < 12) { None }
                        else { Some((start, literals, end, 0, 0, true)) }
                    } else if input.len() - end < 2 { None }
                    else {
                        let offset = input[end] as nat + 256 * input[end + 1] as nat;
                        if offset == 0 || offset > produced + literals { None }
                        else {
                            match length_field(input, end + 2, input[at] % 16) {
                                None => None,
                                Some((n, next)) => {
                                    if next < end + 2 || next > input.len() { None }
                                    else { Some((start, literals, next, offset, n + 4, false)) }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
struct Step {
    literal_start: usize,
    literal_len: usize,
    next: usize,
    offset: usize,
    match_len: u128,
    final_block: bool,
}

fn read_step(input: &[u8], at: usize, produced: u128, had_match: bool, last_match: u128)
    -> (r: Option<Step>)
    requires at < input.len(), produced as int <= 512 * at as int, last_match <= produced,
    ensures match r {
        None => segment(input@, at as int, produced as nat, had_match, last_match as nat) == None,
        Some(s) => {
            &&& segment(input@, at as int, produced as nat, had_match, last_match as nat)
                == Some((s.literal_start as int, s.literal_len as nat, s.next as int,
                    s.offset as nat, s.match_len as nat, s.final_block))
            &&& at < s.next <= input.len()
            &&& at < s.literal_start <= input.len()
            &&& s.literal_len <= input.len() - s.literal_start
            &&& s.literal_start as int + s.literal_len as int <= s.next as int
            &&& produced as int + s.literal_len as int + s.match_len as int <= 512 * s.next as int
            &&& (s.final_block ==> s.next == input.len() && s.match_len == 0 && s.offset == 0)
            &&& (!s.final_block ==> 0 < s.offset <= produced + s.literal_len && 4 <= s.match_len)
        }
    },
{
    let token = input[at];
    let (literal_wide, literal_start) = match read_length(input, at + 1, token / 16) {
        Some(pair) => pair, None => return None,
    };
    if literal_wide > (input.len() - literal_start) as u128 { return None; }
    let literal_len = literal_wide as usize;
    let end = literal_start + literal_len;
    if end == input.len() {
        if had_match && (literal_len < 5 || last_match + literal_wide < 12) { return None; }
        return Some(Step { literal_start, literal_len, next: end, offset: 0, match_len: 0, final_block: true });
    }
    if input.len() - end < 2 { return None; }
    let offset = input[end] as usize + (input[end + 1] as usize) * 256;
    if offset == 0 || offset as u128 > produced + literal_wide { return None; }
    let (base_length, next) = match read_length(input, end + 2, token % 16) {
        Some(pair) => pair, None => return None,
    };
    let match_len = base_length + 4;
    Some(Step { literal_start, literal_len, next, offset, match_len, final_block: false })
}

/// LZ4 overlapping copies repeat the preceding offset-byte window.
pub open spec fn matched(prefix: Seq<u8>, offset: nat, count: nat) -> Seq<u8> {
    if offset == 0 || offset > prefix.len() { prefix }
    else { prefix + Seq::new(count, |i: int| prefix[prefix.len() - offset + i % (offset as int)]) }
}

pub proof fn matched_step(prefix: Seq<u8>, offset: nat, count: nat)
    requires 0 < offset <= prefix.len(),
    ensures matched(prefix, offset, count).len() == prefix.len() + count,
        matched(prefix, offset, count + 1)
            == matched(prefix, offset, count).push(matched(prefix, offset, count)[prefix.len() + count - offset]),
{
    let previous = matched(prefix, offset, count);
    if count < offset { lemma_small_mod(count, offset); }
    else { lemma_mod_sub_multiples_vanish(count as int, offset as int); }
    assert(matched(prefix, offset, count + 1).take(previous.len() as int) =~= previous);
    assert(matched(prefix, offset, count + 1) =~= previous.push(previous[prefix.len() + count - offset]));
}

proof fn matched_one_step(prefix: Seq<u8>, count: nat)
    requires prefix.len() > 0,
    ensures matched(prefix, 1, count + 1)
        == matched(prefix, 1, count).push(prefix[prefix.len() - 1]),
{
    matched_step(prefix, 1, count);
    assert(matched(prefix, 1, count)[prefix.len() + count - 1]
        == prefix[prefix.len() - 1]);
}

pub open spec fn block_state(input: Seq<u8>, at: int, prefix: Seq<u8>, had_match: bool, last_match: nat)
    -> Option<Seq<u8>>
    decreases if 0 <= at <= input.len() { input.len() - at } else { 0int },
{
    if at < 0 || at >= input.len() { None }
    else {
        match segment(input, at, prefix.len(), had_match, last_match) {
            None => None,
            Some((start, literals, next, offset, count, last)) => {
                if next <= at || next > input.len() || start < 0 || start + literals > input.len() { None }
                else {
                    let with_literals = prefix + input.subrange(start, start + literals);
                    if last { Some(with_literals) }
                    else { block_state(input, next, matched(with_literals, offset, count), true, count) }
                }
            }
        }
    }
}

pub open spec fn decoded(input: Seq<u8>) -> Option<Seq<u8>> {
    block_state(input, 0, Seq::empty(), false, 0)
}

pub proof fn state_prefix(input: Seq<u8>, at: int, prefix: Seq<u8>, had_match: bool, last_match: nat)
    requires block_state(input, at, prefix, had_match, last_match).is_some(),
    ensures prefix.len() <= block_state(input, at, prefix, had_match, last_match).unwrap().len(),
        block_state(input, at, prefix, had_match, last_match).unwrap().take(prefix.len() as int) == prefix,
    decreases if 0 <= at <= input.len() { input.len() - at } else { 0int },
{
    match segment(input, at, prefix.len(), had_match, last_match) {
        None => { assert(false); }
        Some((start, literals, next, offset, count, last)) => {
            let with_literals = prefix + input.subrange(start, start + literals);
            if !last {
                let after = matched(with_literals, offset, count);
                state_prefix(input, next, after, true, count);
                assert(after.take(prefix.len() as int) =~= prefix);
                assert(block_state(input, next, after, true, count).unwrap().take(prefix.len() as int) =~= prefix);
            } else { assert(with_literals.take(prefix.len() as int) =~= prefix); }
        }
    }
}

fn decoded_length(input: &[u8], capacity: usize) -> (r: Result<usize, Error>)
    ensures r == match decoded(input@) {
        None => Err(Error::InvalidInput),
        Some(bytes) => if bytes.len() <= capacity { Ok(bytes.len() as usize) } else { Err(Error::OutputTooSmall) },
    },
{
    let mut at: usize = 0;
    let mut produced: u128 = 0;
    let mut last_match: u128 = 0;
    let mut had_match = false;
    let ghost mut prefix: Seq<u8> = Seq::empty();
    let ghost mut byte_work: nat = 0;
    while at < input.len()
        invariant at <= input.len(), produced as int <= 512 * at as int,
            byte_work <= at,
            produced == prefix.len(), last_match <= produced,
            decoded(input@) == block_state(input@, at as int, prefix, had_match, last_match as nat),
        decreases input.len() - at,
    {
        let step = match read_step(input, at, produced, had_match, last_match) {
            None => {
                // A failed header can inspect only the remaining input span.
                proof { assert(byte_work + (input.len() - at) <= input.len()); }
                return Err(Error::InvalidInput);
            }
            Some(s) => s,
        };
        proof {
            // Header reads exclude literal payload; both offsets and length
            // extensions lie in this forward, non-overlapping input span.
            byte_work = byte_work + (step.next as int - at as int - step.literal_len as int) as nat;
            assert(byte_work <= step.next);
        }
        let total = produced + step.literal_len as u128 + step.match_len;
        let ghost literals = input@.subrange(step.literal_start as int, step.literal_start as int + step.literal_len as int);
        if step.final_block {
            proof { assert(byte_work <= input.len()); }
            if total > capacity as u128 { return Err(Error::OutputTooSmall); }
            return Ok(total as usize);
        }
        proof { prefix = matched(prefix + literals, step.offset as nat, step.match_len as nat); }
        produced = total;
        last_match = step.match_len;
        had_match = true;
        at = step.next;
    }
    Err(Error::InvalidInput)
}

pub fn decompress_block_into(input: &[u8], output: &mut [u8]) -> (r: Result<usize, Error>)
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
    let ghost mut byte_work: nat = 0;
    let mut at: usize = 0;
    let mut j: usize = 0;
    let mut had_match = false;
    let mut last_match: u128 = 0;
    proof { written_empty(before); }
    while at < input.len()
        invariant at <= input.len(), j <= n <= output.len(), j == prefix.len(),
            byte_work <= at as int + 2 * j as int,
            before == old(output)@,
            j as int <= 512 * at as int, last_match <= j,
            decoded(input@).is_some(), decoded(input@).unwrap().len() == n,
            decoded(input@) == block_state(input@, at as int, prefix, had_match, last_match as nat),
            written(before, output@, prefix),
        decreases input.len() - at,
    {
        let step = match read_step(input, at, j as u128, had_match, last_match) {
            None => { proof { assert(false); } return Err(Error::InvalidInput); }
            Some(s) => s,
        };
        proof {
            byte_work = byte_work + (step.next as int - at as int - step.literal_len as int) as nat;
        }
        let ghost with_literals = prefix + input@.subrange(step.literal_start as int,
            step.literal_start as int + step.literal_len as int);
        let ghost after_match = matched(with_literals, step.offset as nat, step.match_len as nat);
        proof {
            if step.final_block {
                assert(decoded(input@) == Some(with_literals));
            } else {
                state_prefix(input@, step.next as int, after_match, true, step.match_len as nat);
                assert(after_match.len() <= n);
            }
        }
        let literals = &input[step.literal_start..step.literal_start + step.literal_len];
        let ghost current = output@;
        copy_bytes(literals, output, j);
        proof {
            extend_written(before, current, output@, prefix, literals@);
            prefix = with_literals;
            // copy_bytes performs one input read and one output write per byte.
            byte_work = byte_work + 2 * step.literal_len as nat;
        }
        j = j + step.literal_len;
        if step.final_block {
            proof {
                assert(decoded(input@) == Some(prefix));
                assert(n == prefix.len());
                assert(written(before, output@, prefix));
                assert(n <= before.len());
                assert(before == old(output)@);
                assert(byte_work <= input.len() as int + 2 * n as int);
                // Include the first validation pass's checked input-span bound.
                assert(input.len() as int + byte_work <= 2 * input.len() as int + 2 * n as int);
            }
            return Ok(n);
        }
        let count = step.match_len as usize;
        let ghost start = j;
        let ghost prior = prefix;
        let mut copied: usize = 0;
        proof { assert(matched(prior, step.offset as nat, 0) =~= prior); }
        if step.offset == 1 {
            let repeated = output[j - 1];
            let ghost fill_work_start = byte_work;
            proof { byte_work = byte_work + 1; }
            while copied < count
                invariant copied <= count, j == start + copied, j <= n <= output.len(),
                    step.offset == 1, 0 < start == prior.len(),
                    repeated == prior[prior.len() - 1],
                    start + count <= n, 1 <= count,
                    byte_work == fill_work_start + 1 + copied,
                    fill_work_start <= step.next as int + 2 * start as int,
                    before == old(output)@,
                    written(before, output@, matched(prior, 1, copied as nat)),
                decreases count - copied,
            {
                let ghost current = output@;
                proof { matched_one_step(prior, copied as nat); }
                output[j] = repeated;
                proof {
                    append_written(before, current, matched(prior, 1, copied as nat), repeated);
                    byte_work = byte_work + 1;
                }
                copied = copied + 1;
                j = j + 1;
            }
            proof {
                assert(1 + count as int <= 2 * count as int);
                assert(byte_work <= step.next as int + 2 * j as int);
            }
        } else {
            while copied < count
                invariant copied <= count, j == start + copied, j <= n <= output.len(),
                    byte_work <= step.next as int + 2 * j as int,
                    before == old(output)@,
                    start == prior.len(), 0 < step.offset <= start, start + count <= n,
                    written(before, output@, matched(prior, step.offset as nat, copied as nat)),
                decreases count - copied,
            {
                let byte = output[j - step.offset];
                let ghost current = output@;
                proof { matched_step(prior, step.offset as nat, copied as nat); }
                output[j] = byte;
                proof {
                    append_written(before, current, matched(prior, step.offset as nat, copied as nat), byte);
                    byte_work = byte_work + 2;
                }
                copied = copied + 1;
                j = j + 1;
            }
        }
        proof { prefix = after_match; }
        had_match = true;
        last_match = step.match_len;
        at = step.next;
    }
    proof { assert(false); }
    Err(Error::InvalidInput)
}

/// Security corollary of the checked API postcondition: the returned prefix
/// cannot disclose a destination's previous contents (CVE-2026-32829 class).
/// The preserved suffix is deliberately excluded from the observation.
proof fn decoded_prefix_is_independent_of_previous_output(
    input: Seq<u8>,
    before_a: Seq<u8>, after_a: Seq<u8>,
    before_b: Seq<u8>, after_b: Seq<u8>,
)
    requires decoded(input).is_some(),
        written(before_a, after_a, decoded(input).unwrap()),
        written(before_b, after_b, decoded(input).unwrap()),
    ensures after_a.take(decoded(input).unwrap().len() as int)
        == after_b.take(decoded(input).unwrap().len() as int),
{
    let bytes = decoded(input).unwrap();
    assert(after_a.take(bytes.len() as int) =~= bytes);
    assert(after_b.take(bytes.len() as int) =~= bytes);
}

}
