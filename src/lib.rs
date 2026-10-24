//! Byte-processing primitives with explicitly stated correctness contracts.
//!
//! See CONTRACTS.md and the proof-status table before relying on a guarantee.

#![forbid(unsafe_code)]

use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidInput,
    OutputTooSmall,
}

/// The produced prefix is correct and every byte beyond it is preserved.
pub open spec fn written(before: Seq<u8>, after: Seq<u8>, bytes: Seq<u8>) -> bool {
    bytes.len() <= before.len()
        && after == bytes + before.skip(bytes.len() as int)
}

pub proof fn written_empty(before: Seq<u8>)
    ensures written(before, before, Seq::empty()),
{
    assert(before.skip(0) =~= before);
    assert(Seq::<u8>::empty() + before =~= before);
}

/// A single checked write extends a correct prefix by one byte.
pub proof fn append_written(before: Seq<u8>, current: Seq<u8>, prefix: Seq<u8>, b: u8)
    requires written(before, current, prefix), prefix.len() < before.len(),
    ensures written(before, current.update(prefix.len() as int, b), prefix.push(b)),
{
    let next = current.update(prefix.len() as int, b);
    assert(next =~= prefix.push(b) + before.skip(prefix.len() as int + 1));
}

/// Prefixing a successful parse, while propagating a failed parse.
pub open spec fn prepend(prefix: Seq<u8>, rest: Option<Seq<u8>>) -> Option<Seq<u8>> {
    match rest {
        Some(bytes) => Some(prefix + bytes),
        None => None,
    }
}

pub proof fn prepend_assoc(a: Seq<u8>, b: Seq<u8>, rest: Option<Seq<u8>>)
    ensures prepend(a, prepend(b, rest)) == prepend(a + b, rest),
{
    match rest {
        Some(c) => { assert(a + (b + c) =~= (a + b) + c); }
        None => {}
    }
}

pub proof fn prepend_empty(rest: Option<Seq<u8>>)
    ensures prepend(Seq::empty(), rest) == rest,
{
    match rest {
        Some(bytes) => { assert(Seq::<u8>::empty() + bytes =~= bytes); }
        None => {}
    }
}

pub proof fn prepend_finish(prefix: Seq<u8>)
    ensures prepend(prefix, Some(Seq::empty())) == Some(prefix),
{
    assert(prefix + Seq::<u8>::empty() =~= prefix);
}

pub proof fn extend_written(original: Seq<u8>, current: Seq<u8>, after: Seq<u8>, prefix: Seq<u8>, bytes: Seq<u8>)
    requires written(original, current, prefix),
        written(current, after, current.take(prefix.len() as int) + bytes),
    ensures written(original, after, prefix + bytes),
{
    assert(current.take(prefix.len() as int) =~= prefix);
    assert(current.skip(prefix.len() as int + bytes.len() as int)
        =~= original.skip(prefix.len() as int + bytes.len() as int));
}

pub(crate) fn copy_bytes(input: &[u8], output: &mut [u8], start: usize)
    requires start <= old(output)@.len(), input.len() <= old(output)@.len() - start,
    ensures written(old(output)@, final(output)@, old(output)@.take(start as int) + input@),
{
    let ghost before = output@;
    let mut i: usize = 0;
    let ghost mut byte_work: nat = 0;
    proof {
        assert(input@.take(0) =~= Seq::<u8>::empty());
        assert(before.take(start as int) + before.skip(start as int) =~= before);
    }
    while i < input.len()
        invariant i <= input.len(), start <= before.len(), input.len() <= before.len() - start,
            start <= output.len(), input.len() <= output.len() - start,
            byte_work == 2 * i,
            output@.len() == before.len(),
            written(before, output@, before.take(start as int) + input@.take(i as int)),
        decreases input.len() - i,
    {
        let ghost prefix = before.take(start as int) + input@.take(i as int);
        let ghost current = output@;
        let b = input[i];
        output[start + i] = b;
        proof {
            append_written(before, current, prefix, b);
            assert(prefix.push(b) =~= before.take(start as int) + input@.take(i as int + 1));
            byte_work = byte_work + 2;
        }
        i = i + 1;
    }
    proof {
        assert(input@.take(i as int) =~= input@);
        assert(byte_work == 2 * input.len());
    }
}

}

pub mod base64;
mod brotli_block;
mod brotli_input;
mod brotli_prefix;
mod composition_demo;
pub mod lz4;
pub mod percent;
