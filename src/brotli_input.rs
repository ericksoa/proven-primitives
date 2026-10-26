//! Private RFC 7932 streaming input and window-header core.
//!
//! This is not a complete Brotli decoder or a public API. It establishes the
//! pending-bit and terminal-state foundation approved as milestone B1.

#![allow(dead_code)]

use vstd::prelude::*;

verus! {

spec fn byte_bit(byte: u8, bit: int) -> u8 {
    if bit == 0 { byte % 2 }
    else if bit == 1 { (byte / 2) % 2 }
    else if bit == 2 { (byte / 4) % 2 }
    else if bit == 3 { (byte / 8) % 2 }
    else if bit == 4 { (byte / 16) % 2 }
    else if bit == 5 { (byte / 32) % 2 }
    else if bit == 6 { (byte / 64) % 2 }
    else { (byte / 128) % 2 }
}

spec fn byte_bits(byte: u8) -> Seq<u8> {
    seq![byte_bit(byte, 0), byte_bit(byte, 1), byte_bit(byte, 2), byte_bit(byte, 3),
        byte_bit(byte, 4), byte_bit(byte, 5), byte_bit(byte, 6), byte_bit(byte, 7)]
}

spec fn bytes_bits(bytes: Seq<u8>) -> Seq<u8>
    decreases bytes.len(),
{
    if bytes.len() == 0 { Seq::empty() }
    else { byte_bits(bytes[0]) + bytes_bits(bytes.skip(1)) }
}

spec fn bits_value(bits: Seq<u8>) -> nat
    decreases bits.len(),
{
    if bits.len() == 0 { 0 }
    else { bits[0] as nat + 2 * bits_value(bits.skip(1)) }
}

proof fn byte_bits_index(byte: u8, at: int)
    requires 0 <= at < 8,
    ensures byte_bits(byte)[at] == byte_bit(byte, at),
{
    if at == 0 {} else if at == 1 {} else if at == 2 {} else if at == 3 {}
    else if at == 4 {} else if at == 5 {} else if at == 6 {} else {}
}

proof fn bytes_bits_concat(a: Seq<u8>, b: Seq<u8>)
    ensures bytes_bits(a + b) == bytes_bits(a) + bytes_bits(b),
    decreases a.len(),
{
    if a.len() > 0 {
        bytes_bits_concat(a.skip(1), b);
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert(byte_bits(a[0]) + (bytes_bits(a.skip(1)) + bytes_bits(b))
            =~= (byte_bits(a[0]) + bytes_bits(a.skip(1))) + bytes_bits(b));
    } else {
        assert(a =~= Seq::<u8>::empty());
    }
}

proof fn bytes_bits_take_step(bytes: Seq<u8>, at: int)
    requires 0 <= at < bytes.len(),
    ensures bytes_bits(bytes.take(at + 1))
        == bytes_bits(bytes.take(at)) + byte_bits(bytes[at]),
{
    bytes_bits_concat(bytes.take(at), seq![bytes[at]]);
    assert(bytes.take(at + 1) =~= bytes.take(at) + seq![bytes[at]]);
    reveal_with_fuel(bytes_bits, 2);
    assert(bytes_bits(seq![bytes[at]]) == byte_bits(bytes[at]));
}

proof fn bytes_bits_len(bytes: Seq<u8>)
    ensures bytes_bits(bytes).len() == 8 * bytes.len(),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        bytes_bits_len(bytes.skip(1));
    }
}

#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{
    pow2, lemma_pow2_unfold, lemma_pow2_strictly_increases, lemma2_to64,
    lemma2_to64_rest,
};

proof fn bits_value_bound(bits: Seq<u8>)
    requires forall|i: int| 0 <= i < bits.len() ==> bits[i] <= 1,
    ensures bits_value(bits) < pow2(bits.len() as nat),
    decreases bits.len(),
{
    if bits.len() == 0 {
        lemma2_to64();
    } else {
        bits_value_bound(bits.skip(1));
        lemma_pow2_unfold(bits.len() as nat);
        assert(bits_value(bits) == bits[0] as nat + 2 * bits_value(bits.skip(1)));
    }
}

spec fn input_bytes_needed(available: nat, width: nat) -> nat {
    if available >= width { 0 } else { ((width - available + 7) / 8) as nat }
}

spec fn input_bytes_taken(available: nat, width: nat, input_len: nat) -> nat {
    let needed = input_bytes_needed(available, width);
    if input_len < needed { input_len } else { needed }
}

fn get_byte_bit(byte: u8, bit: usize) -> (r: u8)
    requires bit < 8,
    ensures r == byte_bit(byte, bit as int), r <= 1,
{
    if bit == 0 { byte % 2 }
    else if bit == 1 { (byte / 2) % 2 }
    else if bit == 2 { (byte / 4) % 2 }
    else if bit == 3 { (byte / 8) % 2 }
    else if bit == 4 { (byte / 16) % 2 }
    else if bit == 5 { (byte / 32) % 2 }
    else if bit == 6 { (byte / 64) % 2 }
    else { (byte / 128) % 2 }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BitReadStatus {
    Value(u64),
    NeedInput,
    Truncated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BitRead {
    consumed: usize,
    status: BitReadStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BitQueue {
    pending: [u8; 8],
    len: usize,
    offset: usize,
}

impl BitQueue {
    spec fn valid(&self) -> bool {
        self.len <= 8 && self.offset < 8 && (self.len == 0 ==> self.offset == 0)
    }

    spec fn bits(&self) -> Seq<u8> {
        if self.valid() {
            Seq::new((self.len * 8 - self.offset) as nat, |i: int|
                byte_bit(self.pending@[((self.offset as int + i) / 8) as int],
                    (self.offset as int + i) % 8))
        } else {
            Seq::empty()
        }
    }

    fn new() -> (r: Self)
        ensures r.valid(), r.bits().len() == 0,
    {
        Self { pending: [0u8; 8], len: 0, offset: 0 }
    }

    fn reset(&mut self)
        ensures final(self).valid(), final(self).bits().len() == 0,
    {
        self.len = 0;
        self.offset = 0;
    }

    fn bit_at(&self, at: usize) -> (r: u8)
        requires self.valid(), at < self.bits().len(),
        ensures r == self.bits()[at as int], r <= 1,
    {
        let physical = self.offset + at;
        let byte = self.pending[physical / 8];
        get_byte_bit(byte, physical % 8)
    }

    fn append_byte(&mut self, byte: u8)
        requires old(self).valid(), old(self).len < 8,
        ensures final(self).valid(),
            final(self).len == old(self).len + 1,
            final(self).offset == old(self).offset,
            final(self).bits() == old(self).bits() + byte_bits(byte),
    {
        let ghost before = self.bits();
        let ghost old_len = self.len;
        let ghost old_offset = self.offset;
        self.pending[self.len] = byte;
        self.len = self.len + 1;
        proof {
            assert(final(self).bits().len() == before.len() + 8);
            assert(final(self).bits() =~= before + byte_bits(byte)) by {
                assert forall|i: int| 0 <= i < final(self).bits().len()
                    implies final(self).bits()[i] == (before + byte_bits(byte))[i] by {
                    if i < before.len() {
                        assert((old_offset as int + i) / 8 < old_len);
                    } else {
                        let tail = i - before.len();
                        assert(0 <= tail < 8);
                        assert((old_offset as int + i) / 8 == old_len);
                        assert((old_offset as int + i) % 8 == tail);
                        byte_bits_index(byte, tail);
                    }
                }
            }
        }
    }

    fn compact_after(&mut self, consumed_bits: usize)
        requires old(self).valid(), consumed_bits <= old(self).bits().len(),
        ensures final(self).valid(),
            final(self).bits() == old(self).bits().skip(consumed_bits as int),
    {
        let total = self.offset + consumed_bits;
        let drop = total / 8;
        let next_offset = total % 8;
        let old_len = self.len;
        let mut i: usize = 0;
        let ghost mut compact_work: nat = 0;
        while i + drop < old_len
            invariant drop <= old_len <= 8, i <= old_len - drop,
                self.len == old_len, self.offset < 8,
                compact_work == i,
                forall|j: int| 0 <= j < i ==> self.pending@[j] == old(self).pending@[j + drop as int],
                forall|j: int| i <= j < 8 ==> self.pending@[j] == old(self).pending@[j],
            decreases old_len - drop - i,
        {
            let ghost before_write = self.pending@;
            if drop == 0 {
                assert(before_write[i as int] == old(self).pending@[i as int]);
            } else {
                assert(i < i + drop < 8);
                assert(before_write[(i + drop) as int]
                    == old(self).pending@[(i + drop) as int]);
            }
            self.pending[i] = self.pending[i + drop];
            proof {
                assert forall|j: int| 0 <= j < i + 1 implies
                    self.pending@[j] == old(self).pending@[j + drop as int] by {
                    if j < i {
                    } else {
                        assert(j == i);
                    }
                }
                assert forall|j: int| i + 1 <= j < 8 implies
                    self.pending@[j] == old(self).pending@[j] by {
                }
            }
            i = i + 1;
            proof { compact_work = compact_work + 1; }
        }
        self.len = old_len - drop;
        self.offset = if self.len == 0 { 0 } else { next_offset };
        proof {
            assert(compact_work <= 8);
            assert(final(self).bits() =~= old(self).bits().skip(consumed_bits as int)) by {
                assert(final(self).bits().len()
                    == old(self).bits().len() - consumed_bits);
                assert forall|j: int| 0 <= j < final(self).bits().len() implies
                    final(self).bits()[j]
                        == old(self).bits().skip(consumed_bits as int)[j] by {
                    assert((next_offset as int + j) / 8 < old_len - drop);
                    assert(final(self).pending@[(next_offset as int + j) / 8]
                        == old(self).pending@[drop as int + (next_offset as int + j) / 8]);
                    assert((old(self).offset as int + consumed_bits as int + j) / 8
                        == drop as int + (next_offset as int + j) / 8);
                    assert((old(self).offset as int + consumed_bits as int + j) % 8
                        == (next_offset as int + j) % 8);
                }
            }
        }
    }

    fn read_bits(
        &mut self,
        width: usize,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: BitRead)
        requires old(self).valid(), width <= 56,
        ensures final(self).valid(), r.consumed <= input.len(),
            r.consumed as nat
                == input_bytes_taken(old(self).bits().len(), width as nat, input.len() as nat),
            match r.status {
                BitReadStatus::Value(value) => {
                    &&& (old(self).bits() + bytes_bits(input@.take(r.consumed as int))).len() >= width
                    &&& final(self).bits() == (old(self).bits()
                        + bytes_bits(input@.take(r.consumed as int))).skip(width as int)
                    &&& value as nat == bits_value((old(self).bits()
                        + bytes_bits(input@.take(r.consumed as int))).take(width as int))
                    &&& (value as nat) < pow2(width as nat)
                },
                BitReadStatus::NeedInput => {
                    &&& !end_of_input
                    &&& r.consumed == input.len()
                    &&& final(self).bits() == old(self).bits() + bytes_bits(input@)
                    &&& final(self).bits().len() < width
                },
                BitReadStatus::Truncated => {
                    &&& end_of_input
                    &&& r.consumed == input.len()
                    &&& final(self).bits() == old(self).bits() + bytes_bits(input@)
                    &&& final(self).bits().len() < width
                },
            },
    {
        let ghost before = self.bits();
        let ghost old_len = self.len;
        let ghost old_offset = self.offset;
        let available_count = self.len * 8 - self.offset;
        let needed = if available_count >= width {
            0usize
        } else {
            (width - available_count + 7) / 8
        };
        let take = if input.len() < needed { input.len() } else { needed };
        let mut consumed: usize = 0;
        let ghost mut append_work: nat = 0;
        proof {
            assert(needed as nat == input_bytes_needed(before.len(), width as nat));
            assert(take as nat == input_bytes_taken(
                before.len(), width as nat, input.len() as nat));
            assert(needed <= 8 - old_len);
            assert(needed <= 7);
        }
        while consumed < take
            invariant self.valid(), width <= 56, consumed <= take <= input.len(),
                take <= needed, old_len + take <= 8,
                self.len == old_len + consumed, self.offset == old_offset,
                self.bits() == before + bytes_bits(input@.take(consumed as int)),
                append_work == consumed,
            decreases take - consumed,
        {
            assert(self.len < 8);
            let byte = input[consumed];
            self.append_byte(byte);
            consumed = consumed + 1;
            proof {
                bytes_bits_take_step(input@, consumed as int - 1);
                append_work = append_work + 1;
            }
        }
        assert(consumed == take);
        if self.len * 8 - self.offset < width {
            proof {
                assert(append_work <= 7);
                assert(consumed == input.len());
                bytes_bits_len(input@);
                assert(input@.take(consumed as int) =~= input@);
                assert(self.bits() == before + bytes_bits(input@));
                assert(self.bits().len() < width);
            }
            return BitRead {
                consumed,
                status: if end_of_input { BitReadStatus::Truncated } else { BitReadStatus::NeedInput },
            };
        }
        let ghost available = self.bits();
        proof {
            assert forall|j: int| 0 <= j < available.len() implies available[j] <= 1 by {
                let physical = self.offset as int + j;
                assert(0 <= physical % 8 < 8);
                if physical % 8 == 0 {} else if physical % 8 == 1 {}
                else if physical % 8 == 2 {} else if physical % 8 == 3 {}
                else if physical % 8 == 4 {} else if physical % 8 == 5 {}
                else if physical % 8 == 6 {} else {}
            }
        }
        let mut i = width;
        let mut value: u128 = 0;
        let ghost mut extract_work: nat = 0;
        while i > 0
            invariant i <= width <= 56, width <= available.len(),
                self.valid(), available == self.bits(),
                value as nat == bits_value(available.subrange(i as int, width as int)),
                value <= u64::MAX,
                extract_work == width - i,
            decreases i,
        {
            i = i - 1;
            assert(0 <= i < width <= available.len());
            let bit = self.bit_at(i);
            value = value * 2 + bit as u128;
            proof {
                assert(available.subrange(i as int, width as int)[0] == available[i as int]);
                assert(available.subrange(i as int, width as int).skip(1)
                    =~= available.subrange(i as int + 1, width as int));
                assert(bits_value(available.subrange(i as int, width as int))
                    == bit as nat + 2 * bits_value(
                        available.subrange(i as int + 1, width as int)));
                assert forall|j: int| 0 <= j < available.subrange(i as int, width as int).len()
                    implies available.subrange(i as int, width as int)[j] <= 1 by {
                    assert(available.subrange(i as int, width as int)[j]
                        == available[i as int + j]);
                }
                bits_value_bound(available.subrange(i as int, width as int));
                assert(available.subrange(i as int, width as int).len() <= 56);
                lemma_pow2_strictly_increases(
                    available.subrange(i as int, width as int).len() as nat, 64);
                lemma2_to64_rest();
                extract_work = extract_work + 1;
            }
        }
        proof {
            assert(append_work <= 7);
            assert(extract_work <= 56);
            bits_value_bound(available.take(width as int));
            assert((value as nat) < pow2(width as nat));
        }
        self.compact_after(width);
        BitRead { consumed, status: BitReadStatus::Value(value as u64) }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeaderError {
    InvalidHeader,
    Truncated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeaderStatus {
    NeedInput,
    Complete { window_bits: u8, window_size: u32 },
    Failed(HeaderError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeaderPhase {
    First,
    Middle,
    Last,
    Complete { window_bits: u8, window_size: u32 },
    Failed(HeaderError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HeaderStep {
    consumed: usize,
    status: HeaderStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HeaderDecoder {
    queue: BitQueue,
    phase: HeaderPhase,
}

spec fn window_size_for(window_bits: u8) -> u32 {
    ((1u32 << window_bits) - 16) as u32
}

spec fn header_middle(byte: u8) -> nat {
    bits_value(byte_bits(byte).subrange(1, 4))
}

spec fn header_last(byte: u8) -> nat {
    bits_value(byte_bits(byte).subrange(4, 7))
}

spec fn header_used_bits(byte: u8) -> nat {
    if byte_bit(byte, 0) == 0 { 1 }
    else if header_middle(byte) != 0 { 4 }
    else { 7 }
}

spec fn header_status_for_byte(byte: u8) -> HeaderStatus {
    if byte_bit(byte, 0) == 0 {
        HeaderStatus::Complete { window_bits: 16, window_size: window_size_for(16) }
    } else if header_middle(byte) != 0 {
        let window_bits = (17 + header_middle(byte)) as u8;
        HeaderStatus::Complete { window_bits, window_size: window_size_for(window_bits) }
    } else if header_last(byte) == 1 {
        HeaderStatus::Failed(HeaderError::InvalidHeader)
    } else if header_last(byte) == 0 {
        HeaderStatus::Complete { window_bits: 17, window_size: window_size_for(17) }
    } else {
        let window_bits = (8 + header_last(byte)) as u8;
        HeaderStatus::Complete { window_bits, window_size: window_size_for(window_bits) }
    }
}

spec fn phase_status(phase: HeaderPhase) -> Option<HeaderStatus> {
    match phase {
        HeaderPhase::Complete { window_bits, window_size } =>
            Some(HeaderStatus::Complete { window_bits, window_size }),
        HeaderPhase::Failed(error) => Some(HeaderStatus::Failed(error)),
        _ => None,
    }
}

spec fn byte_state(decoder: HeaderDecoder, byte: u8) -> bool {
    match decoder.phase {
        HeaderPhase::Middle => {
            &&& byte_bit(byte, 0) == 1
            &&& decoder.queue.bits() == byte_bits(byte).skip(1)
        },
        HeaderPhase::Last => {
            &&& byte_bit(byte, 0) == 1
            &&& header_middle(byte) == 0
            &&& decoder.queue.bits() == byte_bits(byte).skip(4)
        },
        HeaderPhase::Complete { .. } => {
            &&& phase_status(decoder.phase) == Some(header_status_for_byte(byte))
            &&& decoder.queue.bits() == byte_bits(byte).skip(header_used_bits(byte) as int)
        },
        HeaderPhase::Failed(HeaderError::InvalidHeader) => {
            &&& header_status_for_byte(byte) == HeaderStatus::Failed(HeaderError::InvalidHeader)
            &&& decoder.queue.bits() == byte_bits(byte).skip(7)
        },
        _ => false,
    }
}

#[verifier::bit_vector]
proof fn window_size_safe(window_bits: u8)
    requires 10 <= window_bits <= 24,
    ensures 16 <= (1u32 << window_bits),
        (1u32 << window_bits) - 16 <= u32::MAX,
{}

impl HeaderDecoder {
    spec fn rep_valid(&self) -> bool {
        self.queue.valid()
    }

    spec fn stable_valid(&self) -> bool {
        self.rep_valid() && match self.phase {
            HeaderPhase::First => self.queue.bits().len() == 0,
            HeaderPhase::Complete { window_bits, window_size } =>
                10 <= window_bits <= 24 && window_size == window_size_for(window_bits),
            HeaderPhase::Failed(_) => true,
            _ => false,
        }
    }

    fn new() -> (r: Self)
        ensures r.stable_valid(), r.phase == HeaderPhase::First,
            r.queue.bits().len() == 0,
    {
        Self { queue: BitQueue::new(), phase: HeaderPhase::First }
    }

    fn reset(&mut self)
        ensures final(self).stable_valid(), final(self).phase == HeaderPhase::First,
            final(self).queue.bits().len() == 0,
    {
        self.queue.reset();
        self.phase = HeaderPhase::First;
    }

    fn complete(&mut self, window_bits: u8)
        requires old(self).rep_valid(), 10 <= window_bits <= 24,
        ensures final(self).stable_valid(),
            final(self).phase == (HeaderPhase::Complete {
                window_bits,
                window_size: window_size_for(window_bits),
            }),
            final(self).queue.bits() == old(self).queue.bits(),
    {
        proof { window_size_safe(window_bits); }
        let window_size = (1u32 << window_bits) - 16;
        self.phase = HeaderPhase::Complete { window_bits, window_size };
    }

    #[verifier::rlimit(500)]
    fn advance_header(
        &mut self,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: HeaderStep)
        requires old(self).stable_valid(),
        ensures final(self).stable_valid(), r.consumed <= input.len(),
            match old(self).phase {
                HeaderPhase::First => if input.len() == 0 {
                    &&& r.consumed == 0
                    &&& if end_of_input {
                        r.status == HeaderStatus::Failed(HeaderError::Truncated)
                            && phase_status(final(self).phase) == Some(r.status)
                    } else {
                        &&& r.status == HeaderStatus::NeedInput
                        &&& final(self).phase == HeaderPhase::First
                        &&& final(self).queue.bits().len() == 0
                    }
                } else {
                    &&& r.consumed == 1
                    &&& r.status == header_status_for_byte(input@[0])
                    &&& phase_status(final(self).phase) == Some(r.status)
                    &&& final(self).queue.bits()
                        == byte_bits(input@[0]).skip(header_used_bits(input@[0]) as int)
                },
                HeaderPhase::Complete { window_bits, window_size } =>
                    r == HeaderStep { consumed: 0, status: HeaderStatus::Complete { window_bits, window_size } }
                        && *final(self) == *old(self),
                HeaderPhase::Failed(error) =>
                    r == HeaderStep { consumed: 0, status: HeaderStatus::Failed(error) }
                        && *final(self) == *old(self),
                _ => true,
            },
    {
        let ghost started_phase = self.phase;
        match self.phase {
            HeaderPhase::Complete { window_bits, window_size } => {
                return HeaderStep { consumed: 0, status: HeaderStatus::Complete { window_bits, window_size } };
            }
            HeaderPhase::Failed(error) => {
                return HeaderStep { consumed: 0, status: HeaderStatus::Failed(error) };
            }
            _ => {
                proof {
                    match started_phase {
                        HeaderPhase::Complete { .. } | HeaderPhase::Failed(_) => assert(false),
                        _ => {}
                    }
                }
            }
        }
        proof {
            assert(started_phase == HeaderPhase::First);
            assert(self.queue.bits().len() == 0);
        }

        let first_read = self.queue.read_bits(1, input, end_of_input);
        let first = match first_read.status {
            BitReadStatus::NeedInput => {
                proof {
                    assert(input.len() == 0);
                    assert(first_read.consumed == 0);
                    assert(!end_of_input);
                    assert(self.queue.bits().len() == 0);
                }
                return HeaderStep { consumed: 0, status: HeaderStatus::NeedInput };
            }
            BitReadStatus::Truncated => {
                self.phase = HeaderPhase::Failed(HeaderError::Truncated);
                proof {
                    assert(input.len() == 0);
                    assert(first_read.consumed == 0);
                    assert(end_of_input);
                    assert(self.stable_valid());
                    assert(phase_status(self.phase)
                        == Some(HeaderStatus::Failed(HeaderError::Truncated)));
                }
                return HeaderStep { consumed: 0, status: HeaderStatus::Failed(HeaderError::Truncated) };
            }
            BitReadStatus::Value(value) => value,
        };

        let ghost byte = input@[0];
        proof {
            lemma2_to64();
            assert(input.len() > 0);
            assert(first_read.consumed == 1);
            reveal_with_fuel(bytes_bits, 2);
            assert(input@.take(1) =~= seq![byte]);
            assert(bytes_bits(input@.take(1)) == byte_bits(byte));
            assert(first as nat == bits_value(byte_bits(byte).take(1)));
            assert(first as nat == byte_bit(byte, 0) as nat);
            assert(first < 2);
            assert(self.queue.bits() == byte_bits(byte).skip(1));
        }
        if first == 0 {
            self.complete(16);
            let status = HeaderStatus::Complete { window_bits: 16, window_size: 65_520 };
            proof {
                reveal(window_size_for);
                assert(window_size_for(16) == 65_520) by (bit_vector);
                assert(status == header_status_for_byte(byte));
                assert(header_used_bits(byte) == 1);
                assert(phase_status(self.phase) == Some(status));
            }
            return HeaderStep { consumed: 1, status };
        }

        self.phase = HeaderPhase::Middle;
        let ghost middle_before = self.queue.bits();
        let middle_read = self.queue.read_bits(3, &input[1..], end_of_input);
        let middle = match middle_read.status {
            BitReadStatus::Value(value) => value,
            _ => { proof { assert(false); } 0 },
        };
        proof {
            lemma2_to64();
            assert(middle_read.consumed == 0);
            assert(middle_before == byte_bits(byte).skip(1));
            assert(middle as nat == bits_value(middle_before.take(3)));
            assert(middle_before.take(3) =~= byte_bits(byte).subrange(1, 4));
            assert(middle as nat == header_middle(byte));
            assert(middle < 8);
            assert(self.queue.bits() == byte_bits(byte).skip(4));
        }
        if middle != 0 {
            let digit = middle as u8;
            let window_bits = 17 + digit;
            assert(18 <= window_bits <= 24);
            self.complete(window_bits);
            let window_size = match self.phase {
                HeaderPhase::Complete { window_size, .. } => window_size,
                _ => { proof { assert(false); } 0 },
            };
            let status = HeaderStatus::Complete { window_bits, window_size };
            proof {
                assert(status == header_status_for_byte(byte));
                assert(header_used_bits(byte) == 4);
                assert(phase_status(self.phase) == Some(status));
            }
            return HeaderStep { consumed: 1, status };
        }

        self.phase = HeaderPhase::Last;
        let ghost last_before = self.queue.bits();
        let last_read = self.queue.read_bits(3, &input[1..], end_of_input);
        let last = match last_read.status {
            BitReadStatus::Value(value) => value,
            _ => { proof { assert(false); } 0 },
        };
        proof {
            lemma2_to64();
            assert(last_read.consumed == 0);
            assert(last_before == byte_bits(byte).skip(4));
            assert(last as nat == bits_value(last_before.take(3)));
            assert(last_before.take(3) =~= byte_bits(byte).subrange(4, 7));
            assert(last as nat == header_last(byte));
            assert(last < 8);
            assert(self.queue.bits() == byte_bits(byte).skip(7));
            assert(header_used_bits(byte) == 7);
        }
        if last == 1 {
            self.phase = HeaderPhase::Failed(HeaderError::InvalidHeader);
            let status = HeaderStatus::Failed(HeaderError::InvalidHeader);
            proof {
                assert(status == header_status_for_byte(byte));
                assert(self.stable_valid());
                assert(phase_status(self.phase) == Some(status));
            }
            HeaderStep { consumed: 1, status }
        } else {
            let window_bits = if last == 0 { 17u8 } else { 8u8 + last as u8 };
            assert(10 <= window_bits <= 17);
            self.complete(window_bits);
            let window_size = match self.phase {
                HeaderPhase::Complete { window_size, .. } => window_size,
                _ => { proof { assert(false); } 0 },
            };
            let status = HeaderStatus::Complete { window_bits, window_size };
            proof {
                assert(status == header_status_for_byte(byte));
                assert(phase_status(self.phase) == Some(status));
            }
            HeaderStep { consumed: 1, status }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetaBlockError {
    HeaderNotReady,
    Truncated,
    ReservedBit,
    ExuberantLength,
    ExuberantMetadataLength,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MetaBlockHeader {
    is_last: bool,
    is_empty: bool,
    is_uncompressed: bool,
    is_metadata: bool,
    length: u32,
}

impl MetaBlockHeader {
    spec fn valid(&self) -> bool {
        &&& self.length <= 16_777_216
        &&& (self.is_empty ==> {
            &&& self.is_last
            &&& !self.is_uncompressed
            &&& !self.is_metadata
            &&& self.length == 0
        })
        &&& (self.is_metadata ==> {
            &&& !self.is_empty
            &&& !self.is_uncompressed
        })
        &&& (!self.is_empty && !self.is_metadata ==> 1 <= self.length)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetaBlockPhase {
    Last,
    Empty,
    Nibbles { is_last: bool },
    Size {
        is_last: bool,
        nibbles: u8,
        index: u8,
        value: u32,
    },
    Uncompressed { is_last: bool, value: u32 },
    Reserved { is_last: bool },
    MetadataBytes { is_last: bool },
    MetadataSize {
        is_last: bool,
        bytes: u8,
        index: u8,
        value: u32,
    },
    Complete(MetaBlockHeader),
    Failed(MetaBlockError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MetaBlockStatus {
    Progress,
    NeedInput,
    Complete(MetaBlockHeader),
    Failed(MetaBlockError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MetaBlockStep {
    consumed: usize,
    status: MetaBlockStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MetaBlockDecoder {
    queue: BitQueue,
    phase: MetaBlockPhase,
}

spec fn meta_phase_width(phase: MetaBlockPhase) -> nat {
    match phase {
        MetaBlockPhase::Last | MetaBlockPhase::Empty | MetaBlockPhase::Reserved { .. } => 1,
        MetaBlockPhase::Nibbles { .. } | MetaBlockPhase::MetadataBytes { .. } => 2,
        MetaBlockPhase::Size { .. } => 4,
        MetaBlockPhase::Uncompressed { is_last, .. } => if is_last { 0 } else { 1 },
        MetaBlockPhase::MetadataSize { .. } => 8,
        MetaBlockPhase::Complete(_) | MetaBlockPhase::Failed(_) => 0,
    }
}

spec fn meta_phase_terminal(phase: MetaBlockPhase) -> bool {
    match phase {
        MetaBlockPhase::Complete(_) | MetaBlockPhase::Failed(_) => true,
        _ => false,
    }
}

spec fn meta_transition(
    phase: MetaBlockPhase,
    field: nat,
) -> (MetaBlockPhase, MetaBlockStatus) {
    match phase {
        MetaBlockPhase::Last => {
            let next = if field == 0 {
                MetaBlockPhase::Nibbles { is_last: false }
            } else {
                MetaBlockPhase::Empty
            };
            (next, MetaBlockStatus::Progress)
        },
        MetaBlockPhase::Empty => {
            if field != 0 {
                let header = MetaBlockHeader {
                    is_last: true,
                    is_empty: true,
                    is_uncompressed: false,
                    is_metadata: false,
                    length: 0,
                };
                (MetaBlockPhase::Complete(header), MetaBlockStatus::Complete(header))
            } else {
                (MetaBlockPhase::Nibbles { is_last: true }, MetaBlockStatus::Progress)
            }
        },
        MetaBlockPhase::Nibbles { is_last } => {
            if field == 3 {
                (MetaBlockPhase::Reserved { is_last }, MetaBlockStatus::Progress)
            } else {
                (MetaBlockPhase::Size {
                    is_last,
                    nibbles: (field + 4) as u8,
                    index: 0,
                    value: 0,
                }, MetaBlockStatus::Progress)
            }
        },
        MetaBlockPhase::Size { is_last, nibbles, index, value } => {
            if index + 1 == nibbles && nibbles > 4 && field == 0 {
                (MetaBlockPhase::Failed(MetaBlockError::ExuberantLength),
                    MetaBlockStatus::Failed(MetaBlockError::ExuberantLength))
            } else {
                let next = value | ((field as u32) << (4 * index));
                if index + 1 == nibbles {
                    (MetaBlockPhase::Uncompressed { is_last, value: next },
                        MetaBlockStatus::Progress)
                } else {
                    (MetaBlockPhase::Size {
                        is_last,
                        nibbles,
                        index: (index as int + 1) as u8,
                        value: next,
                    }, MetaBlockStatus::Progress)
                }
            }
        },
        MetaBlockPhase::Uncompressed { is_last, value } => {
            let header = MetaBlockHeader {
                is_last,
                is_empty: false,
                is_uncompressed: !is_last && field != 0,
                is_metadata: false,
                length: (value as int + 1) as u32,
            };
            (MetaBlockPhase::Complete(header), MetaBlockStatus::Complete(header))
        },
        MetaBlockPhase::Reserved { is_last } => {
            if field != 0 {
                (MetaBlockPhase::Failed(MetaBlockError::ReservedBit),
                    MetaBlockStatus::Failed(MetaBlockError::ReservedBit))
            } else {
                (MetaBlockPhase::MetadataBytes { is_last }, MetaBlockStatus::Progress)
            }
        },
        MetaBlockPhase::MetadataBytes { is_last } => {
            if field == 0 {
                let header = MetaBlockHeader {
                    is_last,
                    is_empty: false,
                    is_uncompressed: false,
                    is_metadata: true,
                    length: 0,
                };
                (MetaBlockPhase::Complete(header), MetaBlockStatus::Complete(header))
            } else {
                (MetaBlockPhase::MetadataSize {
                    is_last,
                    bytes: field as u8,
                    index: 0,
                    value: 0,
                }, MetaBlockStatus::Progress)
            }
        },
        MetaBlockPhase::MetadataSize { is_last, bytes, index, value } => {
            if index + 1 == bytes && bytes > 1 && field == 0 {
                (MetaBlockPhase::Failed(MetaBlockError::ExuberantMetadataLength),
                    MetaBlockStatus::Failed(MetaBlockError::ExuberantMetadataLength))
            } else {
                let next = value | ((field as u32) << (8 * index));
                if index + 1 == bytes {
                    let header = MetaBlockHeader {
                        is_last,
                        is_empty: false,
                        is_uncompressed: false,
                        is_metadata: true,
                        length: (next as int + 1) as u32,
                    };
                    (MetaBlockPhase::Complete(header), MetaBlockStatus::Complete(header))
                } else {
                    (MetaBlockPhase::MetadataSize {
                        is_last,
                        bytes,
                        index: (index as int + 1) as u8,
                        value: next,
                    }, MetaBlockStatus::Progress)
                }
            }
        },
        MetaBlockPhase::Complete(header) =>
            (phase, MetaBlockStatus::Complete(header)),
        MetaBlockPhase::Failed(error) =>
            (phase, MetaBlockStatus::Failed(error)),
    }
}

proof fn pow2_width_at_most_byte(width: nat)
    requires width <= 8,
    ensures pow2(width) <= 256,
{
    lemma2_to64();
    if width < 8 {
        lemma_pow2_strictly_increases(width, 8);
    }
}

#[verifier::bit_vector]
proof fn extend_nibble_is_bounded(value: u32, digit: u32, index: u8)
    requires index < 6,
        value < (1u32 << (4 * index)),
        digit < 16,
    ensures (value | (digit << (4 * index))) < (1u32 << (4 * (index + 1))),
        (value | (digit << (4 * index))) < 16_777_216,
{
}

#[verifier::bit_vector]
proof fn extend_metadata_byte_is_bounded(value: u32, byte: u32, index: u8)
    requires index < 3,
        value < (1u32 << (8 * index)),
        byte < 256,
    ensures (value | (byte << (8 * index))) < (1u32 << (8 * (index + 1))),
        (value | (byte << (8 * index))) < 16_777_216,
{
}

impl MetaBlockDecoder {
    spec fn valid(&self) -> bool {
        &&& self.queue.valid()
        &&& match self.phase {
            MetaBlockPhase::Size { nibbles, index, value, .. } => {
                &&& 4 <= nibbles <= 6
                &&& index < nibbles
                &&& value < (1u32 << (4 * index))
            },
            MetaBlockPhase::Uncompressed { value, .. } => value < 16_777_216,
            MetaBlockPhase::MetadataSize { bytes, index, value, .. } => {
                &&& 1 <= bytes <= 3
                &&& index < bytes
                &&& value < (1u32 << (8 * index))
            },
            MetaBlockPhase::Complete(header) => header.valid(),
            _ => true,
        }
    }

    fn from_header(header: HeaderDecoder) -> (r: Result<Self, MetaBlockError>)
        requires header.stable_valid(),
        ensures r.is_ok() ==> {
            &&& r.unwrap().valid()
            &&& r.unwrap().queue == header.queue
            &&& r.unwrap().phase == MetaBlockPhase::Last
        },
    {
        match header.phase {
            HeaderPhase::Complete { .. } => Ok(Self {
                queue: header.queue,
                phase: MetaBlockPhase::Last,
            }),
            _ => Err(MetaBlockError::HeaderNotReady),
        }
    }

    fn reset_after_header(&mut self, header: HeaderDecoder) -> (r: Result<(), MetaBlockError>)
        requires old(self).valid(), header.stable_valid(),
        ensures r.is_ok() ==> {
            &&& final(self).valid()
            &&& final(self).queue == header.queue
            &&& final(self).phase == MetaBlockPhase::Last
        },
    {
        match header.phase {
            HeaderPhase::Complete { .. } => {
                self.queue = header.queue;
                self.phase = MetaBlockPhase::Last;
                Ok(())
            }
            _ => Err(MetaBlockError::HeaderNotReady),
        }
    }

    fn fail(&mut self, error: MetaBlockError) -> (r: MetaBlockStep)
        requires old(self).queue.valid(),
        ensures final(self).valid(),
            final(self).queue == old(self).queue,
            final(self).phase == MetaBlockPhase::Failed(error),
            r == (MetaBlockStep { consumed: 0, status: MetaBlockStatus::Failed(error) }),
    {
        self.phase = MetaBlockPhase::Failed(error);
        MetaBlockStep { consumed: 0, status: MetaBlockStatus::Failed(error) }
    }

    #[verifier::rlimit(500)]
    fn advance_field(
        &mut self,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: MetaBlockStep)
        requires old(self).valid(),
        ensures final(self).valid(), r.consumed <= input.len(),
            match old(self).phase {
                MetaBlockPhase::Complete(header) => {
                    &&& r == (MetaBlockStep { consumed: 0, status: MetaBlockStatus::Complete(header) })
                    &&& *final(self) == *old(self)
                },
                MetaBlockPhase::Failed(error) => {
                    &&& r == (MetaBlockStep { consumed: 0, status: MetaBlockStatus::Failed(error) })
                    &&& *final(self) == *old(self)
                },
                _ => true,
            },
            r.status == MetaBlockStatus::NeedInput ==> {
                &&& !end_of_input
                &&& r.consumed == input.len()
            },
            match r.status {
                MetaBlockStatus::Complete(header) => {
                    &&& header.valid()
                    &&& final(self).phase == MetaBlockPhase::Complete(header)
                },
                MetaBlockStatus::Failed(error) =>
                    final(self).phase == MetaBlockPhase::Failed(error),
                _ => true,
            },
            !meta_phase_terminal(old(self).phase) ==> {
                let width = meta_phase_width(old(self).phase);
                let available = old(self).queue.bits()
                    + bytes_bits(input@.take(r.consumed as int));
                &&& available.len() >= width ==> {
                    let expected = meta_transition(
                        old(self).phase,
                        bits_value(available.take(width as int)),
                    );
                    &&& final(self).phase == expected.0
                    &&& r.status == expected.1
                }
            },
    {
        let phase = self.phase;
        match phase {
            MetaBlockPhase::Complete(header) => {
                return MetaBlockStep { consumed: 0, status: MetaBlockStatus::Complete(header) };
            }
            MetaBlockPhase::Failed(error) => {
                return MetaBlockStep { consumed: 0, status: MetaBlockStatus::Failed(error) };
            }
            _ => {}
        }

        let width: usize = match phase {
            MetaBlockPhase::Last => 1,
            MetaBlockPhase::Empty => 1,
            MetaBlockPhase::Nibbles { .. } => 2,
            MetaBlockPhase::Size { .. } => 4,
            MetaBlockPhase::Uncompressed { is_last, .. } => if is_last { 0 } else { 1 },
            MetaBlockPhase::Reserved { .. } => 1,
            MetaBlockPhase::MetadataBytes { .. } => 2,
            MetaBlockPhase::MetadataSize { .. } => 8,
            MetaBlockPhase::Complete(_) | MetaBlockPhase::Failed(_) => {
                proof { assert(false); }
                0
            }
        };

        let read = self.queue.read_bits(width, input, end_of_input);
        let bits = match read.status {
            BitReadStatus::Value(value) => {
                proof {
                    assert(width <= 8);
                    pow2_width_at_most_byte(width as nat);
                    assert(value < 256);
                }
                value as u32
            }
            BitReadStatus::NeedInput => {
                return MetaBlockStep { consumed: read.consumed, status: MetaBlockStatus::NeedInput };
            }
            BitReadStatus::Truncated => {
                self.phase = MetaBlockPhase::Failed(MetaBlockError::Truncated);
                return MetaBlockStep {
                    consumed: read.consumed,
                    status: MetaBlockStatus::Failed(MetaBlockError::Truncated),
                };
            }
        };
        proof {
            lemma2_to64();
            assert((bits as nat) < pow2(width as nat));
        }

        let mut status = MetaBlockStatus::Progress;
        match phase {
            MetaBlockPhase::Last => {
                self.phase = if bits == 0 {
                    MetaBlockPhase::Nibbles { is_last: false }
                } else {
                    MetaBlockPhase::Empty
                };
                assert(self.valid());
            }
            MetaBlockPhase::Empty => {
                if bits != 0 {
                    let header = MetaBlockHeader {
                        is_last: true,
                        is_empty: true,
                        is_uncompressed: false,
                        is_metadata: false,
                        length: 0,
                    };
                    self.phase = MetaBlockPhase::Complete(header);
                    status = MetaBlockStatus::Complete(header);
                } else {
                    self.phase = MetaBlockPhase::Nibbles { is_last: true };
                }
                assert(self.valid());
            }
            MetaBlockPhase::Nibbles { is_last } => {
                assert(width == 2);
                assert(bits < 4);
                if bits == 3 {
                    self.phase = MetaBlockPhase::Reserved { is_last };
                } else {
                    let nibbles = bits as u8 + 4;
                    assert(4 <= nibbles <= 6);
                    assert(0u32 < (1u32 << 0)) by (bit_vector);
                    self.phase = MetaBlockPhase::Size {
                        is_last,
                        nibbles,
                        index: 0,
                        value: 0,
                    };
                }
                assert(self.valid());
            }
            MetaBlockPhase::Size { is_last, nibbles, index, value } => {
                assert(width == 4);
                assert(bits < 16);
                if index + 1 == nibbles && nibbles > 4 && bits == 0 {
                    self.phase = MetaBlockPhase::Failed(MetaBlockError::ExuberantLength);
                    status = MetaBlockStatus::Failed(MetaBlockError::ExuberantLength);
                } else {
                    proof { extend_nibble_is_bounded(value, bits, index); }
                    let next = value | (bits << (4 * index));
                    if index + 1 == nibbles {
                        self.phase = MetaBlockPhase::Uncompressed { is_last, value: next };
                    } else {
                        self.phase = MetaBlockPhase::Size {
                            is_last,
                            nibbles,
                            index: index + 1,
                            value: next,
                        };
                    }
                }
                assert(self.valid());
            }
            MetaBlockPhase::Uncompressed { is_last, value } => {
                let header = MetaBlockHeader {
                    is_last,
                    is_empty: false,
                    is_uncompressed: !is_last && bits != 0,
                    is_metadata: false,
                    length: value + 1,
                };
                self.phase = MetaBlockPhase::Complete(header);
                status = MetaBlockStatus::Complete(header);
                assert(self.valid());
            }
            MetaBlockPhase::Reserved { is_last } => {
                if bits != 0 {
                    self.phase = MetaBlockPhase::Failed(MetaBlockError::ReservedBit);
                    status = MetaBlockStatus::Failed(MetaBlockError::ReservedBit);
                } else {
                    self.phase = MetaBlockPhase::MetadataBytes { is_last };
                }
                assert(self.valid());
            }
            MetaBlockPhase::MetadataBytes { is_last } => {
                assert(width == 2);
                assert(bits < 4);
                if bits == 0 {
                    let header = MetaBlockHeader {
                        is_last,
                        is_empty: false,
                        is_uncompressed: false,
                        is_metadata: true,
                        length: 0,
                    };
                    self.phase = MetaBlockPhase::Complete(header);
                    status = MetaBlockStatus::Complete(header);
                } else {
                    let bytes = bits as u8;
                    assert(1 <= bytes <= 3);
                    assert(0u32 < (1u32 << 0)) by (bit_vector);
                    self.phase = MetaBlockPhase::MetadataSize {
                        is_last,
                        bytes,
                        index: 0,
                        value: 0,
                    };
                }
                assert(self.valid());
            }
            MetaBlockPhase::MetadataSize { is_last, bytes, index, value } => {
                assert(width == 8);
                assert(bits < 256);
                if index + 1 == bytes && bytes > 1 && bits == 0 {
                    self.phase = MetaBlockPhase::Failed(MetaBlockError::ExuberantMetadataLength);
                    status = MetaBlockStatus::Failed(MetaBlockError::ExuberantMetadataLength);
                } else {
                    proof { extend_metadata_byte_is_bounded(value, bits, index); }
                    let next = value | (bits << (8 * index));
                    if index + 1 == bytes {
                        let header = MetaBlockHeader {
                            is_last,
                            is_empty: false,
                            is_uncompressed: false,
                            is_metadata: true,
                            length: next + 1,
                        };
                        self.phase = MetaBlockPhase::Complete(header);
                        status = MetaBlockStatus::Complete(header);
                    } else {
                        self.phase = MetaBlockPhase::MetadataSize {
                            is_last,
                            bytes,
                            index: index + 1,
                            value: next,
                        };
                    }
                }
                assert(self.valid());
            }
            MetaBlockPhase::Complete(_) | MetaBlockPhase::Failed(_) => {
                proof { assert(false); }
            }
        }
        MetaBlockStep { consumed: read.consumed, status }
    }
}

const CODE_LENGTH_ORDER: [u8; 18] = [
    1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15,
];

proof fn code_length_order_is_rfc()
    ensures CODE_LENGTH_ORDER@[0] == 1,
        CODE_LENGTH_ORDER@[1] == 2,
        CODE_LENGTH_ORDER@[2] == 3,
        CODE_LENGTH_ORDER@[3] == 4,
        CODE_LENGTH_ORDER@[4] == 0,
        CODE_LENGTH_ORDER@[5] == 5,
        CODE_LENGTH_ORDER@[6] == 17,
        CODE_LENGTH_ORDER@[7] == 6,
        CODE_LENGTH_ORDER@[8] == 16,
        CODE_LENGTH_ORDER@[9] == 7,
        CODE_LENGTH_ORDER@[10] == 8,
        CODE_LENGTH_ORDER@[11] == 9,
        CODE_LENGTH_ORDER@[12] == 10,
        CODE_LENGTH_ORDER@[13] == 11,
        CODE_LENGTH_ORDER@[14] == 12,
        CODE_LENGTH_ORDER@[15] == 13,
        CODE_LENGTH_ORDER@[16] == 14,
        CODE_LENGTH_ORDER@[17] == 15,
{
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CodeDescriptionError {
    MetaBlockNotCompressed,
    InvalidAlphabet,
    DuplicateSimpleSymbol,
    CodeLengthSpace,
    Truncated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SimpleCodeDescription {
    selector: u8,
    count: u8,
    symbols: [u16; 4],
}

spec fn simple_count(selector: u8) -> nat {
    if selector <= 2 { selector as nat + 1 } else { 4 }
}

spec fn active_symbols_distinct(symbols: Seq<u16>, count: nat) -> bool {
    forall|i: int, j: int| 0 <= i < count && 0 <= j < count && i != j
        ==> symbols[i] != symbols[j]
}

impl SimpleCodeDescription {
    spec fn valid(&self, alphabet_limit: u16) -> bool {
        &&& 1 <= alphabet_limit <= 704
        &&& self.selector <= 4
        &&& self.count as nat == simple_count(self.selector)
        &&& forall|i: int| 0 <= i < self.count ==> self.symbols@[i] < alphabet_limit
        &&& active_symbols_distinct(self.symbols@, self.count as nat)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ComplexCodeLengthAlphabet {
    skip: u8,
    lengths: [u8; 18],
}

impl ComplexCodeLengthAlphabet {
    spec fn valid(&self) -> bool {
        &&& (self.skip == 0 || self.skip == 2 || self.skip == 3)
        &&& forall|i: int| 0 <= i < 18 ==> self.lengths@[i] <= 5
    }

    proof fn length_bound(&self, index: int)
        requires self.valid(), 0 <= index < 18,
        ensures self.lengths@[index] <= 5,
    {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ComplexProgress {
    skip: u8,
    index: u8,
    lengths: [u8; 18],
    space: u8,
    nonzero: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ComplexSymbolProgress {
    code: ComplexCodeLengthAlphabet,
    symbol: u16,
    prev_code_len: u8,
    repeat: u32,
    repeat_code_len: u8,
    space: u32,
    prefix_width: u8,
    prefix_bits: u8,
    singleton: u8,
}

impl ComplexSymbolProgress {
    spec fn valid(&self, alphabet_limit: u16) -> bool {
        &&& self.code.valid()
        &&& 1 <= alphabet_limit <= 704
        &&& self.symbol < alphabet_limit
        &&& 1 <= self.prev_code_len <= 15
        &&& self.repeat <= self.symbol
        &&& (self.repeat == 0 || self.repeat >= 3)
        &&& self.repeat_code_len <= 15
        &&& 1 <= self.space <= 32_768
        &&& self.prefix_width < 5
        &&& self.prefix_bits < (1u8 << self.prefix_width)
        &&& self.singleton <= 18
        &&& (self.singleton < 18 ==> {
            &&& self.code.lengths@[self.singleton as int] != 0
            &&& forall|i: int| 0 <= i < 18 && i != self.singleton
                ==> self.code.lengths@[i] == 0
            &&& self.prefix_width == 0
            &&& self.prefix_bits == 0
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComplexAfterSpan {
    Symbol(ComplexSymbolProgress),
    TrailingZeros {
        code: ComplexCodeLengthAlphabet,
        start: u16,
    },
    Complete {
        code: ComplexCodeLengthAlphabet,
        symbols: u16,
    },
}

impl ComplexAfterSpan {
    spec fn valid(&self, alphabet_limit: u16) -> bool {
        match self {
            ComplexAfterSpan::Symbol(progress) => progress.valid(alphabet_limit),
            ComplexAfterSpan::TrailingZeros { code, start } => {
                &&& code.valid()
                &&& start < alphabet_limit
            },
            ComplexAfterSpan::Complete { code, symbols } => {
                &&& code.valid()
                &&& symbols == alphabet_limit
            },
        }
    }
}

impl ComplexProgress {
    spec fn valid(&self) -> bool {
        &&& (self.skip == 0 || self.skip == 2 || self.skip == 3)
        &&& self.skip <= self.index < 18
        &&& self.space <= 32
        &&& self.nonzero <= self.index - self.skip
        &&& forall|i: int| 0 <= i < 18 ==> self.lengths@[i] <= 5
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CodeDescriptionPhase {
    Selector,
    SimpleSize,
    SimpleSymbols {
        selector: u8,
        count: u8,
        index: u8,
        width: u8,
        symbols: [u16; 4],
    },
    SimpleShape { symbols: [u16; 4] },
    ComplexPrefix2(ComplexProgress),
    ComplexPrefix3(ComplexProgress),
    ComplexPrefix4(ComplexProgress),
    ComplexSymbol(ComplexSymbolProgress),
    ComplexRepeat {
        progress: ComplexSymbolProgress,
        length: u8,
        extra_bits: u8,
    },
    ComplexPendingSpan {
        start: u16,
        span_count: u16,
        length: u8,
        after: ComplexAfterSpan,
    },
    CompleteSimple(SimpleCodeDescription),
    CompleteComplexAlphabet(ComplexCodeLengthAlphabet),
    CompleteComplex {
        code: ComplexCodeLengthAlphabet,
        decoded_symbols: u16,
    },
    Failed(CodeDescriptionError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CodeDescriptionStatus {
    Progress,
    NeedInput,
    Simple(SimpleCodeDescription),
    ComplexAlphabet(ComplexCodeLengthAlphabet),
    ComplexComplete { symbols: u16 },
    Failed(CodeDescriptionError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CodeDescriptionStep {
    consumed: usize,
    status: CodeDescriptionStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CodeDescriptionDecoder {
    queue: BitQueue,
    alphabet_max: u16,
    alphabet_limit: u16,
    phase: CodeDescriptionPhase,
}

spec fn alphabet_bit_width_spec(alphabet_max: u16) -> nat {
    if alphabet_max <= 1 { 0 }
    else if alphabet_max <= 2 { 1 }
    else if alphabet_max <= 4 { 2 }
    else if alphabet_max <= 8 { 3 }
    else if alphabet_max <= 16 { 4 }
    else if alphabet_max <= 32 { 5 }
    else if alphabet_max <= 64 { 6 }
    else if alphabet_max <= 128 { 7 }
    else if alphabet_max <= 256 { 8 }
    else if alphabet_max <= 512 { 9 }
    else { 10 }
}

spec fn code_phase_width(phase: CodeDescriptionPhase, alphabet_max: u16) -> nat {
    match phase {
        CodeDescriptionPhase::Selector | CodeDescriptionPhase::SimpleSize
        | CodeDescriptionPhase::ComplexPrefix2(_) => 2,
        CodeDescriptionPhase::SimpleSymbols { .. } => alphabet_bit_width_spec(alphabet_max),
        CodeDescriptionPhase::SimpleShape { .. }
        | CodeDescriptionPhase::ComplexPrefix3(_)
        | CodeDescriptionPhase::ComplexPrefix4(_) => 1,
        CodeDescriptionPhase::ComplexSymbol(progress) =>
            if progress.singleton < 18 { 0 } else { 1 },
        CodeDescriptionPhase::ComplexRepeat { extra_bits, .. } => extra_bits as nat,
        _ => 0,
    }
}

spec fn code_phase_terminal(phase: CodeDescriptionPhase) -> bool {
    match phase {
        CodeDescriptionPhase::CompleteSimple(_)
        | CodeDescriptionPhase::CompleteComplex { .. }
        | CodeDescriptionPhase::Failed(_) => true,
        _ => false,
    }
}

spec fn simple_prefix_contains(symbols: Seq<u16>, count: nat, symbol: u16) -> bool {
    exists|i: int| 0 <= i < count && symbols[i] == symbol
}

spec fn code_length_space_weight(value: u8) -> nat {
    if value == 1 { 16 }
    else if value == 2 { 8 }
    else if value == 3 { 4 }
    else if value == 4 { 2 }
    else if value == 5 { 1 }
    else { 0 }
}

fn code_length_space_weight_exec(value: u8) -> (r: u8)
    requires value <= 5,
    ensures r as nat == code_length_space_weight(value),
{
    if value == 1 { 16 }
    else if value == 2 { 8 }
    else if value == 3 { 4 }
    else if value == 4 { 2 }
    else if value == 5 { 1 }
    else { 0 }
}

spec fn symbol_code_length_weight(value: u8) -> nat {
    if value == 1 { 16_384 }
    else if value == 2 { 8_192 }
    else if value == 3 { 4_096 }
    else if value == 4 { 2_048 }
    else if value == 5 { 1_024 }
    else if value == 6 { 512 }
    else if value == 7 { 256 }
    else if value == 8 { 128 }
    else if value == 9 { 64 }
    else if value == 10 { 32 }
    else if value == 11 { 16 }
    else if value == 12 { 8 }
    else if value == 13 { 4 }
    else if value == 14 { 2 }
    else if value == 15 { 1 }
    else { 0 }
}

fn symbol_code_length_weight_exec(value: u8) -> (r: u32)
    requires 1 <= value <= 15,
    ensures r as nat == symbol_code_length_weight(value), 1 <= r <= 16_384,
{
    if value == 1 { 16_384 }
    else if value == 2 { 8_192 }
    else if value == 3 { 4_096 }
    else if value == 4 { 2_048 }
    else if value == 5 { 1_024 }
    else if value == 6 { 512 }
    else if value == 7 { 256 }
    else if value == 8 { 128 }
    else if value == 9 { 64 }
    else if value == 10 { 32 }
    else if value == 11 { 16 }
    else if value == 12 { 8 }
    else if value == 13 { 4 }
    else if value == 14 { 2 }
    else { 1 }
}

spec fn auxiliary_count_prefix(lengths: Seq<u8>, length: u8, limit: nat) -> nat
    decreases limit,
{
    if limit == 0 { 0 }
    else {
        auxiliary_count_prefix(lengths, length, (limit - 1) as nat)
            + if lengths[(limit - 1) as int] == length { 1nat } else { 0nat }
    }
}

spec fn auxiliary_first_code(lengths: Seq<u8>, length: nat) -> nat
    decreases length,
{
    if length <= 1 { 0 }
    else {
        2 * (auxiliary_first_code(lengths, (length - 1) as nat)
            + auxiliary_count_prefix(lengths, (length - 1) as u8, lengths.len()))
    }
}

spec fn auxiliary_canonical_code(lengths: Seq<u8>, symbol: int) -> nat {
    auxiliary_first_code(lengths, lengths[symbol] as nat)
        + auxiliary_count_prefix(lengths, lengths[symbol], symbol as nat)
}

spec fn auxiliary_reversed_code(value: nat, width: u8) -> nat {
    if width == 1 {
        value % 2
    } else if width == 2 {
        (value % 2) * 2 + (value / 2) % 2
    } else if width == 3 {
        (value % 2) * 4 + ((value / 2) % 2) * 2 + (value / 4) % 2
    } else if width == 4 {
        (value % 2) * 8 + ((value / 2) % 2) * 4
            + ((value / 4) % 2) * 2 + (value / 8) % 2
    } else {
        (value % 2) * 16 + ((value / 2) % 2) * 8
            + ((value / 4) % 2) * 4 + ((value / 8) % 2) * 2
            + (value / 16) % 2
    }
}

fn reverse_auxiliary_code(value: u32, width: u8) -> (r: u8)
    requires 1 <= width <= 5, (value as nat) < pow2(width as nat),
    ensures r as nat == auxiliary_reversed_code(value as nat, width), r <= 31,
{
    if width == 1 {
        (value % 2) as u8
    } else if width == 2 {
        ((value % 2) * 2 + (value / 2) % 2) as u8
    } else if width == 3 {
        ((value % 2) * 4 + ((value / 2) % 2) * 2 + (value / 4) % 2) as u8
    } else if width == 4 {
        ((value % 2) * 8 + ((value / 2) % 2) * 4
            + ((value / 4) % 2) * 2 + (value / 8) % 2) as u8
    } else {
        ((value % 2) * 16 + ((value / 2) % 2) * 8
            + ((value / 4) % 2) * 4 + ((value / 8) % 2) * 2
            + (value / 16) % 2) as u8
    }
}

proof fn pow2_matches_auxiliary_shift(width: u8)
    requires 1 <= width <= 5,
    ensures pow2(width as nat) == (1u32 << width) as nat,
{
    lemma2_to64();
    if width == 1 {
        assert((1u32 << 1) == 2) by (bit_vector);
    } else if width == 2 {
        assert((1u32 << 2) == 4) by (bit_vector);
    } else if width == 3 {
        assert((1u32 << 3) == 8) by (bit_vector);
    } else if width == 4 {
        assert((1u32 << 4) == 16) by (bit_vector);
    } else {
        assert(width == 5);
        assert((1u32 << 5) == 32) by (bit_vector);
    }
}

fn auxiliary_count_exec(
    lengths: &[u8; 18],
    length: u8,
    limit: usize,
) -> (r: u32)
    requires limit <= 18,
    ensures r as nat == auxiliary_count_prefix(lengths@, length, limit as nat), r <= limit,
{
    let mut i: usize = 0;
    let mut count: u32 = 0;
    while i < limit
        invariant i <= limit <= 18, count <= i,
            count as nat == auxiliary_count_prefix(lengths@, length, i as nat),
        decreases limit - i,
    {
        reveal(auxiliary_count_prefix);
        if lengths[i] == length {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn auxiliary_first_code_exec(lengths: &[u8; 18], length: u8) -> (r: u32)
    requires 1 <= length <= 5,
    ensures r as nat == auxiliary_first_code(lengths@, length as nat), r <= 1116,
{
    let mut width: u8 = 1;
    let mut code: u32 = 0;
    while width < length
        invariant 1 <= width <= length <= 5,
            code as nat == auxiliary_first_code(lengths@, width as nat),
            (width == 1 ==> code == 0),
            (width == 2 ==> code <= 36),
            (width == 3 ==> code <= 108),
            (width == 4 ==> code <= 252),
            (width == 5 ==> code <= 540),
        decreases length - width,
    {
        let count = auxiliary_count_exec(lengths, width, 18);
        assert(code + count <= 558);
        assert((code + count) * 2 <= 1116);
        code = (code + count) * 2;
        reveal(auxiliary_first_code);
        width = width + 1;
    }
    code
}

fn auxiliary_canonical_code_exec(
    lengths: &[u8; 18],
    symbol: usize,
) -> (r: u32)
    requires symbol < 18, 1 <= lengths@[symbol as int] <= 5,
    ensures r as nat == auxiliary_canonical_code(lengths@, symbol as int), r <= 1134,
{
    let length = lengths[symbol];
    let first = auxiliary_first_code_exec(lengths, length);
    let rank = auxiliary_count_exec(lengths, length, symbol);
    first + rank
}

fn decode_auxiliary_symbol(
    code: &ComplexCodeLengthAlphabet,
    bits: u8,
    width: u8,
) -> (r: Option<u8>)
    requires code.valid(), 1 <= width <= 5, bits < (1u8 << width),
    ensures
        r.is_some() ==> {
            &&& r.unwrap() < 18
            &&& auxiliary_symbol_match(*code, bits, width, r.unwrap())
        },
        r.is_none() ==> forall|symbol: u8| !auxiliary_symbol_match(
            *code, bits, width, symbol),
{
    let mut i: usize = 0;
    while i < 18
        invariant i <= 18, code.valid(), 1 <= width <= 5,
            forall|symbol: u8| symbol < i
                ==> !auxiliary_symbol_match(*code, bits, width, symbol),
        decreases 18 - i,
    {
        if code.lengths[i] == width {
            assert(0 <= (i as int) < 18);
            assert(code.lengths@[i as int] == width);
            proof { code.length_bound(i as int); }
            assert(1 <= code.lengths@[i as int] <= 5);
            let candidate = auxiliary_canonical_code_exec(&code.lengths, i);
            proof { pow2_matches_auxiliary_shift(width); }
            if candidate < (1u32 << width) {
                let reversed = reverse_auxiliary_code(candidate, width);
                if reversed == bits {
                    return Some(i as u8);
                }
            }
        }
        i = i + 1;
    }
    None
}

fn auxiliary_singleton(code: &ComplexCodeLengthAlphabet) -> (r: Option<u8>)
    requires code.valid(),
    ensures
        r.is_some() ==> {
            &&& r.unwrap() < 18
            &&& code.lengths@[r.unwrap() as int] != 0
            &&& forall|i: int| 0 <= i < 18 && i != r.unwrap()
                ==> code.lengths@[i] == 0
        },
{
    let mut found: u8 = 18;
    let mut multiple = false;
    let mut i: usize = 0;
    while i < 18
        invariant i <= 18, found <= 18,
            found < 18 ==> {
                &&& code.lengths@[found as int] != 0
                &&& found < i
            },
            !multiple ==> forall|j: int| 0 <= j < i && code.lengths@[j] != 0
                ==> found == j,
        decreases 18 - i,
    {
        if code.lengths[i] != 0 {
            if found == 18 {
                found = i as u8;
            } else {
                multiple = true;
            }
        }
        i = i + 1;
    }
    if found < 18 && !multiple { Some(found) } else { None }
}

fn start_complex_symbol_progress(
    code: ComplexCodeLengthAlphabet,
    _alphabet_limit: u16,
) -> (r: ComplexSymbolProgress)
    requires code.valid(), 1 <= _alphabet_limit <= 704,
    ensures
        r.valid(_alphabet_limit),
        r.code == code,
        r.symbol == 0,
        r.prev_code_len == 8,
        r.repeat == 0,
        r.repeat_code_len == 0,
        r.space == 32_768,
        r.prefix_width == 0,
        r.prefix_bits == 0,
        r.singleton <= 18,
{
    let singleton = auxiliary_singleton(&code);
    let singleton_value = match singleton {
        Some(symbol) => symbol,
        None => 18,
    };
    let progress = ComplexSymbolProgress {
        code,
        symbol: 0,
        prev_code_len: 8,
        repeat: 0,
        repeat_code_len: 0,
        space: 32_768,
        prefix_width: 0,
        prefix_bits: 0,
        singleton: singleton_value,
    };
    proof {
        assert(0u8 < (1u8 << 0)) by (bit_vector);
    }
    assert(progress.valid(_alphabet_limit));
    progress
}

#[verifier::bit_vector]
proof fn append_auxiliary_bit_bound(bits: u8, width: u8, bit: u8)
    requires width < 5, bits < (1u8 << width), bit < 2,
    ensures (bits | (bit << width)) < (1u8 << (width + 1)),
        (bits | (bit << width)) <= 31,
{}

#[verifier::bit_vector]
proof fn repeated_shift_bound(repeat: u32, extra_bits: u8)
    requires 3 <= repeat <= 704, 2 <= extra_bits <= 3,
    ensures (((repeat - 2) as u32) << extra_bits) <= 5_616,
        (((repeat - 2) as u32) << extra_bits)
            == if extra_bits == 2 { (repeat - 2) * 4 } else { (repeat - 2) * 8 },
{}

proof fn pow2_matches_small_shift(width: u8)
    requires 2 <= width <= 3,
    ensures pow2(width as nat) == (1u8 << width) as nat,
{
    lemma2_to64();
    if width == 2 {
        assert((1u8 << 2) == 4) by (bit_vector);
    } else {
        assert(width == 3);
        assert((1u8 << 3) == 8) by (bit_vector);
    }
}

#[verifier::bit_vector]
proof fn repeated_amount_fits(weight: u32, delta: u32)
    requires weight <= 16_384, delta <= 5_626,
    ensures weight * delta <= 92_176_384,
        (weight * delta) as nat == (weight as nat) * (delta as nat),
{}

spec fn complex_process_holds(
    old: ComplexProgress,
    value: u8,
    phase: CodeDescriptionPhase,
    status: CodeDescriptionStatus,
) -> bool {
    let slot = CODE_LENGTH_ORDER@[old.index as int] as int;
    let lengths = old.lengths@.update(slot, value);
    let amount = code_length_space_weight(value);
    if amount > old.space {
        &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
        &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
    } else {
        let next_space = old.space as nat - amount;
        let next_nonzero = old.nonzero as nat + if value == 0 { 0nat } else { 1nat };
        let next_index = old.index as nat + 1;
        if next_space == 0 {
            match phase {
                CodeDescriptionPhase::CompleteComplexAlphabet(code) => {
                    &&& code.skip == old.skip
                    &&& code.lengths@ == lengths
                    &&& status == CodeDescriptionStatus::ComplexAlphabet(code)
                },
                _ => false,
            }
        } else if next_index == 18 {
            if next_nonzero == 1 {
                match phase {
                    CodeDescriptionPhase::CompleteComplexAlphabet(code) => {
                        &&& code.skip == old.skip
                        &&& code.lengths@ == lengths
                        &&& status == CodeDescriptionStatus::ComplexAlphabet(code)
                    },
                    _ => false,
                }
            } else {
                &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
                &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
            }
        } else {
            match phase {
                CodeDescriptionPhase::ComplexPrefix2(next) => {
                    &&& next.skip == old.skip
                    &&& next.index as nat == next_index
                    &&& next.lengths@ == lengths
                    &&& next.space as nat == next_space
                    &&& next.nonzero as nat == next_nonzero
                    &&& status == CodeDescriptionStatus::Progress
                },
                _ => false,
            }
        }
    }
}

spec fn complex_after_span_holds(
    old: ComplexSymbolProgress,
    next_symbol: u16,
    next_space: u32,
    next_prev: u8,
    next_repeat: u32,
    next_repeat_code_len: u8,
    alphabet_limit: u16,
    after: ComplexAfterSpan,
) -> bool {
    if next_space == 0 {
        if next_symbol < alphabet_limit {
            match after {
                ComplexAfterSpan::TrailingZeros { code, start } => {
                    &&& code == old.code
                    &&& start == next_symbol
                },
                _ => false,
            }
        } else {
            match after {
                ComplexAfterSpan::Complete { code, symbols } => {
                    &&& code == old.code
                    &&& symbols == alphabet_limit
                },
                _ => false,
            }
        }
    } else {
        match after {
            ComplexAfterSpan::Symbol(next) => {
                &&& next.code == old.code
                &&& next.symbol == next_symbol
                &&& next.prev_code_len == next_prev
                &&& next.repeat == next_repeat
                &&& next.repeat_code_len == next_repeat_code_len
                &&& next.space == next_space
                &&& next.prefix_width == 0
                &&& next.prefix_bits == 0
                &&& next.singleton == old.singleton
            },
            _ => false,
        }
    }
}

spec fn direct_symbol_transition_holds(
    old: ComplexSymbolProgress,
    length: u8,
    alphabet_limit: u16,
    phase: CodeDescriptionPhase,
    status: CodeDescriptionStatus,
) -> bool {
    let amount = symbol_code_length_weight(length);
    if amount > old.space {
        &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
        &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
    } else {
        let next_symbol = old.symbol as nat + 1;
        let next_space = old.space as nat - amount;
        if next_symbol == alphabet_limit && next_space != 0 {
            &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
            &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
        } else {
            match phase {
                CodeDescriptionPhase::ComplexPendingSpan {
                    start, span_count: count, length: emitted, after,
                } => {
                    &&& start == old.symbol
                    &&& count == 1
                    &&& emitted == length
                    &&& status == CodeDescriptionStatus::Progress
                    &&& complex_after_span_holds(
                        old,
                        next_symbol as u16,
                        next_space as u32,
                        if length == 0 { old.prev_code_len } else { length },
                        0,
                        old.repeat_code_len,
                        alphabet_limit,
                        after,
                    )
                },
                _ => false,
            }
        }
    }
}

spec fn repeated_symbol_transition_holds(
    old: ComplexSymbolProgress,
    length: u8,
    extra_bits: u8,
    suffix: u8,
    alphabet_limit: u16,
    phase: CodeDescriptionPhase,
    status: CodeDescriptionStatus,
) -> bool {
    let reset_repeat: nat = if old.repeat_code_len == length { old.repeat as nat } else { 0nat };
    let base: nat = if reset_repeat > 0 {
        ((reset_repeat - 2) as nat) * if extra_bits == 2 { 4nat } else { 8nat }
    } else { 0nat };
    let next_repeat = base + suffix as nat + 3;
    let delta = next_repeat - reset_repeat;
    let amount = delta * symbol_code_length_weight(length);
    if old.symbol as nat + delta > alphabet_limit || amount > old.space {
        &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
        &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
    } else {
        let next_symbol = old.symbol as nat + delta;
        let next_space = old.space as nat - amount;
        if next_symbol == alphabet_limit && next_space != 0 {
            &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
            &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
        } else {
            match phase {
                CodeDescriptionPhase::ComplexPendingSpan {
                    start, span_count: count, length: emitted, after,
                } => {
                    &&& start == old.symbol
                    &&& count as nat == delta
                    &&& emitted == length
                    &&& status == CodeDescriptionStatus::Progress
                    &&& complex_after_span_holds(
                        old,
                        next_symbol as u16,
                        next_space as u32,
                        old.prev_code_len,
                        next_repeat as u32,
                        length,
                        alphabet_limit,
                        after,
                    )
                },
                _ => false,
            }
        }
    }
}

spec fn auxiliary_symbol_match(
    code: ComplexCodeLengthAlphabet,
    bits: u8,
    width: u8,
    symbol: u8,
) -> bool {
    &&& symbol < 18
    &&& code.lengths@[symbol as int] == width
    &&& auxiliary_canonical_code(code.lengths@, symbol as int) < pow2(width as nat)
    &&& auxiliary_reversed_code(
        auxiliary_canonical_code(code.lengths@, symbol as int),
        width,
    ) == bits
}

spec fn complex_symbol_transition_holds(
    old: ComplexSymbolProgress,
    field: nat,
    alphabet_limit: u16,
    phase: CodeDescriptionPhase,
    status: CodeDescriptionStatus,
) -> bool {
    if old.singleton < 18 {
        if old.singleton < 16 {
            direct_symbol_transition_holds(old, old.singleton, alphabet_limit, phase, status)
        } else {
            &&& phase == CodeDescriptionPhase::ComplexRepeat {
                progress: old,
                length: if old.singleton == 16 { old.prev_code_len } else { 0 },
                extra_bits: if old.singleton == 16 { 2 } else { 3 },
            }
            &&& status == CodeDescriptionStatus::Progress
        }
    } else {
        let next_bits = old.prefix_bits | ((field as u8) << old.prefix_width);
        let next_width = (old.prefix_width + 1) as u8;
        if exists|symbol: u8| auxiliary_symbol_match(old.code, next_bits, next_width, symbol) {
            exists|symbol: u8| {
                &&& auxiliary_symbol_match(old.code, next_bits, next_width, symbol)
                &&& if symbol < 16 {
                    direct_symbol_transition_holds(old, symbol, alphabet_limit, phase, status)
                } else {
                    &&& phase == CodeDescriptionPhase::ComplexRepeat {
                        progress: ComplexSymbolProgress {
                            prefix_width: 0,
                            prefix_bits: 0,
                            ..old
                        },
                        length: if symbol == 16 { old.prev_code_len } else { 0 },
                        extra_bits: if symbol == 16 { 2 } else { 3 },
                    }
                    &&& status == CodeDescriptionStatus::Progress
                }
            }
        } else if next_width == 5 {
            &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace)
            &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
        } else {
            &&& phase == CodeDescriptionPhase::ComplexSymbol(ComplexSymbolProgress {
                prefix_width: next_width,
                prefix_bits: next_bits,
                ..old
            })
            &&& status == CodeDescriptionStatus::Progress
        }
    }
}

spec fn pending_span_transition_holds(
    after: ComplexAfterSpan,
    alphabet_limit: u16,
    phase: CodeDescriptionPhase,
    status: CodeDescriptionStatus,
) -> bool {
    match after {
        ComplexAfterSpan::Symbol(progress) => {
            &&& phase == CodeDescriptionPhase::ComplexSymbol(progress)
            &&& status == CodeDescriptionStatus::Progress
        },
        ComplexAfterSpan::TrailingZeros { code, start } => {
            let count = (alphabet_limit - start) as u16;
            &&& phase == CodeDescriptionPhase::ComplexPendingSpan {
                start,
                span_count: count,
                length: 0,
                after: ComplexAfterSpan::Complete {
                    code,
                    symbols: alphabet_limit,
                },
            }
            &&& status == CodeDescriptionStatus::Progress
        },
        ComplexAfterSpan::Complete { code, symbols } => {
            &&& phase == CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbols }
            &&& status == CodeDescriptionStatus::ComplexComplete { symbols }
        },
    }
}

spec fn code_transition_holds(
    old: CodeDescriptionPhase,
    field: nat,
    alphabet_max: u16,
    alphabet_limit: u16,
    phase: CodeDescriptionPhase,
    status: CodeDescriptionStatus,
) -> bool {
    match old {
        CodeDescriptionPhase::Selector => {
            if field == 1 {
                &&& phase == CodeDescriptionPhase::SimpleSize
                &&& status == CodeDescriptionStatus::Progress
            } else {
                let skip = field as u8;
                &&& (skip == 0 || skip == 2 || skip == 3)
                &&& match phase {
                    CodeDescriptionPhase::ComplexPrefix2(next) => {
                        &&& next.skip == skip
                        &&& next.index == skip
                        &&& next.space == 32
                        &&& next.nonzero == 0
                        &&& forall|i: int| 0 <= i < 18 ==> next.lengths@[i] == 0
                        &&& status == CodeDescriptionStatus::Progress
                    },
                    _ => false,
                }
            }
        },
        CodeDescriptionPhase::SimpleSize => {
            let selector = field as u8;
            match phase {
                CodeDescriptionPhase::SimpleSymbols {
                    selector: next_selector,
                    count,
                    index,
                    width,
                    symbols,
                } => {
                    &&& next_selector == selector
                    &&& count as nat == field + 1
                    &&& index == 0
                    &&& width as nat == alphabet_bit_width_spec(alphabet_max)
                    &&& forall|i: int| 0 <= i < 4 ==> symbols@[i] == 0
                    &&& status == CodeDescriptionStatus::Progress
                },
                _ => false,
            }
        },
        CodeDescriptionPhase::SimpleSymbols {
            selector, count, index, width, symbols,
        } => {
            if field >= alphabet_limit {
                &&& phase == CodeDescriptionPhase::Failed(CodeDescriptionError::InvalidAlphabet)
                &&& status == CodeDescriptionStatus::Failed(CodeDescriptionError::InvalidAlphabet)
            } else {
                let symbol = field as u16;
                if simple_prefix_contains(symbols@, index as nat, symbol) {
                    &&& phase == CodeDescriptionPhase::Failed(
                        CodeDescriptionError::DuplicateSimpleSymbol,
                    )
                    &&& status == CodeDescriptionStatus::Failed(
                        CodeDescriptionError::DuplicateSimpleSymbol,
                    )
                } else {
                    let updated = symbols@.update(index as int, symbol);
                    if index + 1 < count {
                        match phase {
                            CodeDescriptionPhase::SimpleSymbols {
                                selector: next_selector,
                                count: next_count,
                                index: next_index,
                                width: next_width,
                                symbols: next_symbols,
                            } => {
                                &&& next_selector == selector
                                &&& next_count == count
                                &&& next_index == index + 1
                                &&& next_width == width
                                &&& next_symbols@ == updated
                                &&& status == CodeDescriptionStatus::Progress
                            },
                            _ => false,
                        }
                    } else if selector == 3 {
                        match phase {
                            CodeDescriptionPhase::SimpleShape { symbols: next_symbols } => {
                                &&& next_symbols@ == updated
                                &&& status == CodeDescriptionStatus::Progress
                            },
                            _ => false,
                        }
                    } else {
                        match phase {
                            CodeDescriptionPhase::CompleteSimple(code) => {
                                &&& code.selector == selector
                                &&& code.count == count
                                &&& code.symbols@ == updated
                                &&& status == CodeDescriptionStatus::Simple(code)
                            },
                            _ => false,
                        }
                    }
                }
            }
        },
        CodeDescriptionPhase::SimpleShape { symbols } => {
            match phase {
                CodeDescriptionPhase::CompleteSimple(code) => {
                    &&& code.selector as nat == 3 + field
                    &&& code.count == 4
                    &&& code.symbols == symbols
                    &&& status == CodeDescriptionStatus::Simple(code)
                },
                _ => false,
            }
        },
        CodeDescriptionPhase::ComplexPrefix2(progress) => {
            if field == 0 {
                complex_process_holds(progress, 0, phase, status)
            } else if field == 1 {
                complex_process_holds(progress, 4, phase, status)
            } else if field == 2 {
                complex_process_holds(progress, 3, phase, status)
            } else {
                &&& phase == CodeDescriptionPhase::ComplexPrefix3(progress)
                &&& status == CodeDescriptionStatus::Progress
            }
        },
        CodeDescriptionPhase::ComplexPrefix3(progress) => {
            if field == 0 {
                complex_process_holds(progress, 2, phase, status)
            } else {
                &&& phase == CodeDescriptionPhase::ComplexPrefix4(progress)
                &&& status == CodeDescriptionStatus::Progress
            }
        },
        CodeDescriptionPhase::ComplexPrefix4(progress) => {
            if field == 0 {
                complex_process_holds(progress, 1, phase, status)
            } else {
                complex_process_holds(progress, 5, phase, status)
            }
        },
        CodeDescriptionPhase::CompleteComplexAlphabet(code) => match phase {
            CodeDescriptionPhase::ComplexSymbol(next) => {
                &&& next.code == code
                &&& next.symbol == 0
                &&& next.prev_code_len == 8
                &&& next.repeat == 0
                &&& next.repeat_code_len == 0
                &&& next.space == 32_768
                &&& next.prefix_width == 0
                &&& next.prefix_bits == 0
                &&& status == CodeDescriptionStatus::Progress
            },
            _ => false,
        },
        CodeDescriptionPhase::ComplexSymbol(progress) =>
            complex_symbol_transition_holds(progress, field, alphabet_limit, phase, status),
        CodeDescriptionPhase::ComplexRepeat {
            progress,
            length,
            extra_bits,
        } => repeated_symbol_transition_holds(
            progress,
            length,
            extra_bits,
            field as u8,
            alphabet_limit,
            phase,
            status,
        ),
        CodeDescriptionPhase::ComplexPendingSpan { after, .. } =>
            pending_span_transition_holds(after, alphabet_limit, phase, status),
        _ => false,
    }
}

fn alphabet_bit_width(alphabet_max: u16) -> (r: u8)
    requires 1 <= alphabet_max <= 704,
    ensures r <= 10, r as nat == alphabet_bit_width_spec(alphabet_max),
{
    if alphabet_max <= 1 { 0 }
    else if alphabet_max <= 2 { 1 }
    else if alphabet_max <= 4 { 2 }
    else if alphabet_max <= 8 { 3 }
    else if alphabet_max <= 16 { 4 }
    else if alphabet_max <= 32 { 5 }
    else if alphabet_max <= 64 { 6 }
    else if alphabet_max <= 128 { 7 }
    else if alphabet_max <= 256 { 8 }
    else if alphabet_max <= 512 { 9 }
    else { 10 }
}

fn simple_symbols_distinct(symbols: &[u16; 4], count: u8) -> (r: bool)
    requires 1 <= count <= 4,
    ensures r == active_symbols_distinct(symbols@, count as nat),
{
    let mut i: usize = 0;
    while i < count as usize
        invariant i <= count <= 4,
            forall|a: int, b: int| 0 <= a < i && 0 <= b < count && a != b
                ==> symbols@[a] != symbols@[b],
        decreases count as usize - i,
    {
        let mut j = i + 1;
        while j < count as usize
            invariant i < count <= 4, i + 1 <= j <= count,
                forall|a: int, b: int| 0 <= a < i && 0 <= b < count && a != b
                    ==> symbols@[a] != symbols@[b],
                forall|b: int| i < b < j ==> symbols@[i as int] != symbols@[b],
            decreases count as usize - j,
        {
            if symbols[i] == symbols[j] {
                return false;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    true
}

fn process_complex_code_length(
    progress: ComplexProgress,
    value: u8,
) -> (r: CodeDescriptionPhase)
    requires progress.valid(), progress.index < 18, value <= 5,
    ensures
        match r {
            CodeDescriptionPhase::ComplexPrefix2(next) => next.valid(),
            CodeDescriptionPhase::CompleteComplexAlphabet(code) => code.valid(),
            CodeDescriptionPhase::Failed(_) => true,
            _ => false,
        },
        complex_process_holds(
            progress,
            value,
            r,
            match r {
                CodeDescriptionPhase::CompleteComplexAlphabet(code) =>
                    CodeDescriptionStatus::ComplexAlphabet(code),
                CodeDescriptionPhase::Failed(error) => CodeDescriptionStatus::Failed(error),
                _ => CodeDescriptionStatus::Progress,
            },
        ),
{
    let mut next = progress;
    let slot = CODE_LENGTH_ORDER[progress.index as usize] as usize;
    next.lengths[slot] = value;
    next.index = progress.index + 1;
    if value != 0 {
        let amount = code_length_space_weight_exec(value);
        if amount > progress.space {
            return CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
        }
        next.space = progress.space - amount;
        next.nonzero = progress.nonzero + 1;
    }
    if next.space == 0 {
        return CodeDescriptionPhase::CompleteComplexAlphabet(ComplexCodeLengthAlphabet {
            skip: next.skip,
            lengths: next.lengths,
        });
    }
    if next.index == 18 {
        if next.nonzero == 1 {
            return CodeDescriptionPhase::CompleteComplexAlphabet(ComplexCodeLengthAlphabet {
                skip: next.skip,
                lengths: next.lengths,
            });
        }
        return CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
    }
    CodeDescriptionPhase::ComplexPrefix2(next)
}

fn complex_after_symbol(
    progress: ComplexSymbolProgress,
    next_symbol: u16,
    next_space: u32,
    next_prev: u8,
    next_repeat: u32,
    next_repeat_code_len: u8,
    alphabet_limit: u16,
) -> (r: ComplexAfterSpan)
    requires progress.valid(alphabet_limit),
        progress.symbol < next_symbol <= alphabet_limit,
        next_space <= progress.space,
        next_space == 0 || next_symbol < alphabet_limit,
        1 <= next_prev <= 15,
        next_repeat <= next_symbol,
        next_repeat == 0 || next_repeat >= 3,
        next_repeat_code_len <= 15,
    ensures r.valid(alphabet_limit),
        complex_after_span_holds(
            progress,
            next_symbol,
            next_space,
            next_prev,
            next_repeat,
            next_repeat_code_len,
            alphabet_limit,
            r,
        ),
{
    if next_space == 0 {
        if next_symbol < alphabet_limit {
            ComplexAfterSpan::TrailingZeros {
                code: progress.code,
                start: next_symbol,
            }
        } else {
            ComplexAfterSpan::Complete {
                code: progress.code,
                symbols: alphabet_limit,
            }
        }
    } else {
        assert(1 <= next_space <= 32_768);
        let next = ComplexSymbolProgress {
            code: progress.code,
            symbol: next_symbol,
            prev_code_len: next_prev,
            repeat: next_repeat,
            repeat_code_len: next_repeat_code_len,
            space: next_space,
            prefix_width: 0,
            prefix_bits: 0,
            singleton: progress.singleton,
        };
        proof {
            assert(0u8 < (1u8 << 0)) by (bit_vector);
        }
        assert(next.valid(alphabet_limit));
        ComplexAfterSpan::Symbol(next)
    }
}

fn process_direct_symbol_length(
    progress: ComplexSymbolProgress,
    length: u8,
    alphabet_limit: u16,
) -> (r: CodeDescriptionPhase)
    requires progress.valid(alphabet_limit), length <= 15,
    ensures direct_symbol_transition_holds(
        progress,
        length,
        alphabet_limit,
        r,
        match r {
            CodeDescriptionPhase::Failed(error) => CodeDescriptionStatus::Failed(error),
            _ => CodeDescriptionStatus::Progress,
        },
    ),
        match r {
            CodeDescriptionPhase::ComplexPendingSpan { after, .. } =>
                after.valid(alphabet_limit),
            CodeDescriptionPhase::Failed(_) => true,
            _ => false,
        },
{
    let start = progress.symbol;
    let next_symbol = progress.symbol + 1;
    let mut next_space = progress.space;
    let mut next_prev = progress.prev_code_len;
    if length != 0 {
        let amount = symbol_code_length_weight_exec(length);
        if amount > progress.space {
            let result = CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
            assert(direct_symbol_transition_holds(
                progress,
                length,
                alphabet_limit,
                result,
                CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace),
            ));
            return result;
        }
        next_space = progress.space - amount;
        next_prev = length;
    }
    if next_symbol == alphabet_limit && next_space != 0 {
        let result = CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
        assert(direct_symbol_transition_holds(
            progress,
            length,
            alphabet_limit,
            result,
            CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace),
        ));
        return result;
    }
    let after = complex_after_symbol(
        progress,
        next_symbol,
        next_space,
        next_prev,
        0,
        progress.repeat_code_len,
        alphabet_limit,
    );
    let result = CodeDescriptionPhase::ComplexPendingSpan {
        start,
        span_count: 1,
        length,
        after,
    };
    assert(direct_symbol_transition_holds(
        progress,
        length,
        alphabet_limit,
        result,
        CodeDescriptionStatus::Progress,
    ));
    result
}

fn process_repeated_symbol_length(
    progress: ComplexSymbolProgress,
    length: u8,
    extra_bits: u8,
    suffix: u8,
    alphabet_limit: u16,
) -> (r: CodeDescriptionPhase)
    requires progress.valid(alphabet_limit),
        (length == 0 && extra_bits == 3) || (1 <= length <= 15 && extra_bits == 2),
        suffix < (1u8 << extra_bits),
    ensures repeated_symbol_transition_holds(
        progress,
        length,
        extra_bits,
        suffix,
        alphabet_limit,
        r,
        match r {
            CodeDescriptionPhase::Failed(error) => CodeDescriptionStatus::Failed(error),
            _ => CodeDescriptionStatus::Progress,
        },
    ),
        match r {
            CodeDescriptionPhase::ComplexPendingSpan { after, .. } =>
                after.valid(alphabet_limit),
            CodeDescriptionPhase::Failed(_) => true,
            _ => false,
        },
{
    let old_repeat = if progress.repeat_code_len != length {
        0
    } else {
        progress.repeat
    };
    assert(old_repeat as nat == if progress.repeat_code_len == length {
        progress.repeat as nat
    } else { 0nat });
    assert(old_repeat == 0 || 3 <= old_repeat <= 704);
    if extra_bits == 2 {
        assert((1u8 << 2) == 4) by (bit_vector);
        assert(suffix < 4);
    } else {
        assert(extra_bits == 3);
        assert((1u8 << 3) == 8) by (bit_vector);
        assert(suffix < 8);
    }
    let base = if old_repeat > 0 {
        assert(old_repeat >= 3);
        assert(old_repeat - 2 <= 702);
        proof { repeated_shift_bound(old_repeat, extra_bits); }
        (old_repeat - 2) << extra_bits
    } else {
        0
    };
    assert(base <= 5_616);
    assert(base as nat == if old_repeat > 0 {
        ((old_repeat - 2) as nat) * if extra_bits == 2 { 4nat } else { 8nat }
    } else { 0nat });
    let next_repeat = base + suffix as u32 + 3;
    assert(next_repeat as nat == base as nat + suffix as nat + 3);
    assert(next_repeat <= 5_626);
    assert(next_repeat > old_repeat);
    let delta = next_repeat - old_repeat;
    assert(delta as nat == next_repeat as nat - old_repeat as nat);
    if delta > alphabet_limit as u32 - progress.symbol as u32 {
        let result = CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
        assert(repeated_symbol_transition_holds(
            progress,
            length,
            extra_bits,
            suffix,
            alphabet_limit,
            result,
            CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace),
        ));
        return result;
    }
    let next_symbol = progress.symbol + delta as u16;
    let mut next_space = progress.space;
    if length != 0 {
        let weight = symbol_code_length_weight_exec(length);
        assert(weight <= 16_384);
        assert(delta <= 5_626);
        proof { repeated_amount_fits(weight, delta); }
        let amount = weight * delta;
        assert(amount as nat == (weight as nat) * (delta as nat));
        assert(weight as nat == symbol_code_length_weight(length));
        assert((weight as nat) * (delta as nat)
            == (delta as nat) * (weight as nat)) by (nonlinear_arith);
        assert((delta as nat) * (weight as nat)
            == (delta as nat) * symbol_code_length_weight(length));
        assert(amount as nat
            == (delta as nat) * symbol_code_length_weight(length));
        if amount > progress.space {
            let result = CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
            assert(repeated_symbol_transition_holds(
                progress,
                length,
                extra_bits,
                suffix,
                alphabet_limit,
                result,
                CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace),
            ));
            return result;
        }
        next_space = progress.space - amount;
    }
    if next_symbol == alphabet_limit && next_space != 0 {
        let result = CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);
        assert(repeated_symbol_transition_holds(
            progress,
            length,
            extra_bits,
            suffix,
            alphabet_limit,
            result,
            CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace),
        ));
        return result;
    }
    let after = complex_after_symbol(
        progress,
        next_symbol,
        next_space,
        progress.prev_code_len,
        next_repeat,
        length,
        alphabet_limit,
    );
    let result = CodeDescriptionPhase::ComplexPendingSpan {
        start: next_symbol - delta as u16,
        span_count: delta as u16,
        length,
        after,
    };
    assert(repeated_symbol_transition_holds(
        progress,
        length,
        extra_bits,
        suffix,
        alphabet_limit,
        result,
        CodeDescriptionStatus::Progress,
    ));
    result
}

impl CodeDescriptionDecoder {
    spec fn valid(&self) -> bool {
        &&& self.queue.valid()
        &&& 1 <= self.alphabet_limit <= self.alphabet_max <= 704
        &&& match self.phase {
            CodeDescriptionPhase::SimpleSymbols {
                selector, count, index, width, symbols, ..
            } => {
                &&& selector <= 3
                &&& count as nat == simple_count(selector)
                &&& 1 <= count <= 4
                &&& index < count
                &&& width <= 10
                &&& width as nat == alphabet_bit_width_spec(self.alphabet_max)
                &&& forall|i: int| 0 <= i < index ==> symbols@[i] < self.alphabet_limit
                &&& active_symbols_distinct(symbols@, index as nat)
            },
            CodeDescriptionPhase::SimpleShape { symbols } => {
                &&& forall|i: int| 0 <= i < 4 ==> symbols@[i] < self.alphabet_limit
                &&& active_symbols_distinct(symbols@, 4)
            },
            CodeDescriptionPhase::ComplexPrefix2(progress)
            | CodeDescriptionPhase::ComplexPrefix3(progress)
            | CodeDescriptionPhase::ComplexPrefix4(progress) => progress.valid(),
            CodeDescriptionPhase::ComplexSymbol(progress) =>
                progress.valid(self.alphabet_limit),
            CodeDescriptionPhase::ComplexRepeat { progress, length, extra_bits } => {
                &&& progress.valid(self.alphabet_limit)
                &&& (length == 0 || 1 <= length <= 15)
                &&& ((length == 0 && extra_bits == 3)
                    || (length != 0 && extra_bits == 2))
            },
            CodeDescriptionPhase::ComplexPendingSpan {
                start, span_count: count, length, after,
            } => {
                &&& count > 0
                &&& length <= 15
                &&& start as nat + count as nat <= self.alphabet_limit
                &&& after.valid(self.alphabet_limit)
            },
            CodeDescriptionPhase::CompleteSimple(code) => code.valid(self.alphabet_limit),
            CodeDescriptionPhase::CompleteComplexAlphabet(code) => code.valid(),
            CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbols } => {
                &&& code.valid()
                &&& symbols == self.alphabet_limit
            },
            _ => true,
        }
    }

    fn from_meta(
        meta: MetaBlockDecoder,
        alphabet_max: u16,
        alphabet_limit: u16,
    ) -> (r: Result<Self, CodeDescriptionError>)
        requires meta.valid(),
        ensures r.is_ok() ==> {
            &&& r.unwrap().valid()
            &&& r.unwrap().queue == meta.queue
            &&& r.unwrap().phase == CodeDescriptionPhase::Selector
        },
    {
        if alphabet_max == 0 || alphabet_max > 704
            || alphabet_limit == 0 || alphabet_limit > alphabet_max {
            return Err(CodeDescriptionError::InvalidAlphabet);
        }
        match meta.phase {
            MetaBlockPhase::Complete(header) => {
                if header.is_empty || header.is_uncompressed || header.is_metadata {
                    return Err(CodeDescriptionError::MetaBlockNotCompressed);
                }
                Ok(Self {
                    queue: meta.queue,
                    alphabet_max,
                    alphabet_limit,
                    phase: CodeDescriptionPhase::Selector,
                })
            }
            _ => Err(CodeDescriptionError::MetaBlockNotCompressed),
        }
    }

    #[verifier::rlimit(500)]
    fn advance_field(
        &mut self,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: CodeDescriptionStep)
        requires old(self).valid(),
        ensures final(self).valid(), r.consumed <= input.len(),
            match old(self).phase {
                CodeDescriptionPhase::CompleteSimple(code) => {
                    &&& r == (CodeDescriptionStep {
                        consumed: 0,
                        status: CodeDescriptionStatus::Simple(code),
                    })
                    &&& *final(self) == *old(self)
                },
                CodeDescriptionPhase::CompleteComplex { decoded_symbols: symbols, .. } => {
                    &&& r == (CodeDescriptionStep {
                        consumed: 0,
                        status: CodeDescriptionStatus::ComplexComplete { symbols },
                    })
                    &&& *final(self) == *old(self)
                },
                CodeDescriptionPhase::Failed(error) => {
                    &&& r == (CodeDescriptionStep {
                        consumed: 0,
                        status: CodeDescriptionStatus::Failed(error),
                    })
                    &&& *final(self) == *old(self)
                },
                _ => true,
            },
            r.status == CodeDescriptionStatus::NeedInput ==> {
                &&& !end_of_input
                &&& r.consumed == input.len()
            },
            match r.status {
                CodeDescriptionStatus::Simple(code) => {
                    &&& code.valid(final(self).alphabet_limit)
                    &&& final(self).phase == CodeDescriptionPhase::CompleteSimple(code)
                },
                CodeDescriptionStatus::ComplexAlphabet(code) => {
                    &&& code.valid()
                    &&& final(self).phase == CodeDescriptionPhase::CompleteComplexAlphabet(code)
                },
                CodeDescriptionStatus::ComplexComplete { symbols } => match final(self).phase {
                    CodeDescriptionPhase::CompleteComplex {
                        decoded_symbols: final_symbols,
                        ..
                    } => {
                        &&& final_symbols == symbols
                    },
                    _ => false,
                },
                CodeDescriptionStatus::Failed(error) =>
                    final(self).phase == CodeDescriptionPhase::Failed(error),
                _ => true,
            },
            !code_phase_terminal(old(self).phase) ==> {
                let width = code_phase_width(old(self).phase, old(self).alphabet_max);
                let available = old(self).queue.bits()
                    + bytes_bits(input@.take(r.consumed as int));
                &&& available.len() >= width ==> code_transition_holds(
                    old(self).phase,
                    bits_value(available.take(width as int)),
                    old(self).alphabet_max,
                    old(self).alphabet_limit,
                    final(self).phase,
                    r.status,
                )
            },
    {
        let phase = self.phase;
        match phase {
            CodeDescriptionPhase::CompleteSimple(code) => {
                return CodeDescriptionStep {
                    consumed: 0,
                    status: CodeDescriptionStatus::Simple(code),
                };
            }
            CodeDescriptionPhase::CompleteComplex { decoded_symbols: symbols, .. } => {
                return CodeDescriptionStep {
                    consumed: 0,
                    status: CodeDescriptionStatus::ComplexComplete { symbols },
                };
            }
            CodeDescriptionPhase::Failed(error) => {
                return CodeDescriptionStep {
                    consumed: 0,
                    status: CodeDescriptionStatus::Failed(error),
                };
            }
            _ => {}
        }

        if let CodeDescriptionPhase::ComplexPendingSpan { after, .. } = phase {
            self.phase = match after {
                ComplexAfterSpan::Symbol(progress) => CodeDescriptionPhase::ComplexSymbol(progress),
                ComplexAfterSpan::TrailingZeros { code, start } => {
                    let count = self.alphabet_limit - start;
                    CodeDescriptionPhase::ComplexPendingSpan {
                        start,
                        span_count: count,
                        length: 0,
                        after: ComplexAfterSpan::Complete {
                            code,
                            symbols: self.alphabet_limit,
                        },
                    }
                }
                ComplexAfterSpan::Complete { code, symbols } =>
                    CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbols },
            };
            assert(match self.phase {
                CodeDescriptionPhase::ComplexSymbol(progress) =>
                    progress.valid(self.alphabet_limit),
                CodeDescriptionPhase::ComplexPendingSpan {
                    start, span_count: count, length, after,
                } => {
                    &&& count > 0
                    &&& length <= 15
                    &&& start as nat + count as nat <= self.alphabet_limit
                    &&& after.valid(self.alphabet_limit)
                },
                CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbols } =>
                    code.valid() && symbols == self.alphabet_limit,
                _ => false,
            });
            let status = match self.phase {
                CodeDescriptionPhase::CompleteComplex { decoded_symbols: symbols, .. } =>
                    CodeDescriptionStatus::ComplexComplete { symbols },
                _ => CodeDescriptionStatus::Progress,
            };
            assert(self.valid());
            return CodeDescriptionStep { consumed: 0, status };
        }

        if let CodeDescriptionPhase::CompleteComplexAlphabet(code) = phase {
            let progress = start_complex_symbol_progress(code, self.alphabet_limit);
            self.phase = CodeDescriptionPhase::ComplexSymbol(progress);
            let status = CodeDescriptionStatus::Progress;
            assert(self.valid());
            return CodeDescriptionStep { consumed: 0, status };
        }

        let width: usize = match phase {
            CodeDescriptionPhase::Selector | CodeDescriptionPhase::SimpleSize
            | CodeDescriptionPhase::ComplexPrefix2(_) => 2,
            CodeDescriptionPhase::SimpleSymbols { width, .. } => width as usize,
            CodeDescriptionPhase::SimpleShape { .. }
            | CodeDescriptionPhase::ComplexPrefix3(_)
            | CodeDescriptionPhase::ComplexPrefix4(_) => 1,
            CodeDescriptionPhase::ComplexSymbol(progress) => {
                if progress.singleton < 18 { 0 } else { 1 }
            }
            CodeDescriptionPhase::ComplexRepeat { extra_bits, .. } => extra_bits as usize,
            CodeDescriptionPhase::CompleteSimple(_)
            | CodeDescriptionPhase::CompleteComplexAlphabet(_)
            | CodeDescriptionPhase::ComplexPendingSpan { .. }
            | CodeDescriptionPhase::CompleteComplex { .. }
            | CodeDescriptionPhase::Failed(_) => {
                proof { assert(false); }
                0
            }
        };
        proof {
            assert(width as nat == code_phase_width(phase, self.alphabet_max));
        }
        let ghost queue_before = self.queue.bits();
        let read = self.queue.read_bits(width, input, end_of_input);
        let field = match read.status {
            BitReadStatus::Value(value) => value,
            BitReadStatus::NeedInput => {
                proof {
                    assert(read.consumed == input.len());
                    assert(input@.take(read.consumed as int) =~= input@);
                    assert((queue_before + bytes_bits(input@)).len() < width);
                }
                return CodeDescriptionStep {
                    consumed: read.consumed,
                    status: CodeDescriptionStatus::NeedInput,
                };
            }
            BitReadStatus::Truncated => {
                proof {
                    assert(read.consumed == input.len());
                    assert(input@.take(read.consumed as int) =~= input@);
                    assert((queue_before + bytes_bits(input@)).len() < width);
                }
                self.phase = CodeDescriptionPhase::Failed(CodeDescriptionError::Truncated);
                return CodeDescriptionStep {
                    consumed: read.consumed,
                    status: CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated),
                };
            }
        };
        proof {
            lemma2_to64();
            assert((field as nat) < pow2(width as nat));
        }

        let mut status = CodeDescriptionStatus::Progress;
        match phase {
            CodeDescriptionPhase::Selector => {
                assert(width == 2);
                assert(field < 4);
                if field == 1 {
                    self.phase = CodeDescriptionPhase::SimpleSize;
                } else {
                    let skip = field as u8;
                    assert(skip == 0 || skip == 2 || skip == 3);
                    self.phase = CodeDescriptionPhase::ComplexPrefix2(ComplexProgress {
                        skip,
                        index: skip,
                        lengths: [0u8; 18],
                        space: 32,
                        nonzero: 0,
                    });
                }
            }
            CodeDescriptionPhase::SimpleSize => {
                assert(width == 2);
                assert(field < 4);
                let selector = field as u8;
                let count = selector + 1;
                let width = alphabet_bit_width(self.alphabet_max);
                self.phase = CodeDescriptionPhase::SimpleSymbols {
                    selector,
                    count,
                    index: 0,
                    width,
                    symbols: [0u16; 4],
                };
            }
            CodeDescriptionPhase::SimpleSymbols {
                selector, count, index, width: symbol_width, mut symbols,
            } => {
                if field >= self.alphabet_limit as u64 {
                    self.phase = CodeDescriptionPhase::Failed(CodeDescriptionError::InvalidAlphabet);
                    status = CodeDescriptionStatus::Failed(CodeDescriptionError::InvalidAlphabet);
                } else {
                    assert(field < 704);
                    let symbol = field as u16;
                    let mut duplicate = false;
                    let mut i: usize = 0;
                    while i < index as usize
                        invariant i <= index <= count <= 4,
                            !duplicate ==> forall|j: int| 0 <= j < i
                                ==> symbols@[j] != symbol,
                            duplicate ==> exists|j: int| 0 <= j < i && symbols@[j] == symbol,
                        decreases index as usize - i,
                    {
                        if symbols[i] == symbol {
                            duplicate = true;
                        }
                        i = i + 1;
                    }
                    if duplicate {
                        self.phase = CodeDescriptionPhase::Failed(
                            CodeDescriptionError::DuplicateSimpleSymbol,
                        );
                        status = CodeDescriptionStatus::Failed(
                            CodeDescriptionError::DuplicateSimpleSymbol,
                        );
                    } else {
                        symbols[index as usize] = symbol;
                        proof {
                            assert(active_symbols_distinct(
                                symbols@,
                                (index as nat) + 1,
                            )) by {
                                assert forall|a: int, b: int|
                                    0 <= a < index + 1 && 0 <= b < index + 1 && a != b
                                    implies symbols@[a] != symbols@[b] by {
                                    if a < index && b < index {
                                    } else if a == index {
                                        assert(b < index);
                                    } else {
                                        assert(b == index);
                                        assert(a < index);
                                    }
                                }
                            }
                        }
                        if index + 1 < count {
                            self.phase = CodeDescriptionPhase::SimpleSymbols {
                                selector,
                                count,
                                index: index + 1,
                                width: symbol_width,
                                symbols,
                            };
                        } else if selector == 3 {
                            assert(count == 4);
                            let _distinct = simple_symbols_distinct(&symbols, 4);
                            assert(_distinct);
                            self.phase = CodeDescriptionPhase::SimpleShape { symbols };
                        } else {
                            let _distinct = simple_symbols_distinct(&symbols, count);
                            assert(_distinct);
                            let code = SimpleCodeDescription {
                                selector,
                                count,
                                symbols,
                            };
                            self.phase = CodeDescriptionPhase::CompleteSimple(code);
                            status = CodeDescriptionStatus::Simple(code);
                        }
                    }
                }
            }
            CodeDescriptionPhase::SimpleShape { symbols } => {
                assert(width == 1);
                assert(field < 2);
                let selector = 3 + field as u8;
                let code = SimpleCodeDescription {
                    selector,
                    count: 4,
                    symbols,
                };
                self.phase = CodeDescriptionPhase::CompleteSimple(code);
                status = CodeDescriptionStatus::Simple(code);
            }
            CodeDescriptionPhase::ComplexPrefix2(progress) => {
                assert(width == 2);
                assert(field < 4);
                self.phase = if field == 0 {
                    process_complex_code_length(progress, 0)
                } else if field == 1 {
                    process_complex_code_length(progress, 4)
                } else if field == 2 {
                    process_complex_code_length(progress, 3)
                } else {
                    CodeDescriptionPhase::ComplexPrefix3(progress)
                };
            }
            CodeDescriptionPhase::ComplexPrefix3(progress) => {
                assert(width == 1);
                assert(field < 2);
                self.phase = if field == 0 {
                    process_complex_code_length(progress, 2)
                } else {
                    CodeDescriptionPhase::ComplexPrefix4(progress)
                };
            }
            CodeDescriptionPhase::ComplexPrefix4(progress) => {
                assert(width == 1);
                assert(field < 2);
                self.phase = if field == 0 {
                    process_complex_code_length(progress, 1)
                } else {
                    process_complex_code_length(progress, 5)
                };
            }
            CodeDescriptionPhase::ComplexSymbol(mut progress) => {
                let ghost started_progress = progress;
                if progress.singleton < 18 {
                    assert(width == 0);
                    assert(field == 0);
                    let symbol = progress.singleton;
                    if symbol < 16 {
                        self.phase = process_direct_symbol_length(
                            progress,
                            symbol,
                            self.alphabet_limit,
                        );
                    } else {
                        let (length, extra_bits) = if symbol == 16 {
                            (progress.prev_code_len, 2u8)
                        } else {
                            (0u8, 3u8)
                        };
                        assert(progress.valid(self.alphabet_limit));
                        self.phase = CodeDescriptionPhase::ComplexRepeat {
                            progress,
                            length,
                            extra_bits,
                        };
                    }
                } else {
                assert(width == 1);
                assert(field < 2);
                let bit = field as u8;
                proof {
                    append_auxiliary_bit_bound(
                        progress.prefix_bits,
                        progress.prefix_width,
                        bit,
                    );
                }
                let next_bits = progress.prefix_bits | (bit << progress.prefix_width);
                let next_width = progress.prefix_width + 1;
                match decode_auxiliary_symbol(&progress.code, next_bits, next_width) {
                    Some(symbol) => {
                        assert(auxiliary_symbol_match(
                            started_progress.code,
                            next_bits,
                            next_width,
                            symbol,
                        ));
                        if symbol < 16 {
                            self.phase = process_direct_symbol_length(
                                progress,
                                symbol,
                                self.alphabet_limit,
                            );
                        } else {
                            let (length, extra_bits) = if symbol == 16 {
                                (progress.prev_code_len, 2u8)
                            } else {
                                (0u8, 3u8)
                            };
                            progress.prefix_width = 0;
                            progress.prefix_bits = 0;
                            assert(progress.singleton == 18);
                            proof {
                                assert(0u8 < (1u8 << 0)) by (bit_vector);
                            }
                            assert(progress.valid(self.alphabet_limit));
                            self.phase = CodeDescriptionPhase::ComplexRepeat {
                                progress,
                                length,
                                extra_bits,
                            };
                        }
                    }
                    None => {
                        assert(!exists|symbol: u8| auxiliary_symbol_match(
                            started_progress.code,
                            next_bits,
                            next_width,
                            symbol,
                        ));
                        if next_width == 5 {
                            self.phase = CodeDescriptionPhase::Failed(
                                CodeDescriptionError::CodeLengthSpace,
                            );
                        } else {
                            progress.prefix_width = next_width;
                            progress.prefix_bits = next_bits;
                            self.phase = CodeDescriptionPhase::ComplexSymbol(progress);
                        }
                    }
                }
                }
                status = match self.phase {
                    CodeDescriptionPhase::Failed(error) => CodeDescriptionStatus::Failed(error),
                    _ => CodeDescriptionStatus::Progress,
                };
                assert(complex_symbol_transition_holds(
                    started_progress,
                    field as nat,
                    self.alphabet_limit,
                    self.phase,
                    status,
                ));
            }
            CodeDescriptionPhase::ComplexRepeat {
                progress,
                length,
                extra_bits,
            } => {
                assert(width == extra_bits as usize);
                assert(field < 8);
                proof { pow2_matches_small_shift(extra_bits); }
                let next = process_repeated_symbol_length(
                    progress,
                    length,
                    extra_bits,
                    field as u8,
                    self.alphabet_limit,
                );
                status = match next {
                    CodeDescriptionPhase::Failed(error) => CodeDescriptionStatus::Failed(error),
                    _ => CodeDescriptionStatus::Progress,
                };
                assert(repeated_symbol_transition_holds(
                    progress,
                    length,
                    extra_bits,
                    field as u8,
                    self.alphabet_limit,
                    next,
                    status,
                ));
                self.phase = next;
            }
            CodeDescriptionPhase::CompleteSimple(_)
            | CodeDescriptionPhase::CompleteComplexAlphabet(_)
            | CodeDescriptionPhase::ComplexPendingSpan { .. }
            | CodeDescriptionPhase::CompleteComplex { .. }
            | CodeDescriptionPhase::Failed(_) => {
                proof { assert(false); }
            }
        }

        match self.phase {
            CodeDescriptionPhase::CompleteComplexAlphabet(code) => {
                status = CodeDescriptionStatus::ComplexAlphabet(code);
            }
            CodeDescriptionPhase::CompleteComplex { decoded_symbols: symbols, .. } => {
                status = CodeDescriptionStatus::ComplexComplete { symbols };
            }
            CodeDescriptionPhase::Failed(error) => {
                status = CodeDescriptionStatus::Failed(error);
            }
            _ => {}
        }
        assert(code_transition_holds(
            phase,
            field as nat,
            self.alphabet_max,
            self.alphabet_limit,
            self.phase,
            status,
        ));
        assert(self.queue.valid());
        assert(1 <= self.alphabet_limit <= self.alphabet_max <= 704);
        proof { match self.phase {
            CodeDescriptionPhase::ComplexSymbol(progress) => {
                assert(progress.valid(self.alphabet_limit));
            },
            CodeDescriptionPhase::ComplexRepeat { progress, length, extra_bits } => {
                assert(progress.valid(self.alphabet_limit));
                assert(length == 0 || 1 <= length <= 15);
                assert((length == 0 && extra_bits == 3)
                    || (length != 0 && extra_bits == 2));
            },
            CodeDescriptionPhase::ComplexPendingSpan {
                start, span_count: count, length, after,
            } => {
                assert(count > 0);
                assert(length <= 15);
                assert(start as nat + count as nat <= self.alphabet_limit);
                assert(after.valid(self.alphabet_limit));
            },
            _ => {},
        } }
        assert(self.valid());
        CodeDescriptionStep { consumed: read.consumed, status }
    }
}

proof fn valid_bits_ignore_unused_storage(a: BitQueue, b: BitQueue)
    requires a.valid(), b.valid(),
        a.len == b.len, a.offset == b.offset,
        forall|i: int| 0 <= i < a.len ==> a.pending@[i] == b.pending@[i],
    ensures a.bits() == b.bits(),
{
    assert(a.bits() =~= b.bits());
}

}

#[cfg(test)]
mod tests {
    use super::*;

    fn pack_lsb_bits(bits: &[u8]) -> Vec<u8> {
        let mut bytes = vec![0u8; bits.len().div_ceil(8)];
        for (i, bit) in bits.iter().enumerate() {
            bytes[i / 8] |= (bit & 1) << (i % 8);
        }
        bytes
    }

    fn parse_meta_bits(bits: &[u8], one_byte_chunks: bool) -> (MetaBlockDecoder, MetaBlockStep) {
        let bytes = pack_lsb_bits(bits);
        let mut header = HeaderDecoder::new();
        let first = header.advance_header(&bytes, bytes.len() == 1);
        assert!(matches!(first.status, HeaderStatus::Complete { .. }));
        assert_eq!(first.consumed, 1);
        let mut decoder = MetaBlockDecoder::from_header(header).unwrap();
        let mut at = 1usize;
        for _ in 0..32 {
            let end = if one_byte_chunks {
                (at + 1).min(bytes.len())
            } else {
                bytes.len()
            };
            let final_input = end == bytes.len();
            let step = decoder.advance_field(&bytes[at..end], final_input);
            at += step.consumed;
            if !matches!(
                step.status,
                MetaBlockStatus::Progress | MetaBlockStatus::NeedInput
            ) {
                return (decoder, step);
            }
            if at == bytes.len() && matches!(step.status, MetaBlockStatus::NeedInput) {
                let terminal = decoder.advance_field(&[], true);
                return (decoder, terminal);
            }
        }
        panic!("meta-block parser did not terminate")
    }

    fn compressed_meta_prefix_bits() -> Vec<u8> {
        let mut bits = vec![0, 0, 0, 0];
        bits.extend([0; 16]);
        bits.push(0);
        bits
    }

    fn parse_code_description_bits_with_lengths(
        description_bits: &[u8],
        alphabet_max: u16,
        alphabet_limit: u16,
        one_byte_chunks: bool,
    ) -> (CodeDescriptionDecoder, CodeDescriptionStep, Vec<u8>) {
        let mut bits = compressed_meta_prefix_bits();
        bits.extend_from_slice(description_bits);
        let bytes = pack_lsb_bits(&bits);
        let mut header = HeaderDecoder::new();
        let first = header.advance_header(&bytes, false);
        assert!(matches!(first.status, HeaderStatus::Complete { .. }));
        let mut at = first.consumed;
        let mut meta = MetaBlockDecoder::from_header(header).unwrap();
        for _ in 0..32 {
            let end = if one_byte_chunks {
                (at + 1).min(bytes.len())
            } else {
                bytes.len()
            };
            let step = meta.advance_field(&bytes[at..end], end == bytes.len());
            at += step.consumed;
            if matches!(step.status, MetaBlockStatus::Complete(_)) {
                break;
            }
            assert!(matches!(
                step.status,
                MetaBlockStatus::Progress | MetaBlockStatus::NeedInput
            ));
        }
        assert!(matches!(meta.phase, MetaBlockPhase::Complete(_)));
        let mut decoder =
            CodeDescriptionDecoder::from_meta(meta, alphabet_max, alphabet_limit).unwrap();
        let mut lengths = Vec::new();
        for _ in 0..4096 {
            let end = if one_byte_chunks {
                (at + 1).min(bytes.len())
            } else {
                bytes.len()
            };
            let step = decoder.advance_field(&bytes[at..end], end == bytes.len());
            at += step.consumed;
            if let CodeDescriptionPhase::ComplexPendingSpan {
                start,
                span_count: count,
                length,
                ..
            } = decoder.phase
            {
                assert_eq!(start as usize, lengths.len());
                lengths.extend(std::iter::repeat_n(length, count as usize));
            }
            if !matches!(
                step.status,
                CodeDescriptionStatus::Progress
                    | CodeDescriptionStatus::NeedInput
                    | CodeDescriptionStatus::ComplexAlphabet(_)
            ) {
                return (decoder, step, lengths);
            }
            if at == bytes.len() && matches!(step.status, CodeDescriptionStatus::NeedInput) {
                let terminal = decoder.advance_field(&[], true);
                return (decoder, terminal, lengths);
            }
        }
        panic!("code-description parser did not terminate")
    }

    fn parse_code_description_bits(
        description_bits: &[u8],
        alphabet_max: u16,
        alphabet_limit: u16,
        one_byte_chunks: bool,
    ) -> (CodeDescriptionDecoder, CodeDescriptionStep) {
        let (decoder, step, _) = parse_code_description_bits_with_lengths(
            description_bits,
            alphabet_max,
            alphabet_limit,
            one_byte_chunks,
        );
        (decoder, step)
    }

    fn push_bits(bits: &mut Vec<u8>, value: u16, width: u8) {
        for i in 0..width {
            bits.push(((value >> i) & 1) as u8);
        }
    }

    fn push_static_code_length(bits: &mut Vec<u8>, value: u8) {
        match value {
            0 => bits.extend([0, 0]),
            4 => bits.extend([1, 0]),
            3 => bits.extend([0, 1]),
            2 => bits.extend([1, 1, 0]),
            1 => bits.extend([1, 1, 1, 0]),
            5 => bits.extend([1, 1, 1, 1]),
            _ => panic!("invalid static code-length value"),
        }
    }

    fn push_auxiliary_code_lengths(bits: &mut Vec<u8>, entries: &[(u8, u8)]) {
        let mut space = 32u8;
        for symbol in CODE_LENGTH_ORDER {
            let value = entries
                .iter()
                .find_map(|(entry_symbol, length)| {
                    if *entry_symbol == symbol {
                        Some(*length)
                    } else {
                        None
                    }
                })
                .unwrap_or(0);
            push_static_code_length(bits, value);
            space -= code_length_space_weight_exec(value);
            if space == 0 {
                return;
            }
        }
        assert_eq!(
            entries.len(),
            1,
            "only singleton auxiliary trees may be incomplete"
        );
    }

    fn visible_bits(queue: &BitQueue) -> Vec<u8> {
        let mut result = Vec::new();
        for at in queue.offset..queue.len * 8 {
            let byte = queue.pending[at / 8];
            result.push((byte >> (at % 8)) & 1);
        }
        result
    }

    fn header(first: u8, final_input: bool) -> (HeaderDecoder, HeaderStep) {
        let mut decoder = HeaderDecoder::new();
        let step = decoder.advance_header(&[first], final_input);
        (decoder, step)
    }

    #[test]
    fn all_first_bytes_match_rfc_window_header() {
        for byte in 0u8..=255 {
            let (decoder, step) = header(byte, true);
            let low = byte & 1;
            let middle = (byte >> 1) & 7;
            let last = (byte >> 4) & 7;
            let expected = if low == 0 {
                Ok(16)
            } else if middle != 0 {
                Ok(17 + middle)
            } else if last == 1 {
                Err(HeaderError::InvalidHeader)
            } else if last == 0 {
                Ok(17)
            } else {
                Ok(8 + last)
            };
            match (expected, step.status) {
                (
                    Ok(bits),
                    HeaderStatus::Complete {
                        window_bits,
                        window_size,
                    },
                ) => {
                    assert_eq!(window_bits, bits);
                    assert_eq!(window_size, (1u32 << bits) - 16);
                    let used = if low == 0 {
                        1
                    } else if middle != 0 {
                        4
                    } else {
                        7
                    };
                    assert_eq!(visible_bits(&decoder.queue).len(), 8 - used);
                }
                (Err(error), HeaderStatus::Failed(actual)) => assert_eq!(actual, error),
                pair => panic!("unexpected header result for {byte:#04x}: {pair:?}"),
            }
            assert_eq!(step.consumed, 1);
        }
    }

    #[test]
    fn empty_chunks_terminal_states_and_reset() {
        let mut decoder = HeaderDecoder::new();
        assert_eq!(
            decoder.advance_header(&[], false),
            HeaderStep {
                consumed: 0,
                status: HeaderStatus::NeedInput
            }
        );
        assert_eq!(
            decoder.advance_header(&[], true),
            HeaderStep {
                consumed: 0,
                status: HeaderStatus::Failed(HeaderError::Truncated)
            }
        );
        assert_eq!(
            decoder.advance_header(&[0], false),
            HeaderStep {
                consumed: 0,
                status: HeaderStatus::Failed(HeaderError::Truncated)
            }
        );
        decoder.reset();
        assert_eq!(
            decoder.advance_header(&[0, 0xff], false),
            HeaderStep {
                consumed: 1,
                status: HeaderStatus::Complete {
                    window_bits: 16,
                    window_size: 65_520
                }
            }
        );
        assert_eq!(
            decoder.advance_header(&[255], true),
            HeaderStep {
                consumed: 0,
                status: HeaderStatus::Complete {
                    window_bits: 16,
                    window_size: 65_520
                }
            }
        );
        decoder.reset();
        assert_eq!(
            decoder.advance_header(&[0x11], false),
            HeaderStep {
                consumed: 1,
                status: HeaderStatus::Failed(HeaderError::InvalidHeader)
            }
        );
        assert_eq!(
            decoder.advance_header(&[0], true),
            HeaderStep {
                consumed: 0,
                status: HeaderStatus::Failed(HeaderError::InvalidHeader)
            }
        );
    }

    #[test]
    fn bit_reader_widths_splits_and_old_storage() {
        for width in 0usize..=56 {
            for split in 0usize..=8 {
                let bytes = [0xa5, 0x3c, 0xf0, 0x17, 0x42, 0x99, 0x5a, 0xc3];
                let mut one = BitQueue::new();
                one.pending = [0x11; 8];
                let all = one.read_bits(width, &bytes, true);

                let mut split_queue = BitQueue::new();
                split_queue.pending = [0xee; 8];
                let first = split_queue.read_bits(width, &bytes[..split], false);
                let split_result = match first.status {
                    BitReadStatus::NeedInput => split_queue.read_bits(width, &bytes[split..], true),
                    _ => first,
                };
                assert_eq!(all.status, split_result.status);
                assert_eq!(visible_bits(&one), visible_bits(&split_queue));
                assert!(one.len <= 8 && split_queue.len <= 8);
            }
        }
    }

    #[test]
    fn changing_widths_preserves_the_bit_stream() {
        let mut queue = BitQueue::new();
        let bytes = [0b1101_0010, 0b0110_1001, 0xff, 0, 0x55, 0xaa, 0x81, 0x7e];
        let mut at = 0;
        let a = queue.read_bits(3, &bytes[at..at + 1], false);
        at += a.consumed;
        let b = queue.read_bits(5, &bytes[at..at + 1], false);
        at += b.consumed;
        let c = queue.read_bits(16, &bytes[at..at + 2], false);
        at += c.consumed;
        let d = queue.read_bits(40, &bytes[at..], true);
        at += d.consumed;
        assert!(matches!(a.status, BitReadStatus::Value(_)));
        assert!(matches!(b.status, BitReadStatus::Value(_)));
        assert!(matches!(c.status, BitReadStatus::Value(_)));
        assert!(matches!(d.status, BitReadStatus::Value(_)));
        assert_eq!(at, bytes.len());
        assert_eq!(visible_bits(&queue).len(), 0);
    }

    #[test]
    fn meta_block_headers_cover_empty_normal_and_metadata_forms() {
        for chunks in [false, true] {
            let (_, empty) = parse_meta_bits(&[0, 1, 1], chunks);
            assert_eq!(
                empty.status,
                MetaBlockStatus::Complete(MetaBlockHeader {
                    is_last: true,
                    is_empty: true,
                    is_uncompressed: false,
                    is_metadata: false,
                    length: 0,
                })
            );

            let mut uncompressed = vec![0, 0, 0, 0];
            uncompressed.extend([0; 16]);
            uncompressed.push(1);
            let (_, normal) = parse_meta_bits(&uncompressed, chunks);
            assert_eq!(
                normal.status,
                MetaBlockStatus::Complete(MetaBlockHeader {
                    is_last: false,
                    is_empty: false,
                    is_uncompressed: true,
                    is_metadata: false,
                    length: 1,
                })
            );

            let mut last = vec![0, 1, 0, 0, 0, 1];
            last.extend([0; 15]);
            let (_, final_normal) = parse_meta_bits(&last, chunks);
            assert_eq!(
                final_normal.status,
                MetaBlockStatus::Complete(MetaBlockHeader {
                    is_last: true,
                    is_empty: false,
                    is_uncompressed: false,
                    is_metadata: false,
                    length: 2,
                })
            );

            let (_, zero_metadata) = parse_meta_bits(&[0, 0, 1, 1, 0, 0, 0], chunks);
            assert_eq!(
                zero_metadata.status,
                MetaBlockStatus::Complete(MetaBlockHeader {
                    is_last: false,
                    is_empty: false,
                    is_uncompressed: false,
                    is_metadata: true,
                    length: 0,
                })
            );

            let mut metadata = vec![0, 0, 1, 1, 0, 0, 1];
            metadata.extend([0; 8]);
            metadata.extend([1, 0, 0, 0, 0, 0, 0, 0]);
            let (_, sized_metadata) = parse_meta_bits(&metadata, chunks);
            assert_eq!(
                sized_metadata.status,
                MetaBlockStatus::Complete(MetaBlockHeader {
                    is_last: false,
                    is_empty: false,
                    is_uncompressed: false,
                    is_metadata: true,
                    length: 257,
                })
            );
        }
    }

    #[test]
    fn meta_block_errors_are_permanent_and_truthful() {
        let (mut reserved_decoder, reserved) = parse_meta_bits(&[0, 0, 1, 1, 1], true);
        assert_eq!(
            reserved.status,
            MetaBlockStatus::Failed(MetaBlockError::ReservedBit)
        );
        assert_eq!(
            reserved_decoder.advance_field(&[0xff], false),
            MetaBlockStep {
                consumed: 0,
                status: MetaBlockStatus::Failed(MetaBlockError::ReservedBit),
            }
        );

        let mut exuberant = vec![0, 0, 1, 0];
        exuberant.extend([1, 0, 0, 0]);
        exuberant.extend([0; 16]);
        let (_, normal_error) = parse_meta_bits(&exuberant, false);
        assert_eq!(
            normal_error.status,
            MetaBlockStatus::Failed(MetaBlockError::ExuberantLength)
        );

        let mut metadata = vec![0, 0, 1, 1, 0, 0, 1];
        metadata.extend([1, 0, 0, 0, 0, 0, 0, 0]);
        metadata.extend([0; 8]);
        let (_, metadata_error) = parse_meta_bits(&metadata, true);
        assert_eq!(
            metadata_error.status,
            MetaBlockStatus::Failed(MetaBlockError::ExuberantMetadataLength)
        );

        let (_, truncated) = parse_meta_bits(&[0, 0], true);
        assert_eq!(
            truncated.status,
            MetaBlockStatus::Failed(MetaBlockError::Truncated)
        );
    }

    #[test]
    fn simple_code_descriptions_cover_all_rfc_shapes_and_chunks() {
        for chunks in [false, true] {
            for (raw_selector, shape, symbols, expected_selector) in [
                (0u8, None, vec![5u16], 0u8),
                (1, None, vec![1, 6], 1),
                (2, None, vec![0, 3, 7], 2),
                (3, Some(0u8), vec![0, 2, 4, 6], 3),
                (3, Some(1u8), vec![1, 3, 5, 7], 4),
            ] {
                let mut bits = vec![1, 0];
                push_bits(&mut bits, raw_selector as u16, 2);
                for symbol in &symbols {
                    push_bits(&mut bits, *symbol, 3);
                }
                if let Some(bit) = shape {
                    bits.push(bit);
                }
                let (_, step) = parse_code_description_bits(&bits, 8, 8, chunks);
                let code = match step.status {
                    CodeDescriptionStatus::Simple(code) => code,
                    other => panic!("unexpected simple result: {other:?}"),
                };
                assert_eq!(code.selector, expected_selector);
                assert_eq!(code.count as usize, symbols.len());
                assert_eq!(&code.symbols[..symbols.len()], symbols.as_slice());
            }
        }
    }

    #[test]
    fn simple_code_description_errors_are_permanent() {
        let mut duplicate = vec![1, 0, 1, 0];
        push_bits(&mut duplicate, 3, 3);
        push_bits(&mut duplicate, 3, 3);
        let (mut decoder, step) = parse_code_description_bits(&duplicate, 8, 8, true);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::DuplicateSimpleSymbol)
        );
        assert_eq!(
            decoder.advance_field(&[0xff], false),
            CodeDescriptionStep {
                consumed: 0,
                status: CodeDescriptionStatus::Failed(CodeDescriptionError::DuplicateSimpleSymbol,),
            }
        );

        let mut outside = vec![1, 0, 0, 0];
        push_bits(&mut outside, 6, 3);
        let (_, step) = parse_code_description_bits(&outside, 8, 4, false);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::InvalidAlphabet)
        );

        let truncated = vec![1, 0, 0, 0];
        let (_, step) = parse_code_description_bits(&truncated, 704, 704, true);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated)
        );
    }

    #[test]
    fn complex_code_length_alphabet_parses_static_prefixes() {
        for chunks in [false, true] {
            let mut two_length_one = vec![0, 0];
            push_static_code_length(&mut two_length_one, 1);
            push_static_code_length(&mut two_length_one, 1);
            two_length_one.extend([0, 0]);
            let (decoder, step) = parse_code_description_bits(&two_length_one, 2, 2, chunks);
            assert_eq!(
                step.status,
                CodeDescriptionStatus::ComplexComplete { symbols: 2 }
            );
            let code = match decoder.phase {
                CodeDescriptionPhase::CompleteComplex { code, .. } => code,
                other => panic!("unexpected complex phase: {other:?}"),
            };
            assert_eq!(code.lengths[1], 1);
            assert_eq!(code.lengths[2], 1);

            for value in [4u8, 5u8] {
                let mut singleton = vec![0, 0];
                push_static_code_length(&mut singleton, value);
                for _ in 1..18 {
                    push_static_code_length(&mut singleton, 0);
                }
                let (decoder, step) = parse_code_description_bits(&singleton, 2, 2, chunks);
                assert_eq!(
                    step.status,
                    CodeDescriptionStatus::ComplexComplete { symbols: 2 }
                );
                let code = match decoder.phase {
                    CodeDescriptionPhase::CompleteComplex { code, .. } => code,
                    other => panic!("unexpected singleton complex phase: {other:?}"),
                };
                assert_eq!(code.lengths[1], value);
            }

            let mut skip_three = vec![1, 1];
            push_static_code_length(&mut skip_three, 1);
            push_static_code_length(&mut skip_three, 1);
            skip_three.extend([1; 16]);
            let (decoder, step) = parse_code_description_bits(&skip_three, 16, 16, chunks);
            assert_eq!(
                step.status,
                CodeDescriptionStatus::ComplexComplete { symbols: 16 }
            );
            let code = match decoder.phase {
                CodeDescriptionPhase::CompleteComplex { code, .. } => code,
                other => panic!("unexpected skipped complex phase: {other:?}"),
            };
            assert_eq!(code.skip, 3);
            assert_eq!(code.lengths[4], 1);
            assert_eq!(code.lengths[0], 1);
        }
    }

    #[test]
    fn complex_code_length_space_errors_are_permanent() {
        let mut oversubscribed = vec![0, 0];
        for value in [2u8, 1, 1] {
            push_static_code_length(&mut oversubscribed, value);
        }
        let (_, step) = parse_code_description_bits(&oversubscribed, 256, 256, true);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
        );

        let mut incomplete = vec![0, 0];
        push_static_code_length(&mut incomplete, 2);
        push_static_code_length(&mut incomplete, 2);
        for _ in 2..18 {
            push_static_code_length(&mut incomplete, 0);
        }
        let (_, step) = parse_code_description_bits(&incomplete, 256, 256, false);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
        );
    }

    #[test]
    fn complex_repeats_follow_rfc_chaining_in_whole_and_one_byte_chunks() {
        for chunks in [false, true] {
            let mut previous = vec![0, 0];
            push_auxiliary_code_lengths(&mut previous, &[(8, 1), (16, 1)]);
            for final_suffix in [1u16, 1, 2] {
                previous.push(0); // Direct length 8.
                previous.push(1); // Repeat previous length.
                push_bits(&mut previous, 3, 2); // repeat = 6
                previous.push(1);
                push_bits(&mut previous, 3, 2); // repeat = 22
                previous.push(1);
                push_bits(&mut previous, final_suffix, 2); // repeat = 84, 84, 85
            }
            let (decoder, step, lengths) =
                parse_code_description_bits_with_lengths(&previous, 256, 256, chunks);
            assert_eq!(
                step.status,
                CodeDescriptionStatus::ComplexComplete { symbols: 256 }
            );
            assert!(matches!(
                decoder.phase,
                CodeDescriptionPhase::CompleteComplex { .. }
            ));
            assert_eq!(lengths, vec![8u8; 256]);

            let mut zero = vec![0, 0];
            push_auxiliary_code_lengths(&mut zero, &[(1, 1), (17, 1)]);
            zero.push(1);
            push_bits(&mut zero, 0, 3); // Three zero lengths.
            zero.push(1);
            push_bits(&mut zero, 0, 3); // Chain to eleven zero lengths.
            zero.extend([0, 0]); // Two direct length-1 symbols exhaust the space.
            let (_, step, lengths) =
                parse_code_description_bits_with_lengths(&zero, 13, 13, chunks);
            assert_eq!(
                step.status,
                CodeDescriptionStatus::ComplexComplete { symbols: 13 }
            );
            assert_eq!(lengths, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]);
        }
    }

    #[test]
    fn complex_auxiliary_codes_reverse_nonpalindromic_stream_bits() {
        for chunks in [false, true] {
            let mut bits = vec![0, 0];
            push_auxiliary_code_lengths(&mut bits, &[(7, 2), (8, 2), (16, 1)]);
            for _ in 0..128 {
                // Natural canonical code 2 is `10`; the LSB-first stream value is 1.
                push_bits(&mut bits, 1, 2);
            }
            let (_, step, lengths) =
                parse_code_description_bits_with_lengths(&bits, 128, 128, chunks);
            assert_eq!(
                step.status,
                CodeDescriptionStatus::ComplexComplete { symbols: 128 }
            );
            assert_eq!(lengths, vec![7u8; 128]);
        }
    }

    #[test]
    fn complex_repeat_overflow_truncation_and_failure_are_permanent() {
        let mut overflow = vec![0, 0];
        push_auxiliary_code_lengths(&mut overflow, &[(7, 1), (16, 1)]);
        overflow.push(1);
        push_bits(&mut overflow, 0, 2);
        let (mut decoder, step) = parse_code_description_bits(&overflow, 2, 2, true);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace)
        );
        assert_eq!(
            decoder.advance_field(&[0xff], false),
            CodeDescriptionStep {
                consumed: 0,
                status: CodeDescriptionStatus::Failed(CodeDescriptionError::CodeLengthSpace),
            }
        );

        let mut truncated = vec![0, 0];
        push_auxiliary_code_lengths(&mut truncated, &[(7, 1), (16, 1)]);
        truncated.push(1);
        assert_eq!(
            (compressed_meta_prefix_bits().len() + truncated.len()) % 8,
            0
        );
        let (mut decoder, step) = parse_code_description_bits(&truncated, 8, 8, true);
        assert_eq!(
            step.status,
            CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated)
        );
        assert_eq!(
            decoder.advance_field(&[], false),
            CodeDescriptionStep {
                consumed: 0,
                status: CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated),
            }
        );
    }
}
