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
}
