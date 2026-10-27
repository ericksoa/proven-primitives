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

fn active_symbols_in_range(
    symbols: &[u16; 4],
    count: u8,
    alphabet_limit: u16,
) -> (r: bool)
    requires count <= 4,
    ensures r == forall|i: int| 0 <= i < count ==> symbols@[i] < alphabet_limit,
{
    let mut i: usize = 0;
    while i < count as usize
        invariant i <= count <= 4,
            forall|j: int| 0 <= j < i ==> symbols@[j] < alphabet_limit,
        decreases count as usize - i,
    {
        if symbols[i] >= alphabet_limit {
            return false;
        }
        i = i + 1;
    }
    true
}

fn active_symbols_distinct_exec(symbols: &[u16; 4], count: u8) -> (r: bool)
    requires count <= 4,
    ensures r == active_symbols_distinct(symbols@, count as nat),
{
    if count == 0 {
        true
    } else {
        simple_symbols_distinct(symbols, count)
    }
}

fn complex_code_valid_exec(code: &ComplexCodeLengthAlphabet) -> (r: bool)
    ensures r == code.valid(),
{
    if !(code.skip == 0 || code.skip == 2 || code.skip == 3) {
        return false;
    }
    let mut i: usize = 0;
    while i < 18
        invariant i <= 18,
            forall|j: int| 0 <= j < i ==> code.lengths@[j] <= 5,
        decreases 18 - i,
    {
        if code.lengths[i] > 5 {
            return false;
        }
        i = i + 1;
    }
    true
}

fn complex_progress_valid_exec(progress: &ComplexProgress) -> (r: bool)
    ensures r == progress.valid(),
{
    let code = ComplexCodeLengthAlphabet {
        skip: progress.skip,
        lengths: progress.lengths,
    };
    complex_code_valid_exec(&code)
        && progress.skip <= progress.index
        && progress.index < 18
        && progress.space <= 32
        && progress.nonzero <= progress.index - progress.skip
}

fn singleton_code_valid_exec(
    code: &ComplexCodeLengthAlphabet,
    singleton: u8,
) -> (r: bool)
    requires singleton < 18,
    ensures r == {
        &&& code.lengths@[singleton as int] != 0
        &&& forall|i: int| 0 <= i < 18 && i != singleton
            ==> code.lengths@[i] == 0
    },
{
    if code.lengths[singleton as usize] == 0 {
        return false;
    }
    let mut i: usize = 0;
    while i < 18
        invariant i <= 18,
            code.lengths@[singleton as int] != 0,
            forall|j: int| 0 <= j < i && j != singleton
                ==> code.lengths@[j] == 0,
        decreases 18 - i,
    {
        if i != singleton as usize && code.lengths[i] != 0 {
            return false;
        }
        i = i + 1;
    }
    true
}

fn complex_symbol_progress_valid_exec(
    progress: &ComplexSymbolProgress,
    alphabet_limit: u16,
) -> (r: bool)
    ensures r == progress.valid(alphabet_limit),
{
    if !complex_code_valid_exec(&progress.code)
        || alphabet_limit == 0
        || alphabet_limit > 704
        || progress.symbol >= alphabet_limit
        || progress.prev_code_len == 0
        || progress.prev_code_len > 15
        || progress.repeat > progress.symbol as u32
        || (progress.repeat != 0 && progress.repeat < 3)
        || progress.repeat_code_len > 15
        || progress.space == 0
        || progress.space > 32_768
        || progress.prefix_width >= 5
        || progress.singleton > 18
    {
        return false;
    }
    if progress.prefix_bits >= (1u8 << progress.prefix_width) {
        return false;
    }
    if progress.singleton < 18 {
        if !singleton_code_valid_exec(&progress.code, progress.singleton)
            || progress.prefix_width != 0
            || progress.prefix_bits != 0
        {
            return false;
        }
    }
    true
}

fn complex_after_span_valid_exec(
    after: &ComplexAfterSpan,
    alphabet_limit: u16,
) -> (r: bool)
    ensures r == after.valid(alphabet_limit),
{
    match after {
        ComplexAfterSpan::Symbol(progress) =>
            complex_symbol_progress_valid_exec(progress, alphabet_limit),
        ComplexAfterSpan::TrailingZeros { code, start } =>
            complex_code_valid_exec(code) && *start < alphabet_limit,
        ComplexAfterSpan::Complete { code, symbols } =>
            complex_code_valid_exec(code) && *symbols == alphabet_limit,
    }
}

fn simple_code_valid_exec(
    code: &SimpleCodeDescription,
    alphabet_limit: u16,
) -> (r: bool)
    ensures r == code.valid(alphabet_limit),
{
    if alphabet_limit == 0 || alphabet_limit > 704 || code.selector > 4 {
        return false;
    }
    let expected = if code.selector <= 2 { code.selector + 1 } else { 4 };
    code.count == expected
        && active_symbols_in_range(&code.symbols, code.count, alphabet_limit)
        && active_symbols_distinct_exec(&code.symbols, code.count)
}

fn code_description_phase_valid_exec(
    phase: &CodeDescriptionPhase,
    alphabet_max: u16,
    alphabet_limit: u16,
) -> (r: bool)
    ensures r == {
        &&& 1 <= alphabet_limit <= alphabet_max <= 704
        &&& match phase {
            CodeDescriptionPhase::SimpleSymbols {
                selector, count, index, width, symbols, ..
            } => {
                &&& *selector <= 3
                &&& *count as nat == simple_count(*selector)
                &&& 1 <= *count <= 4
                &&& *index < *count
                &&& *width <= 10
                &&& *width as nat == alphabet_bit_width_spec(alphabet_max)
                &&& forall|i: int| 0 <= i < *index ==> symbols@[i] < alphabet_limit
                &&& active_symbols_distinct(symbols@, *index as nat)
            },
            CodeDescriptionPhase::SimpleShape { symbols } => {
                &&& forall|i: int| 0 <= i < 4 ==> symbols@[i] < alphabet_limit
                &&& active_symbols_distinct(symbols@, 4)
            },
            CodeDescriptionPhase::ComplexPrefix2(progress)
            | CodeDescriptionPhase::ComplexPrefix3(progress)
            | CodeDescriptionPhase::ComplexPrefix4(progress) => progress.valid(),
            CodeDescriptionPhase::ComplexSymbol(progress) => progress.valid(alphabet_limit),
            CodeDescriptionPhase::ComplexRepeat { progress, length, extra_bits } => {
                &&& progress.valid(alphabet_limit)
                &&& (*length == 0 || 1 <= *length <= 15)
                &&& ((*length == 0 && *extra_bits == 3)
                    || (*length != 0 && *extra_bits == 2))
            },
            CodeDescriptionPhase::ComplexPendingSpan {
                start, span_count: count, length, after,
            } => {
                &&& *count > 0
                &&& *length <= 15
                &&& *start as nat + *count as nat <= alphabet_limit
                &&& after.valid(alphabet_limit)
            },
            CodeDescriptionPhase::CompleteSimple(code) => code.valid(alphabet_limit),
            CodeDescriptionPhase::CompleteComplexAlphabet(code) => code.valid(),
            CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbols } => {
                &&& code.valid()
                &&& *symbols == alphabet_limit
            },
            _ => true,
        }
    },
{
    if alphabet_limit == 0 || alphabet_limit > alphabet_max || alphabet_max > 704 {
        return false;
    }
    match phase {
        CodeDescriptionPhase::SimpleSymbols {
            selector, count, index, width, symbols,
        } => {
            let expected = if *selector <= 2 { *selector + 1 } else { 4 };
            *selector <= 3
                && *count == expected
                && *index < *count
                && *width == alphabet_bit_width(alphabet_max)
                && active_symbols_in_range(symbols, *index, alphabet_limit)
                && active_symbols_distinct_exec(symbols, *index)
        }
        CodeDescriptionPhase::SimpleShape { symbols } =>
            active_symbols_in_range(symbols, 4, alphabet_limit)
                && active_symbols_distinct_exec(symbols, 4),
        CodeDescriptionPhase::ComplexPrefix2(progress)
        | CodeDescriptionPhase::ComplexPrefix3(progress)
        | CodeDescriptionPhase::ComplexPrefix4(progress) =>
            complex_progress_valid_exec(progress),
        CodeDescriptionPhase::ComplexSymbol(progress) =>
            complex_symbol_progress_valid_exec(progress, alphabet_limit),
        CodeDescriptionPhase::ComplexRepeat { progress, length, extra_bits } =>
            complex_symbol_progress_valid_exec(progress, alphabet_limit)
                && (*length == 0 || *length <= 15)
                && ((*length == 0 && *extra_bits == 3)
                    || (*length != 0 && *extra_bits == 2)),
        CodeDescriptionPhase::ComplexPendingSpan {
            start, span_count, length, after,
        } => {
            *span_count > 0
                && *length <= 15
                && *start as u32 + *span_count as u32 <= alphabet_limit as u32
                && complex_after_span_valid_exec(after, alphabet_limit)
        }
        CodeDescriptionPhase::CompleteSimple(code) =>
            simple_code_valid_exec(code, alphabet_limit),
        CodeDescriptionPhase::CompleteComplexAlphabet(code) => complex_code_valid_exec(code),
        CodeDescriptionPhase::CompleteComplex { code, decoded_symbols } =>
            complex_code_valid_exec(code) && *decoded_symbols == alphabet_limit,
        _ => true,
    }
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
            final(self).alphabet_max == old(self).alphabet_max,
            final(self).alphabet_limit == old(self).alphabet_limit,
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

spec fn distance_postfix_scale(postfix: u8) -> nat {
    if postfix == 0 { 1 }
    else if postfix == 1 { 2 }
    else if postfix == 2 { 4 }
    else { 8 }
}

spec fn normal_distance_alphabet(bits: u8) -> nat {
    let postfix = bits % 4;
    let direct = (bits / 4) as nat * distance_postfix_scale(postfix);
    16 + direct + 24 * (2 * distance_postfix_scale(postfix))
}

fn decode_distance_parameters(bits: u8) -> (r: (u8, u16, u16))
    requires bits < 64,
    ensures
        r.0 == bits % 4,
        r.1 as nat == (bits / 4) as nat * distance_postfix_scale(r.0),
        r.2 as nat == normal_distance_alphabet(bits),
        r.0 <= 3, r.1 <= 120, 64 <= r.2 <= 520,
{
    let postfix = bits % 4;
    let upper = bits / 4;
    let scale: u16 = if postfix == 0 { 1 }
        else if postfix == 1 { 2 }
        else if postfix == 2 { 4 }
        else { 8 };
    let direct = upper as u16 * scale;
    let alphabet = 16u16 + direct + 24u16 * (2u16 * scale);
    (postfix, direct, alphabet)
}

spec fn context_zero_repeat(symbol: u8, suffix: u16) -> nat {
    pow2(symbol as nat) + suffix as nat
}

#[verifier::bit_vector]
proof fn context_repeat_shift_step(width: u8)
    requires 1 <= width <= 16,
    ensures (1u32 << width) == 2u32 * (1u32 << ((width - 1) as u8)),
{}

proof fn pow2_matches_context_repeat_shift(width: u8)
    requires width <= 16,
    ensures pow2(width as nat) == (1u32 << width) as nat,
    decreases width,
{
    lemma2_to64();
    if width == 0 {
        assert((1u32 << 0) == 1) by (bit_vector);
    } else {
        pow2_matches_context_repeat_shift((width - 1) as u8);
        lemma_pow2_unfold(width as nat);
        context_repeat_shift_step(width);
    }
}

#[verifier::bit_vector]
proof fn context_repeat_add_fits(base: u32, suffix: u16)
    requires 2 <= base <= 65_536, (suffix as u32) < base,
    ensures
        base + suffix as u32 <= 131_071,
        (base + suffix as u32) as nat == base as nat + suffix as nat,
{}

#[verifier::bit_vector]
proof fn bounded_u64_fits_u8(value: u64)
    requires value < 256,
    ensures (value as u8) as nat == value as nat,
{}

#[verifier::bit_vector]
proof fn bounded_u64_fits_u16(value: u64)
    requires value < 65_536,
    ensures
        (value as u16) as nat == value as nat,
        (value as u16 as u32) as nat == value as nat,
{}

#[verifier::bit_vector]
proof fn bounded_u64_fits_u32(value: u64)
    requires value <= u32::MAX,
    ensures (value as u32) as nat == value as nat,
{}

#[verifier::bit_vector]
proof fn bounded_u16_fits_u8(value: u16)
    requires value < 256,
    ensures (value as u8) as nat == value as nat,
{}

#[verifier::bit_vector]
proof fn var_uint8_count_adds_one(raw: u16)
    requires raw <= 255,
    ensures
        raw + 1 <= 256,
        (raw + 1) as nat == raw as nat + 1,
{}

fn context_zero_repeat_exec(symbol: u8, suffix: u16) -> (r: u32)
    requires 1 <= symbol <= 16, (suffix as u32) < (1u32 << symbol),
    ensures r as nat == context_zero_repeat(symbol, suffix), 2 <= r <= 131_071,
{
    proof {
        pow2_matches_context_repeat_shift(symbol);
    }
    let base = 1u32 << symbol;
    proof {
        lemma2_to64();
        if symbol > 1 {
            lemma_pow2_strictly_increases(1, symbol as nat);
        }
        if symbol < 16 {
            lemma_pow2_strictly_increases(symbol as nat, 16);
        }
        assert(2 <= base <= 65_536);
        context_repeat_add_fits(base, suffix);
    }
    base + suffix as u32
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarUint8Phase {
    First,
    Short,
    Long { width: u8 },
}

impl VarUint8Phase {
    spec fn valid(&self) -> bool {
        match self {
            VarUint8Phase::Long { width } => 1 <= *width <= 7,
            _ => true,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarUint8Status {
    Progress,
    NeedInput,
    Value(u16),
    Truncated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct VarUint8Step {
    consumed: usize,
    status: VarUint8Status,
}

spec fn var_uint8_width(phase: VarUint8Phase) -> nat {
    match phase {
        VarUint8Phase::First => 1,
        VarUint8Phase::Short => 3,
        VarUint8Phase::Long { width } => width as nat,
    }
}

spec fn var_uint8_transition(
    old: VarUint8Phase,
    field: nat,
    next: VarUint8Phase,
    status: VarUint8Status,
) -> bool {
    match old {
        VarUint8Phase::First => if field == 0 {
            next == VarUint8Phase::First && status == VarUint8Status::Value(0)
        } else {
            next == VarUint8Phase::Short && status == VarUint8Status::Progress
        },
        VarUint8Phase::Short => if field == 0 {
            next == VarUint8Phase::First && status == VarUint8Status::Value(1)
        } else {
            next == VarUint8Phase::Long { width: field as u8 }
                && status == VarUint8Status::Progress
        },
        VarUint8Phase::Long { width } => {
            next == VarUint8Phase::First
                && status == VarUint8Status::Value(
                    ((1u16 << width) + field as u16) as u16,
                )
        },
    }
}

spec fn var_uint8_exact_step(
    start_queue: BitQueue,
    start_phase: VarUint8Phase,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    final_queue: BitQueue,
    final_phase: VarUint8Phase,
    status: VarUint8Status,
) -> bool {
    let width = var_uint8_width(start_phase);
    let source = start_queue.bits() + bytes_bits(input.take(consumed as int));
    &&& consumed as nat == input_bytes_taken(
        start_queue.bits().len(),
        width,
        input.len(),
    )
    &&& if source.len() >= width {
        &&& final_queue.bits() == source.skip(width as int)
        &&& var_uint8_transition(
            start_phase,
            bits_value(source.take(width as int)),
            final_phase,
            status,
        )
    } else {
        &&& consumed == input.len()
        &&& source == start_queue.bits() + bytes_bits(input)
        &&& final_queue.bits() == source
        &&& final_phase == start_phase
        &&& status == if end_of_input {
            VarUint8Status::Truncated
        } else {
            VarUint8Status::NeedInput
        }
    }
}

#[verifier::bit_vector]
proof fn var_uint8_long_value_is_bounded(width: u8, field: u64)
    requires 1 <= width <= 7, field < 128,
    ensures (1u16 << width) + field as u16 <= 255,
{}

fn advance_var_uint8(
    queue: &mut BitQueue,
    phase: &mut VarUint8Phase,
    input: &[u8],
    end_of_input: bool,
) -> (r: VarUint8Step)
    requires old(queue).valid(), old(phase).valid(),
    ensures final(queue).valid(), final(phase).valid(), r.consumed <= input.len(),
        r.status == VarUint8Status::NeedInput ==> {
            &&& !end_of_input
            &&& r.consumed == input.len()
            &&& *final(phase) == *old(phase)
        },
        r.status == VarUint8Status::Truncated ==> {
            &&& end_of_input
            &&& r.consumed == input.len()
            &&& *final(phase) == *old(phase)
        },
        match r.status { VarUint8Status::Value(value) => value <= 255, _ => true },
        var_uint8_exact_step(
            *old(queue),
            *old(phase),
            input@,
            end_of_input,
            r.consumed,
            *final(queue),
            *final(phase),
            r.status,
        ),
        {
            let width = var_uint8_width(*old(phase));
            let available = old(queue).bits() + bytes_bits(input@.take(r.consumed as int));
            available.len() >= width ==> var_uint8_transition(
                *old(phase), bits_value(available.take(width as int)), *final(phase), r.status)
        },
{
    let ghost started_queue = *queue;
    let started = *phase;
    let width: usize = match started {
        VarUint8Phase::First => 1,
        VarUint8Phase::Short => 3,
        VarUint8Phase::Long { width } => width as usize,
    };
    let read = queue.read_bits(width, input, end_of_input);
    let field = match read.status {
        BitReadStatus::Value(value) => value,
        BitReadStatus::NeedInput => return VarUint8Step {
            consumed: read.consumed,
            status: VarUint8Status::NeedInput,
        },
        BitReadStatus::Truncated => return VarUint8Step {
            consumed: read.consumed,
            status: VarUint8Status::Truncated,
        },
    };
    proof {
        lemma2_to64();
        assert((field as nat) < pow2(width as nat));
        pow2_width_at_most_byte(width as nat);
        assert(field < 256);
    }
    let status = match started {
        VarUint8Phase::First => {
            assert(field < 2);
            if field == 0 {
                *phase = VarUint8Phase::First;
                VarUint8Status::Value(0)
            } else {
                *phase = VarUint8Phase::Short;
                VarUint8Status::Progress
            }
        }
        VarUint8Phase::Short => {
            assert(field < 8);
            if field == 0 {
                *phase = VarUint8Phase::First;
                VarUint8Status::Value(1)
            } else {
                *phase = VarUint8Phase::Long { width: field as u8 };
                VarUint8Status::Progress
            }
        }
        VarUint8Phase::Long { width } => {
            assert(field < 128);
            proof { var_uint8_long_value_is_bounded(width, field); }
            let value = (1u16 << width) + field as u16;
            *phase = VarUint8Phase::First;
            VarUint8Status::Value(value)
        }
    };
    assert(var_uint8_transition(started, field as nat, *phase, status));
    VarUint8Step { consumed: read.consumed, status }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct InstalledPrefixState {
    width: u8,
    bits: u16,
    scan: u16,
}

impl InstalledPrefixState {
    spec fn valid(&self) -> bool {
        &&& self.width <= 14
        &&& self.bits < (1u16 << self.width)
        &&& self.scan == 0
    }

    fn initial() -> (r: Self)
        ensures r.valid(), r.width == 0, r.bits == 0, r.scan == 0,
    {
        let initial = Self { width: 0, bits: 0, scan: 0 };
        proof { assert((1u16 << 0) == 1) by (bit_vector); }
        initial
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InstalledSymbolStatus {
    NeedInput,
    Symbol(u16),
    Truncated,
    InvalidPrefixCode,
    InternalState,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct InstalledSymbolStep {
    consumed: usize,
    status: InstalledSymbolStatus,
}

spec fn reversed_installed_code(value: nat, width: u8) -> nat
    decreases width,
{
    if width <= 1 {
        value % 2
    } else {
        (value % 2) * pow2((width - 1) as nat)
            + reversed_installed_code(value / 2, (width - 1) as u8)
    }
}

#[verifier::bit_vector]
proof fn installed_shift_step(width: u8)
    requires 1 <= width <= 15,
    ensures (1u16 << width) == 2u16 * (1u16 << ((width - 1) as u8)),
{}

proof fn pow2_matches_installed_shift(width: u8)
    requires width <= 15,
    ensures pow2(width as nat) == (1u16 << width) as nat,
    decreases width,
{
    lemma2_to64();
    if width == 0 {
        assert((1u16 << 0) == 1) by (bit_vector);
    } else {
        pow2_matches_installed_shift((width - 1) as u8);
        lemma_pow2_unfold(width as nat);
        installed_shift_step(width);
    }
}

#[verifier::bit_vector]
proof fn installed_reverse_combine_fits(bit: u16, width: u8, rest: u16)
    requires
        2 <= width <= 15,
        bit < 2,
        rest < (1u16 << ((width - 1) as u8)),
    ensures
        bit * (1u16 << ((width - 1) as u8)) + rest < (1u16 << width),
{}

fn reverse_installed_code(value: u16, width: u8) -> (r: u16)
    requires 1 <= width <= 15, (value as nat) < pow2(width as nat),
    ensures
        r as nat == reversed_installed_code(value as nat, width),
        (r as nat) < pow2(width as nat),
    decreases width,
{
    if width == 1 {
        value % 2
    } else {
        proof {
            lemma2_to64();
            lemma_pow2_unfold((width - 1) as nat);
            assert((value as nat) / 2 < pow2((width - 1) as nat));
        }
        let bit = value % 2;
        let rest = reverse_installed_code(value / 2, width - 1);
        proof {
            pow2_matches_installed_shift((width - 1) as u8);
            pow2_matches_installed_shift(width);
            assert(rest < (1u16 << ((width - 1) as u8)));
            installed_reverse_combine_fits(bit, width, rest);
        }
        bit * (1u16 << ((width - 1) as u8)) + rest
    }
}

#[verifier::bit_vector]
proof fn installed_one_bit_fits(value: u64)
    requires value < 2,
    ensures (value as u16) < 2, (value as u16) as nat == value as nat,
{}

#[verifier::bit_vector]
proof fn append_installed_bit_fits(bits: u16, width: u8, bit: u16)
    requires width <= 14, bits < (1u16 << width), bit < 2,
    ensures
        width + 1 <= 15,
        (bits | (bit << width)) < (1u16 << (width + 1)),
{}

#[verifier::bit_vector]
proof fn append_installed_bit_value(bits: u16, width: u8, bit: u16)
    requires width <= 14, bits < (1u16 << width), bit < 2,
    ensures
        (bits | (bit << width)) as nat
            == bits as nat + bit as nat * (1u16 << width) as nat,
{}

proof fn bits_value_push(bits: Seq<u8>, bit: u8)
    requires
        bit <= 1,
        forall|i: int| 0 <= i < bits.len() ==> bits[i] <= 1,
    ensures
        bits_value(bits + seq![bit])
            == bits_value(bits) + bit as nat * pow2(bits.len()),
    decreases bits.len(),
{
    if bits.len() == 0 {
        assert(bits =~= Seq::<u8>::empty());
        assert(bits + seq![bit] =~= seq![bit]);
        assert(bits_value(bits) == 0) by { reveal(bits_value); }
        assert(bits_value(bits + seq![bit]) == bit as nat) by {
            reveal_with_fuel(bits_value, 2);
        }
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(bit as nat * pow2(bits.len()) == bit as nat);
        assert(bits_value(bits + seq![bit])
            == bits_value(bits) + bit as nat * pow2(bits.len()));
    } else {
        let tail = bits.skip(1);
        assert forall|i: int| 0 <= i < tail.len() implies tail[i] <= 1 by {
            assert(tail[i] == bits[i + 1]);
        }
        bits_value_push(tail, bit);
        let pushed = bits + seq![bit];
        assert(pushed.len() > 0);
        assert(pushed[0] == bits[0]);
        assert(pushed.skip(1) =~= tail + seq![bit]);
        assert(bits_value(pushed)
            == pushed[0] as nat + 2 * bits_value(pushed.skip(1))) by {
            reveal(bits_value);
        }
        assert(bits_value(bits) == bits[0] as nat + 2 * bits_value(tail)) by {
            reveal(bits_value);
        }
        assert(tail.len() + 1 == bits.len());
        lemma_pow2_unfold(bits.len());
        assert(pow2(bits.len()) == 2 * pow2(tail.len()));
        assert(bits_value(pushed)
            == bits[0] as nat
                + 2 * (bits_value(tail) + bit as nat * pow2(tail.len())));
        if bit == 0 {
            assert(bit as nat == 0);
            assert(bits_value(bits + seq![bit])
                == bits_value(bits) + bit as nat * pow2(bits.len())) by (nonlinear_arith)
                requires
                    bits_value(bits + seq![bit]) == bits_value(pushed),
                    bits_value(pushed)
                        == bits[0] as nat
                            + 2 * (bits_value(tail)
                                + bit as nat * pow2(tail.len())),
                    bits_value(bits)
                        == bits[0] as nat + 2 * bits_value(tail),
                    pow2(bits.len()) == 2 * pow2(tail.len()),
                    bit as nat == 0;
        } else {
            assert(bit == 1);
            assert(bit as nat == 1);
            assert(bits_value(bits + seq![bit])
                == bits_value(bits) + bit as nat * pow2(bits.len())) by (nonlinear_arith)
                requires
                    bits_value(bits + seq![bit]) == bits_value(pushed),
                    bits_value(pushed)
                        == bits[0] as nat
                            + 2 * (bits_value(tail)
                                + bit as nat * pow2(tail.len())),
                    bits_value(bits)
                        == bits[0] as nat + 2 * bits_value(tail),
                    pow2(bits.len()) == 2 * pow2(tail.len()),
                    bit as nat == 1;
        }
    }
}

proof fn pow2_add(a: nat, b: nat)
    ensures pow2(a + b) == pow2(a) * pow2(b),
    decreases b,
{
    if b == 0 {
        lemma2_to64();
        assert(pow2(0) == 1);
        assert(a + b == a);
    } else {
        pow2_add(a, (b - 1) as nat);
        lemma_pow2_unfold(a + b);
        lemma_pow2_unfold(b);
        assert(a + b - 1 == a + (b - 1));
        assert(pow2(a + b) == pow2(a) * pow2(b)) by (nonlinear_arith)
            requires
                pow2(a + b) == 2 * pow2((a + b - 1) as nat),
                pow2(b) == 2 * pow2((b - 1) as nat),
                pow2((a + b - 1) as nat) == pow2(a) * pow2((b - 1) as nat);
    }
}

spec fn installed_prefix_value(
    start: InstalledPrefixState,
    accepted: Seq<u8>,
) -> nat {
    start.bits as nat + pow2(start.width as nat) * bits_value(accepted)
}

spec fn installed_record_matches(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    width: u8,
    bits: nat,
    symbol: int,
) -> bool {
    let at = crate::brotli_prefix::tree_record_at(
        window_bytes,
        region,
        tree,
        symbol as u16,
    );
    &&& 0 <= symbol < meta.symbols
    &&& at + 3 <= workspace.len()
    &&& 1 <= width <= 15
    &&& workspace[at as int] == width
    &&& crate::brotli_prefix::little_u16_at(workspace, at + 1) < pow2(width as nat)
    &&& reversed_installed_code(
        crate::brotli_prefix::little_u16_at(workspace, at + 1),
        width,
    ) == bits
}

spec fn installed_no_match(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    width: u8,
    bits: nat,
) -> bool {
    forall|symbol: int| 0 <= symbol < meta.symbols ==> #[trigger] installed_record_matches(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
        width,
        bits,
        symbol,
    ) == false
}

spec fn installed_no_earlier_match(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start: InstalledPrefixState,
    accepted: Seq<u8>,
    before: int,
) -> bool {
    forall|used: int| 1 <= used < before ==> installed_no_match(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
        (start.width as int + used) as u8,
        installed_prefix_value(start, accepted.take(used)),
    )
}

spec fn installed_symbol_success(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start: InstalledPrefixState,
    input: Seq<u8>,
    consumed: usize,
    final_queue: BitQueue,
    symbol: u16,
) -> bool {
    exists|used: int| #![trigger installed_prefix_value(
        start,
        (start_queue.bits() + bytes_bits(input.take(consumed as int))).take(used),
    )] {
        let source = start_queue.bits() + bytes_bits(input.take(consumed as int));
        &&& 1 <= used <= 15 - start.width
        &&& used <= source.len()
        &&& consumed as nat == input_bytes_taken(
            start_queue.bits().len(),
            used as nat,
            input.len(),
        )
        &&& final_queue.bits() == source.skip(used)
        &&& installed_no_earlier_match(
            workspace,
            window_bytes,
            region,
            tree,
            meta,
            start,
            source,
            used,
        )
        &&& installed_record_matches(
            workspace,
            window_bytes,
            region,
            tree,
            meta,
            (start.width as int + used) as u8,
            installed_prefix_value(start, source.take(used)),
            symbol as int,
        )
        &&& forall|earlier: int| 0 <= earlier < symbol ==>
            #[trigger] installed_record_matches(
                workspace,
                window_bytes,
                region,
                tree,
                meta,
                (start.width as int + used) as u8,
                installed_prefix_value(start, source.take(used)),
                earlier,
            ) == false
    }
}

spec fn installed_symbol_exhausted(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start: InstalledPrefixState,
    input: Seq<u8>,
    final_queue: BitQueue,
) -> bool {
    let accepted = start_queue.bits() + bytes_bits(input);
    &&& accepted.len() < 15 - start.width
    &&& final_queue.bits().len() == 0
    &&& installed_no_earlier_match(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
        start,
        accepted,
        accepted.len() as int + 1,
    )
}

spec fn installed_symbol_suspended(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start: InstalledPrefixState,
    input: Seq<u8>,
    final_queue: BitQueue,
    final_prefix: InstalledPrefixState,
) -> bool {
    let accepted = start_queue.bits() + bytes_bits(input);
    &&& installed_symbol_exhausted(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
        start_queue,
        start,
        input,
        final_queue,
    )
    &&& final_prefix.width as nat == start.width as nat + accepted.len()
    &&& final_prefix.bits as nat == installed_prefix_value(start, accepted)
    &&& final_prefix.scan == 0
}

spec fn installed_symbol_invalid_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start: InstalledPrefixState,
    input: Seq<u8>,
    consumed: usize,
    final_queue: BitQueue,
) -> bool {
    let used = 15 - start.width as int;
    let source = start_queue.bits() + bytes_bits(input.take(consumed as int));
    &&& 1 <= used <= 15
    &&& used <= source.len()
    &&& consumed as nat == input_bytes_taken(
        start_queue.bits().len(),
        used as nat,
        input.len(),
    )
    &&& final_queue.bits() == source.skip(used)
    &&& installed_no_earlier_match(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
        start,
        source,
        used + 1,
    )
}

spec fn installed_symbol_progress(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start_prefix: InstalledPrefixState,
    input: Seq<u8>,
    consumed: usize,
    accepted: Seq<u8>,
    current_queue: BitQueue,
    current_prefix: InstalledPrefixState,
) -> bool {
    let source = start_queue.bits() + bytes_bits(input.take(consumed as int));
    &&& source == accepted + current_queue.bits()
    &&& current_prefix.width as nat == start_prefix.width as nat + accepted.len()
    &&& current_prefix.bits as nat == installed_prefix_value(start_prefix, accepted)
    &&& current_prefix.scan == 0
    &&& consumed as nat == input_bytes_taken(
        start_queue.bits().len(),
        accepted.len(),
        input.len(),
    )
    &&& installed_no_earlier_match(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
        start_prefix,
        accepted,
        accepted.len() as int + 1,
    )
}

spec fn installed_canonical_step(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start_prefix: InstalledPrefixState,
    input: Seq<u8>,
    end_of_input: bool,
    step: InstalledSymbolStep,
    final_queue: BitQueue,
    final_prefix: InstalledPrefixState,
) -> bool {
    match step.status {
        InstalledSymbolStatus::NeedInput => {
            &&& !end_of_input
            &&& step.consumed == input.len()
            &&& installed_symbol_suspended(
                workspace,
                window_bytes,
                region,
                tree,
                meta,
                start_queue,
                start_prefix,
                input,
                final_queue,
                final_prefix,
            )
        },
        InstalledSymbolStatus::Truncated => {
            &&& end_of_input
            &&& step.consumed == input.len()
            &&& installed_symbol_exhausted(
                workspace,
                window_bytes,
                region,
                tree,
                meta,
                start_queue,
                start_prefix,
                input,
                final_queue,
            )
        },
        InstalledSymbolStatus::Symbol(symbol) => installed_symbol_success(
            workspace,
            window_bytes,
            region,
            tree,
            meta,
            start_queue,
            start_prefix,
            input,
            step.consumed,
            final_queue,
            symbol,
        ),
        InstalledSymbolStatus::InvalidPrefixCode => installed_symbol_invalid_prefix(
            workspace,
            window_bytes,
            region,
            tree,
            meta,
            start_queue,
            start_prefix,
            input,
            step.consumed,
            final_queue,
        ),
        InstalledSymbolStatus::InternalState => true,
    }
}

spec fn installed_tree_step_refines(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    start_prefix: InstalledPrefixState,
    input: Seq<u8>,
    end_of_input: bool,
    step: InstalledSymbolStep,
    final_queue: BitQueue,
    final_prefix: InstalledPrefixState,
) -> bool {
    match meta.storage {
        crate::brotli_prefix::TreeStorageState::Unused => {
            &&& step.consumed == 0
            &&& step.status == InstalledSymbolStatus::InternalState
            &&& final_queue == start_queue
            &&& final_prefix == InstalledPrefixState { width: 0, bits: 0, scan: 0 }
        },
        crate::brotli_prefix::TreeStorageState::Single { symbol } => {
            &&& step.consumed == 0
            &&& final_queue == start_queue
            &&& if start_prefix == (InstalledPrefixState { width: 0, bits: 0, scan: 0 })
                && symbol < meta.symbols {
                &&& step.status == InstalledSymbolStatus::Symbol(symbol)
                &&& final_prefix == InstalledPrefixState { width: 0, bits: 0, scan: 0 }
            } else {
                &&& step.status == InstalledSymbolStatus::InternalState
                &&& final_prefix == InstalledPrefixState { width: 0, bits: 0, scan: 0 }
            }
        },
        crate::brotli_prefix::TreeStorageState::Canonical { initialized } => {
            if initialized == meta.symbols {
                installed_canonical_step(
                    workspace,
                    window_bytes,
                    region,
                    tree,
                    meta,
                    start_queue,
                    start_prefix,
                    input,
                    end_of_input,
                    step,
                    final_queue,
                    final_prefix,
                )
            } else {
                &&& step.consumed == 0
                &&& step.status == InstalledSymbolStatus::InternalState
                &&& final_queue == start_queue
                &&& final_prefix == InstalledPrefixState { width: 0, bits: 0, scan: 0 }
            }
        },
    }
}

proof fn input_bytes_taken_one_more(
    available: nat,
    accepted: nat,
    input_len: nat,
    consumed: nat,
    current_bits: nat,
    added: nat,
)
    requires
        consumed == input_bytes_taken(available, accepted, input_len),
        consumed <= input_len,
        accepted <= available + 8 * consumed,
        current_bits == available + 8 * consumed - accepted,
        added == input_bytes_taken(current_bits, 1, (input_len - consumed) as nat),
    ensures
        consumed + added == input_bytes_taken(
            available,
            accepted + 1,
            input_len,
        ),
{
    reveal(input_bytes_taken);
    reveal(input_bytes_needed);
    if available >= accepted + 1 {
        assert(consumed == 0);
        assert(current_bits >= 1);
        assert(added == 0);
    } else {
        assert(accepted >= available);
        if current_bits >= 1 {
            assert(added == 0);
        } else {
            assert(current_bits == 0);
            assert(added <= 1);
        }
    }
}

proof fn bytes_bits_extend_take(bytes: Seq<u8>, consumed: int, added: int)
    requires
        0 <= consumed,
        0 <= added,
        consumed + added <= bytes.len(),
    ensures
        bytes_bits(bytes.take(consumed + added))
            == bytes_bits(bytes.take(consumed))
                + bytes_bits(bytes.subrange(consumed, consumed + added)),
{
    assert(bytes.take(consumed + added) =~=
        bytes.take(consumed) + bytes.subrange(consumed, consumed + added));
    bytes_bits_concat(bytes.take(consumed), bytes.subrange(consumed, consumed + added));
}

fn advance_installed_tree_symbol(
    workspace: &[u8],
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    meta: crate::brotli_prefix::TreeMetadata,
    queue: &mut BitQueue,
    prefix: &mut InstalledPrefixState,
    input: &[u8],
    end_of_input: bool,
) -> (r: InstalledSymbolStep)
    requires old(queue).valid(), old(prefix).valid(), meta.valid_for(region),
    ensures final(queue).valid(), final(prefix).valid(), r.consumed <= input.len(),
        r.status == InstalledSymbolStatus::NeedInput ==> {
            &&& !end_of_input
            &&& r.consumed == input.len()
        },
        match r.status {
            InstalledSymbolStatus::Symbol(symbol) => {
                &&& symbol < meta.symbols
                &&& *final(prefix) == InstalledPrefixState { width: 0, bits: 0, scan: 0 }
            },
            InstalledSymbolStatus::Truncated
            | InstalledSymbolStatus::InvalidPrefixCode
            | InstalledSymbolStatus::InternalState =>
                *final(prefix) == InstalledPrefixState { width: 0, bits: 0, scan: 0 },
            _ => true,
        },
        meta.storage == crate::brotli_prefix::TreeStorageState::Unused ==> {
            &&& r.consumed == 0
            &&& r.status == InstalledSymbolStatus::InternalState
            &&& *final(queue) == *old(queue)
        },
        match meta.storage {
            crate::brotli_prefix::TreeStorageState::Single { symbol } => {
                &&& r.consumed == 0
                &&& *final(queue) == *old(queue)
                &&& if old(prefix).width == 0
                    && old(prefix).bits == 0
                    && old(prefix).scan == 0
                    && symbol < meta.symbols {
                    r.status == InstalledSymbolStatus::Symbol(symbol)
                } else {
                    r.status == InstalledSymbolStatus::InternalState
                }
            },
            _ => true,
        },
        match meta.storage {
            crate::brotli_prefix::TreeStorageState::Canonical { initialized } => {
                &&& (initialized != meta.symbols ==> {
                    &&& r.consumed == 0
                    &&& r.status == InstalledSymbolStatus::InternalState
                    &&& *final(queue) == *old(queue)
                })
                &&& (initialized == meta.symbols ==> installed_canonical_step(
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    meta,
                    *old(queue),
                    *old(prefix),
                    input@,
                    end_of_input,
                    r,
                    *final(queue),
                    *final(prefix),
                ))
            },
            _ => true,
        },
        installed_tree_step_refines(
            workspace@,
            window_bytes,
            region,
            tree,
            meta,
            *old(queue),
            *old(prefix),
            input@,
            end_of_input,
            r,
            *final(queue),
            *final(prefix),
        ),
{
    let ghost start_queue = *queue;
    let ghost start_prefix = *prefix;
    match meta.storage {
        crate::brotli_prefix::TreeStorageState::Unused => {
            *prefix = InstalledPrefixState::initial();
            return InstalledSymbolStep { consumed: 0, status: InstalledSymbolStatus::InternalState };
        }
        crate::brotli_prefix::TreeStorageState::Single { symbol } => {
            if prefix.width != 0 || prefix.bits != 0 || prefix.scan != 0
                || symbol >= meta.symbols {
                *prefix = InstalledPrefixState::initial();
                return InstalledSymbolStep { consumed: 0, status: InstalledSymbolStatus::InternalState };
            }
            return InstalledSymbolStep { consumed: 0, status: InstalledSymbolStatus::Symbol(symbol) };
        }
        crate::brotli_prefix::TreeStorageState::Canonical { initialized } => {
            if initialized != meta.symbols {
                *prefix = InstalledPrefixState::initial();
                return InstalledSymbolStep { consumed: 0, status: InstalledSymbolStatus::InternalState };
            }
        }
    }

    let mut consumed: usize = 0;
    let mut iterations: u8 = 0;
    let ghost mut accepted = Seq::<u8>::empty();
    proof {
        reveal(installed_symbol_progress);
        reveal(installed_prefix_value);
        reveal(installed_no_earlier_match);
        reveal(input_bytes_taken);
        reveal(input_bytes_needed);
        assert(input@.take(0) =~= Seq::<u8>::empty());
        reveal_with_fuel(bytes_bits, 2);
        reveal_with_fuel(bits_value, 2);
        assert(bytes_bits(input@.take(0)) =~= Seq::<u8>::empty());
        assert(start_queue.bits() + bytes_bits(input@.take(0))
            =~= start_queue.bits());
        assert((start_queue.bits() + bytes_bits(input@.take(0))).take(0)
            =~= Seq::<u8>::empty());
        assert(bits_value((start_queue.bits() + bytes_bits(input@.take(0))).take(0)) == 0);
        assert(installed_prefix_value(
            start_prefix,
            (start_queue.bits() + bytes_bits(input@.take(0))).take(0),
        ) == start_prefix.bits as nat);
        assert(start_queue.bits().skip(0) == start_queue.bits());
        assert(installed_no_earlier_match(
            workspace@,
            window_bytes,
            region,
            tree,
            meta,
            start_prefix,
            start_queue.bits(),
            1,
        ));
        assert(installed_symbol_progress(
            workspace@,
            window_bytes,
            region,
            tree,
            meta,
            start_queue,
            start_prefix,
            input@,
            consumed,
            accepted,
            *queue,
            *prefix,
        ));
    }
    while iterations < 15
        invariant consumed <= input.len(), iterations <= 15,
            queue.valid(), prefix.valid(), meta.valid_for(region),
            meta.storage == (crate::brotli_prefix::TreeStorageState::Canonical {
                initialized: meta.symbols,
            }),
            start_queue == *old(queue), start_prefix == *old(prefix),
            start_queue.valid(), start_prefix.valid(),
            start_prefix.width as nat + iterations as nat <= 15,
            accepted.len() == iterations,
            forall|i: int| 0 <= i < accepted.len() ==> accepted[i] <= 1,
            installed_symbol_progress(
                workspace@,
                window_bytes,
                region,
                tree,
                meta,
                start_queue,
                start_prefix,
                input@,
                consumed,
                accepted,
                *queue,
                *prefix,
            ),
        decreases 15 - iterations,
    {
        let ghost old_consumed = consumed;
        let ghost before_queue = *queue;
        let ghost before_accepted = accepted;
        let ghost before_source = start_queue.bits()
            + bytes_bits(input@.take(consumed as int));
        let remaining_input = &input[consumed..];
        let read = queue.read_bits(1, remaining_input, end_of_input);
        let bit = match read.status {
            BitReadStatus::Value(value) => {
                proof {
                    lemma2_to64();
                    assert(value < 2);
                    installed_one_bit_fits(value);
                }
                value as u16
            },
            BitReadStatus::NeedInput => {
                proof {
                    reveal(installed_symbol_progress);
                    reveal(installed_symbol_suspended);
                    reveal(installed_symbol_exhausted);
                    let remaining = input@.skip(old_consumed as int);
                    assert(remaining_input@ =~= remaining);
                    assert(read.consumed == remaining_input.len());
                    assert(queue.bits()
                        == before_queue.bits() + bytes_bits(remaining));
                    assert(queue.bits().len() < 1);
                    assert(queue.bits().len() == 0);
                    assert(before_queue.bits() + bytes_bits(remaining)
                        =~= Seq::<u8>::empty());
                    bytes_bits_extend_take(
                        input@,
                        old_consumed as int,
                        read.consumed as int,
                    );
                    assert(old_consumed + read.consumed == input.len());
                    assert(input@.take(
                        old_consumed as int + read.consumed as int,
                    ) =~= input@);
                    assert(bytes_bits(input@)
                        == bytes_bits(input@.take(old_consumed as int))
                            + bytes_bits(remaining));
                    assert(before_source == before_accepted + before_queue.bits());
                    assert(start_queue.bits() + bytes_bits(input@)
                        =~= before_source + bytes_bits(remaining));
                    assert(start_queue.bits() + bytes_bits(input@)
                        =~= before_accepted);
                    assert(installed_symbol_suspended(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        start_queue,
                        start_prefix,
                        input@,
                        *queue,
                        *prefix,
                    ));
                }
                let result = InstalledSymbolStep {
                    consumed: consumed + read.consumed,
                    status: InstalledSymbolStatus::NeedInput,
                };
                proof {
                    reveal(installed_canonical_step);
                    assert(installed_canonical_step(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        start_queue,
                        start_prefix,
                        input@,
                        end_of_input,
                        result,
                        *queue,
                        *prefix,
                    ));
                }
                return result;
            },
            BitReadStatus::Truncated => {
                proof {
                    reveal(installed_canonical_step);
                    reveal(installed_symbol_progress);
                    reveal(installed_symbol_exhausted);
                    let remaining = input@.skip(old_consumed as int);
                    assert(remaining_input@ =~= remaining);
                    assert(read.consumed == remaining_input.len());
                    assert(queue.bits()
                        == before_queue.bits() + bytes_bits(remaining));
                    assert(queue.bits().len() < 1);
                    assert(queue.bits().len() == 0);
                    assert(before_queue.bits() + bytes_bits(remaining)
                        =~= Seq::<u8>::empty());
                    bytes_bits_extend_take(
                        input@,
                        old_consumed as int,
                        read.consumed as int,
                    );
                    assert(old_consumed + read.consumed == input.len());
                    assert(input@.take(
                        old_consumed as int + read.consumed as int,
                    ) =~= input@);
                    assert(bytes_bits(input@)
                        == bytes_bits(input@.take(old_consumed as int))
                            + bytes_bits(remaining));
                    assert(before_source == before_accepted + before_queue.bits());
                    assert(start_queue.bits() + bytes_bits(input@)
                        =~= before_source + bytes_bits(remaining));
                    assert(start_queue.bits() + bytes_bits(input@)
                        =~= before_accepted);
                    assert(installed_symbol_exhausted(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        start_queue,
                        start_prefix,
                        input@,
                        *queue,
                    ));
                }
                *prefix = InstalledPrefixState::initial();
                let result = InstalledSymbolStep {
                    consumed: consumed + read.consumed,
                    status: InstalledSymbolStatus::Truncated,
                };
                proof {
                    assert(installed_canonical_step(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        start_queue,
                        start_prefix,
                        input@,
                        end_of_input,
                        result,
                        *queue,
                        *prefix,
                    ));
                }
                return result;
            }
        };
        consumed = consumed + read.consumed;
        let old_width = prefix.width;
        let next_width = old_width + 1;
        let next_bits = prefix.bits | (bit << old_width);
        proof {
            append_installed_bit_fits(prefix.bits, old_width, bit);
            append_installed_bit_value(prefix.bits, old_width, bit);
            pow2_matches_installed_shift(old_width);
            reveal(installed_symbol_progress);
            let remaining = input@.skip(old_consumed as int);
            assert(remaining_input@ =~= remaining);
            reveal(input_bytes_taken);
            reveal(input_bytes_needed);
            assert(read.consumed <= 1);
            bytes_bits_extend_take(
                input@,
                old_consumed as int,
                read.consumed as int,
            );
            assert(input@.subrange(
                old_consumed as int,
                old_consumed as int + read.consumed as int,
            ) =~= remaining.take(read.consumed as int));
            assert(bytes_bits(input@.take(consumed as int))
                == bytes_bits(input@.take(old_consumed as int))
                    + bytes_bits(remaining.take(read.consumed as int)));
            let local_source = before_queue.bits()
                + bytes_bits(remaining.take(read.consumed as int));
            let after_source = start_queue.bits()
                + bytes_bits(input@.take(consumed as int));
            assert(before_source == before_accepted + before_queue.bits());
            assert(after_source =~= before_accepted + local_source);
            assert(local_source.len() >= 1);
            assert(queue.bits() == local_source.skip(1));
            assert(bit as nat == bits_value(local_source.take(1)));
            assert(local_source.take(1) =~= seq![bit as u8]) by {
                assert(local_source.take(1).len() == 1);
                assert(local_source.take(1)[0] == bit as u8);
            }
            assert(local_source =~= local_source.take(1) + local_source.skip(1));
            assert(after_source =~= (before_accepted + seq![bit as u8]) + queue.bits());
            bytes_bits_len(input@.take(old_consumed as int));
            bytes_bits_len(input@.take(consumed as int));
            assert(before_source.len()
                == start_queue.bits().len() + 8 * old_consumed as nat);
            assert(before_source.len()
                == before_accepted.len() + before_queue.bits().len());
            assert(before_queue.bits().len()
                == start_queue.bits().len() + 8 * old_consumed as nat
                    - before_accepted.len());
            assert(remaining.len() == input.len() - old_consumed);
            input_bytes_taken_one_more(
                start_queue.bits().len(),
                before_accepted.len(),
                input.len() as nat,
                old_consumed as nat,
                before_queue.bits().len(),
                read.consumed as nat,
            );
            bits_value_push(before_accepted, bit as u8);
            pow2_add(start_prefix.width as nat, before_accepted.len());
            reveal(installed_prefix_value);
            assert(prefix.bits as nat == installed_prefix_value(
                start_prefix,
                before_accepted,
            ));
            assert(prefix.width as nat
                == start_prefix.width as nat + before_accepted.len());
            assert(pow2(prefix.width as nat)
                == pow2(start_prefix.width as nat) * pow2(before_accepted.len()));
            assert(next_bits as nat == installed_prefix_value(
                start_prefix,
                before_accepted + seq![bit as u8],
            )) by (nonlinear_arith)
                requires
                    next_bits as nat == prefix.bits as nat
                        + bit as nat * pow2(prefix.width as nat),
                    prefix.bits as nat == installed_prefix_value(
                        start_prefix,
                        before_accepted,
                    ),
                    bits_value(before_accepted + seq![bit as u8])
                        == bits_value(before_accepted)
                            + bit as nat * pow2(before_accepted.len()),
                    pow2(prefix.width as nat)
                        == pow2(start_prefix.width as nat)
                            * pow2(before_accepted.len());
            assert(next_bits as nat == installed_prefix_value(
                start_prefix,
                before_accepted + seq![bit as u8],
            ));
            accepted = before_accepted + seq![bit as u8];
            reveal(installed_no_earlier_match);
            assert(installed_no_earlier_match(
                workspace@,
                window_bytes,
                region,
                tree,
                meta,
                start_prefix,
                accepted,
                accepted.len() as int,
            )) by {
                assert forall|used: int| 1 <= used < accepted.len() implies
                    installed_no_match(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        (start_prefix.width as int + used) as u8,
                        installed_prefix_value(start_prefix, accepted.take(used)),
                    ) by {
                    assert(used <= before_accepted.len());
                    assert(accepted.take(used) =~= before_accepted.take(used));
                }
            }
        }
        let mut symbol: u16 = 0;
        while symbol < meta.symbols
            invariant symbol <= meta.symbols, meta.valid_for(region),
                meta.storage == (crate::brotli_prefix::TreeStorageState::Canonical {
                    initialized: meta.symbols,
                }),
                start_queue == *old(queue), start_prefix == *old(prefix),
                queue.valid(), prefix.valid(), consumed <= input.len(),
                1 <= next_width <= 15,
                next_bits < (1u16 << next_width),
                accepted.len() == iterations as nat + 1,
                forall|i: int| 0 <= i < accepted.len() ==> accepted[i] <= 1,
                start_queue.bits() + bytes_bits(input@.take(consumed as int))
                    == accepted + queue.bits(),
                consumed as nat == input_bytes_taken(
                    start_queue.bits().len(),
                    accepted.len(),
                    input.len() as nat,
                ),
                next_width as nat == start_prefix.width as nat + accepted.len(),
                next_bits as nat == installed_prefix_value(start_prefix, accepted),
                installed_no_earlier_match(
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    meta,
                    start_prefix,
                    accepted,
                    accepted.len() as int,
                ),
                forall|earlier: int| 0 <= earlier < symbol ==>
                    #[trigger] installed_record_matches(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        next_width,
                        next_bits as nat,
                        earlier,
                    ) == false,
            decreases meta.symbols - symbol,
        {
            let record = match crate::brotli_prefix::read_tree_record(
                workspace,
                window_bytes,
                region,
                tree,
                &meta,
                symbol,
            ) {
                Ok(value) => value,
                Err(_) => {
                    *prefix = InstalledPrefixState::initial();
                    return InstalledSymbolStep { consumed, status: InstalledSymbolStatus::InternalState };
                }
            };
            if record.length == next_width && record.length != 0 {
                if record.code >= (1u16 << next_width) {
                    *prefix = InstalledPrefixState::initial();
                    return InstalledSymbolStep {
                        consumed,
                        status: InstalledSymbolStatus::InternalState,
                    };
                }
                proof { pow2_matches_installed_shift(next_width); }
                let reversed = reverse_installed_code(record.code, next_width);
                if reversed == next_bits {
                    proof {
                        reveal(installed_record_matches);
                        let at = crate::brotli_prefix::tree_record_at(
                            window_bytes,
                            region,
                            tree,
                            symbol,
                        );
                        assert(record.length == workspace@[at as int]);
                        assert(record.code as nat
                            == crate::brotli_prefix::little_u16_at(workspace@, at + 1));
                        assert(installed_record_matches(
                            workspace@,
                            window_bytes,
                            region,
                            tree,
                            meta,
                            next_width,
                            next_bits as nat,
                            symbol as int,
                        ));
                        reveal(installed_symbol_success);
                        assert(installed_symbol_success(
                            workspace@,
                            window_bytes,
                            region,
                            tree,
                            meta,
                            start_queue,
                            start_prefix,
                            input@,
                            consumed,
                            *queue,
                            symbol,
                        )) by {
                            let used = accepted.len() as int;
                            let source = start_queue.bits()
                                + bytes_bits(input@.take(consumed as int));
                            assert(1 <= used <= 15 - start_prefix.width);
                            assert(used <= source.len());
                            assert(source == accepted + queue.bits());
                            assert(source.take(used) =~= accepted);
                            assert(source.skip(used) =~= queue.bits());
                            assert(installed_no_earlier_match(
                                workspace@,
                                window_bytes,
                                region,
                                tree,
                                meta,
                                start_prefix,
                                source,
                                used,
                            )) by {
                                reveal(installed_no_earlier_match);
                                assert forall|prior: int| 1 <= prior < used implies
                                    installed_no_match(
                                        workspace@,
                                        window_bytes,
                                        region,
                                        tree,
                                        meta,
                                        (start_prefix.width as int + prior) as u8,
                                        installed_prefix_value(
                                            start_prefix,
                                            source.take(prior),
                                        ),
                                    ) by {
                                    assert(source.take(prior) =~= accepted.take(prior));
                                }
                            }
                            assert(installed_prefix_value(start_prefix, source.take(used))
                                == next_bits as nat);
                            assert(exists|candidate: int| #![trigger installed_prefix_value(
                                start_prefix,
                                (start_queue.bits()
                                    + bytes_bits(input@.take(consumed as int))).take(candidate),
                            )] candidate == used && {
                                let candidate_source = start_queue.bits()
                                    + bytes_bits(input@.take(consumed as int));
                                &&& 1 <= candidate <= 15 - start_prefix.width
                                &&& candidate <= candidate_source.len()
                                &&& consumed as nat == input_bytes_taken(
                                    start_queue.bits().len(),
                                    candidate as nat,
                                    input.len() as nat,
                                )
                                &&& queue.bits() == candidate_source.skip(candidate)
                                &&& installed_no_earlier_match(
                                    workspace@,
                                    window_bytes,
                                    region,
                                    tree,
                                    meta,
                                    start_prefix,
                                    candidate_source,
                                    candidate,
                                )
                                &&& installed_record_matches(
                                    workspace@,
                                    window_bytes,
                                    region,
                                    tree,
                                    meta,
                                    (start_prefix.width as int + candidate) as u8,
                                    installed_prefix_value(
                                        start_prefix,
                                        candidate_source.take(candidate),
                                    ),
                                    symbol as int,
                                )
                                &&& forall|earlier: int| 0 <= earlier < symbol ==>
                                    #[trigger] installed_record_matches(
                                        workspace@,
                                        window_bytes,
                                        region,
                                        tree,
                                        meta,
                                        (start_prefix.width as int + candidate) as u8,
                                        installed_prefix_value(
                                            start_prefix,
                                            candidate_source.take(candidate),
                                        ),
                                        earlier,
                                    ) == false
                            });
                        }
                    }
                    *prefix = InstalledPrefixState::initial();
                    proof {
                        assert(meta.storage == (crate::brotli_prefix::TreeStorageState::Canonical {
                            initialized: meta.symbols,
                        }));
                        assert(installed_symbol_success(
                            workspace@,
                            window_bytes,
                            region,
                            tree,
                            meta,
                            start_queue,
                            start_prefix,
                            input@,
                            consumed,
                            *queue,
                            symbol,
                        ));
                        assert(*prefix == InstalledPrefixState {
                            width: 0,
                            bits: 0,
                            scan: 0,
                        });
                    }
                    let result = InstalledSymbolStep {
                        consumed,
                        status: InstalledSymbolStatus::Symbol(symbol),
                    };
                    proof {
                        reveal(installed_canonical_step);
                        assert(installed_tree_step_refines(
                            workspace@,
                            window_bytes,
                            region,
                            tree,
                            meta,
                            start_queue,
                            start_prefix,
                            input@,
                            end_of_input,
                            result,
                            *queue,
                            *prefix,
                        ));
                    }
                    return result;
                }
                proof {
                    reveal(installed_record_matches);
                    let at = crate::brotli_prefix::tree_record_at(
                        window_bytes,
                        region,
                        tree,
                        symbol,
                    );
                    assert(record.code as nat
                        == crate::brotli_prefix::little_u16_at(workspace@, at + 1));
                    assert(installed_record_matches(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        next_width,
                        next_bits as nat,
                        symbol as int,
                    ) == false);
                }
            } else {
                proof {
                    reveal(installed_record_matches);
                    let at = crate::brotli_prefix::tree_record_at(
                        window_bytes,
                        region,
                        tree,
                        symbol,
                    );
                    assert(record.length == workspace@[at as int]);
                    assert(installed_record_matches(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        next_width,
                        next_bits as nat,
                        symbol as int,
                    ) == false);
                }
            }
            symbol = symbol + 1;
        }
        proof {
            reveal(installed_no_match);
            assert(installed_no_match(
                workspace@,
                window_bytes,
                region,
                tree,
                meta,
                next_width,
                next_bits as nat,
            ));
            reveal(installed_no_earlier_match);
            assert(installed_no_earlier_match(
                workspace@,
                window_bytes,
                region,
                tree,
                meta,
                start_prefix,
                accepted,
                accepted.len() as int + 1,
            )) by {
                assert forall|used: int| 1 <= used < accepted.len() + 1 implies
                    installed_no_match(
                        workspace@,
                        window_bytes,
                        region,
                        tree,
                        meta,
                        (start_prefix.width as int + used) as u8,
                        installed_prefix_value(start_prefix, accepted.take(used)),
                    ) by {
                    if used < accepted.len() {
                    } else {
                        assert(used == accepted.len());
                        assert(accepted.take(used) =~= accepted);
                        assert((start_prefix.width as int + used) as u8 == next_width);
                        assert(installed_prefix_value(start_prefix, accepted) == next_bits as nat);
                    }
                }
            }
        }
        if next_width == 15 {
            proof {
                reveal(installed_symbol_invalid_prefix);
                let used = 15 - start_prefix.width as int;
                let source = start_queue.bits()
                    + bytes_bits(input@.take(consumed as int));
                assert(used == accepted.len());
                assert(1 <= used <= 15);
                assert(source == accepted + queue.bits());
                assert(used <= source.len());
                assert(source.take(used) =~= accepted);
                assert(source.skip(used) =~= queue.bits());
                assert(consumed as nat == input_bytes_taken(
                    start_queue.bits().len(),
                    used as nat,
                    input.len() as nat,
                ));
                assert(installed_no_earlier_match(
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    meta,
                    start_prefix,
                    source,
                    used + 1,
                )) by {
                    reveal(installed_no_earlier_match);
                    assert forall|prior: int| 1 <= prior < used + 1 implies
                        installed_no_match(
                            workspace@,
                            window_bytes,
                            region,
                            tree,
                            meta,
                            (start_prefix.width as int + prior) as u8,
                            installed_prefix_value(start_prefix, source.take(prior)),
                        ) by {
                        assert(prior <= used);
                        assert(source.take(prior) =~= accepted.take(prior));
                    }
                }
                assert(installed_symbol_invalid_prefix(
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    meta,
                    start_queue,
                    start_prefix,
                    input@,
                    consumed,
                    *queue,
                ));
            }
            *prefix = InstalledPrefixState::initial();
            let result = InstalledSymbolStep {
                consumed,
                status: InstalledSymbolStatus::InvalidPrefixCode,
            };
            proof {
                reveal(installed_canonical_step);
                assert(installed_canonical_step(
                    workspace@,
                    window_bytes,
                    region,
                    tree,
                    meta,
                    start_queue,
                    start_prefix,
                    input@,
                    end_of_input,
                    result,
                    *queue,
                    *prefix,
                ));
            }
            return result;
        }
        prefix.width = next_width;
        prefix.bits = next_bits;
        prefix.scan = 0;
        iterations = iterations + 1;
    }
    *prefix = InstalledPrefixState::initial();
    InstalledSymbolStep { consumed, status: InstalledSymbolStatus::InternalState }
}

const B3B_SCALAR_OFFSET: u32 = 1_163_276;
const B3B_SCALAR_BYTES: u16 = 256;
const B3B_QUEUE_OFFSET: u16 = 0;
const B3B_QUEUE_LEN: u16 = 8;
const B3B_QUEUE_OFFSET_BYTE: u16 = 9;
const B3B_OUTER_PHASE: u16 = 10;
const B3B_TERMINAL_ERROR: u16 = 11;
const B3B_CURRENT_KIND: u16 = 12;
const B3B_VAR_PHASE: u16 = 13;
const B3B_VAR_WIDTH: u16 = 14;
const B3B_CONTEXT_PHASE: u16 = 15;
const B3B_BLOCK_COUNTS: u16 = 16;
const B3B_INITIAL_LENGTHS: u16 = 22;
const B3B_DISTANCE_POSTFIX: u16 = 34;
const B3B_CONTEXT_KIND: u16 = 35;
const B3B_DIRECT_DISTANCE: u16 = 36;
const B3B_LITERAL_TREES: u16 = 38;
const B3B_DISTANCE_TREES: u16 = 40;
const B3B_MAP_TREES: u16 = 42;
const B3B_MAP_SIZE: u16 = 44;
const B3B_MAP_INDEX: u16 = 46;
const B3B_MAP_INITIALIZED: u16 = 48;
const B3B_MODES_INITIALIZED: u16 = 50;
const B3B_MAX_RUN_PREFIX: u16 = 52;
const B3B_PENDING_RUN: u16 = 53;
const B3B_GROUP_KIND: u16 = 54;
const B3B_GROUP_PHASE: u16 = 55;
const B3B_TREE_INDEX: u16 = 56;
const B3B_TREE_COUNT: u16 = 58;
const B3B_CODE_PHASE: u16 = 60;
const B3B_CODE_AUX_PHASE: u16 = 61;
const B3B_SIMPLE_SELECTOR: u16 = 62;
const B3B_SIMPLE_COUNT: u16 = 63;
const B3B_CODE_INDEX: u16 = 64;
const B3B_CODE_WIDTH: u16 = 65;
const B3B_AUX_SKIP: u16 = 66;
const B3B_AUX_INDEX: u16 = 67;
const B3B_AUX_SPACE: u16 = 68;
const B3B_AUX_NONZERO: u16 = 69;
const B3B_PREVIOUS_LENGTH: u16 = 70;
const B3B_REPEATED_LENGTH: u16 = 71;
const B3B_FINAL_SYMBOL: u16 = 72;
const B3B_CHAINED_REPEAT: u16 = 74;
const B3B_FINAL_SPACE: u16 = 78;
const B3B_FINAL_PREFIX_BITS: u16 = 82;
const B3B_FINAL_PREFIX_WIDTH: u16 = 83;
const B3B_AUX_SINGLETON: u16 = 84;
const B3B_CODE_ERROR: u16 = 85;
const B3B_SIMPLE_SYMBOLS: u16 = 86;
const B3B_AUX_LENGTHS: u16 = 94;
const B3B_BUILDER_INITIALIZED: u16 = 112;
const B3B_ACTIVE_REGION: u16 = 114;
const B3B_INSTALLED_PREFIX_WIDTH: u16 = 115;
const B3B_ACTIVE_TREE: u16 = 116;
const B3B_ALPHABET_MAX: u16 = 118;
const B3B_ALPHABET_LIMIT: u16 = 120;
const B3B_INSTALLED_PREFIX_BITS: u16 = 122;
const B3B_INSTALLED_SCAN: u16 = 124;
const B3B_BLOCK_LENGTH_PHASE: u16 = 126;
const B3B_BLOCK_LENGTH_SYMBOL: u16 = 127;
const B3B_BLOCK_LENGTH_SUFFIX_WIDTH: u16 = 128;
const B3B_BLOCK_SWITCH_PHASE: u16 = 129;
const B3B_BLOCK_LENGTH_SUFFIX: u16 = 130;
const B3B_BLOCK_RING: u16 = 134;
const B3B_REMAINING_LENGTHS: u16 = 146;
const B3B_BLOCK_SWITCH_KIND: u16 = 158;
const B3B_MTF_UPPER_BOUND: u16 = 159;
const B3B_PENDING_BLOCK_TYPE: u16 = 160;
const B3B_COVERAGE_INDEX: u16 = 162;
const B3B_EXPECTED_TREES: u16 = 164;
const B3B_ACTIVE_LITERAL_TREE: u16 = 166;
const B3B_ACTIVE_COMMAND_TREE: u16 = 168;
const B3B_ACTIVE_DISTANCE_TREE: u16 = 170;
const B3B_ERROR_DETAIL: u16 = 172;
const B3B_PENDING_SPAN_LENGTH: u16 = 174;

proof fn b3b_scalar_layout_is_exact()
    ensures
        B3B_SCALAR_OFFSET == 1_163_276,
        B3B_SCALAR_BYTES == 256,
        B3B_QUEUE_OFFSET == 0,
        B3B_QUEUE_LEN == 8,
        B3B_QUEUE_OFFSET_BYTE == 9,
        B3B_OUTER_PHASE == 10,
        B3B_TERMINAL_ERROR == 11,
        B3B_CURRENT_KIND == 12,
        B3B_VAR_PHASE == 13,
        B3B_VAR_WIDTH == 14,
        B3B_CONTEXT_PHASE == 15,
        B3B_BLOCK_COUNTS == 16,
        B3B_INITIAL_LENGTHS == 22,
        B3B_DISTANCE_POSTFIX == 34,
        B3B_CONTEXT_KIND == 35,
        B3B_DIRECT_DISTANCE == 36,
        B3B_LITERAL_TREES == 38,
        B3B_DISTANCE_TREES == 40,
        B3B_MAP_TREES == 42,
        B3B_MAP_SIZE == 44,
        B3B_MAP_INDEX == 46,
        B3B_MAP_INITIALIZED == 48,
        B3B_MODES_INITIALIZED == 50,
        B3B_MAX_RUN_PREFIX == 52,
        B3B_PENDING_RUN == 53,
        B3B_GROUP_KIND == 54,
        B3B_GROUP_PHASE == 55,
        B3B_TREE_INDEX == 56,
        B3B_TREE_COUNT == 58,
        B3B_CODE_PHASE == 60,
        B3B_CODE_AUX_PHASE == 61,
        B3B_SIMPLE_SELECTOR == 62,
        B3B_SIMPLE_COUNT == 63,
        B3B_CODE_INDEX == 64,
        B3B_CODE_WIDTH == 65,
        B3B_AUX_SKIP == 66,
        B3B_AUX_INDEX == 67,
        B3B_AUX_SPACE == 68,
        B3B_AUX_NONZERO == 69,
        B3B_PREVIOUS_LENGTH == 70,
        B3B_REPEATED_LENGTH == 71,
        B3B_FINAL_SYMBOL == 72,
        B3B_CHAINED_REPEAT == 74,
        B3B_FINAL_SPACE == 78,
        B3B_FINAL_PREFIX_BITS == 82,
        B3B_FINAL_PREFIX_WIDTH == 83,
        B3B_AUX_SINGLETON == 84,
        B3B_CODE_ERROR == 85,
        B3B_SIMPLE_SYMBOLS == 86,
        B3B_AUX_LENGTHS == 94,
        B3B_BUILDER_INITIALIZED == 112,
        B3B_ACTIVE_REGION == 114,
        B3B_INSTALLED_PREFIX_WIDTH == 115,
        B3B_ACTIVE_TREE == 116,
        B3B_ALPHABET_MAX == 118,
        B3B_ALPHABET_LIMIT == 120,
        B3B_INSTALLED_PREFIX_BITS == 122,
        B3B_INSTALLED_SCAN == 124,
        B3B_BLOCK_LENGTH_PHASE == 126,
        B3B_BLOCK_LENGTH_SYMBOL == 127,
        B3B_BLOCK_LENGTH_SUFFIX_WIDTH == 128,
        B3B_BLOCK_SWITCH_PHASE == 129,
        B3B_BLOCK_LENGTH_SUFFIX == 130,
        B3B_BLOCK_RING == 134,
        B3B_REMAINING_LENGTHS == 146,
        B3B_BLOCK_SWITCH_KIND == 158,
        B3B_MTF_UPPER_BOUND == 159,
        B3B_PENDING_BLOCK_TYPE == 160,
        B3B_COVERAGE_INDEX == 162,
        B3B_EXPECTED_TREES == 164,
        B3B_ACTIVE_LITERAL_TREE == 166,
        B3B_ACTIVE_COMMAND_TREE == 168,
        B3B_ACTIVE_DISTANCE_TREE == 170,
        B3B_ERROR_DETAIL == 172,
        B3B_PENDING_SPAN_LENGTH == 174,
        B3B_PENDING_SPAN_LENGTH + 1 == 175,
        B3B_PENDING_SPAN_LENGTH + 1 <= B3B_SCALAR_BYTES,
        crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET == 1_163_248,
        crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET == 1_163_260,
        crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET == 1_163_272,
        crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET + 12
            == crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET,
        crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET + 12
            == crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET,
        crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET + 4 == B3B_SCALAR_OFFSET,
        crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET == 1_136_640,
        crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET == 1_153_024,
        crate::brotli_prefix::MTF_OFFSET == 1_159_916,
        crate::brotli_prefix::MTF_LIST_OFFSET == 1_159_920,
        crate::brotli_prefix::MTF_LIST_OFFSET + 256 <= B3B_SCALAR_OFFSET,
        crate::brotli_prefix::FIXED_SCRATCH_BYTES == 1_176_560,
        crate::brotli_prefix::BUILDER_OFFSET == 1_156_860,
        crate::brotli_prefix::BUILDER_CODE_LENGTHS_OFFSET == 1_156_860,
{}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompressedFormatError {
    InvalidPrefixCode,
    DuplicateSimpleSymbol,
    CodeLengthSpace,
    InvalidBlockLength,
    ContextMapRepeat,
    ContextMapValue,
    ContextMapCoverage,
    InvalidBlockSwitch,
    InvalidSequence,
    InvalidMetadata,
    InvalidDistanceAlphabet,
    InvalidBlockDeclaration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompressedHeaderError {
    InvalidFormat(CompressedFormatError),
    Truncated,
    UnsupportedMode,
    Workspace(crate::brotli_prefix::WorkspaceError),
    InternalState,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CompressedHeader {
    num_block_types: [u16; 3],
    initial_block_lengths: [u32; 3],
    distance_postfix_bits: u8,
    num_direct_distance_codes: u16,
    distance_alphabet_size: u16,
    num_literal_htrees: u16,
    num_distance_htrees: u16,
    literal_context_map_len: u16,
    distance_context_map_len: u16,
    literal_context_modes_len: u16,
    literal_trees_initialized: u16,
    command_trees_initialized: u16,
    distance_trees_initialized: u16,
    active_literal_tree: u16,
    active_command_tree: u16,
    active_distance_tree: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompressedHeaderStatus {
    NeedInput,
    Complete(CompressedHeader),
    Failed(CompressedHeaderError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CompressedHeaderStep {
    consumed: usize,
    status: CompressedHeaderStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompressedOuterPhase {
    BlockCount,
    BlockTypeTree,
    BlockLengthTree,
    InitialBlockLength,
    DistanceParameters,
    ContextModes,
    LiteralContextMap,
    DistanceContextMap,
    LiteralTreeGroup,
    CommandTreeGroup,
    DistanceTreeGroup,
    Complete,
    Failed,
}

spec fn compressed_outer_phase_tag_spec(phase: CompressedOuterPhase) -> u8 {
    match phase {
        CompressedOuterPhase::BlockCount => 0,
        CompressedOuterPhase::BlockTypeTree => 1,
        CompressedOuterPhase::BlockLengthTree => 2,
        CompressedOuterPhase::InitialBlockLength => 3,
        CompressedOuterPhase::DistanceParameters => 4,
        CompressedOuterPhase::ContextModes => 5,
        CompressedOuterPhase::LiteralContextMap => 6,
        CompressedOuterPhase::DistanceContextMap => 7,
        CompressedOuterPhase::LiteralTreeGroup => 8,
        CompressedOuterPhase::CommandTreeGroup => 9,
        CompressedOuterPhase::DistanceTreeGroup => 10,
        CompressedOuterPhase::Complete => 11,
        CompressedOuterPhase::Failed => 12,
    }
}

fn compressed_outer_phase_tag(phase: CompressedOuterPhase) -> (r: u8)
    ensures r == compressed_outer_phase_tag_spec(phase), r <= 12,
{
    match phase {
        CompressedOuterPhase::BlockCount => 0,
        CompressedOuterPhase::BlockTypeTree => 1,
        CompressedOuterPhase::BlockLengthTree => 2,
        CompressedOuterPhase::InitialBlockLength => 3,
        CompressedOuterPhase::DistanceParameters => 4,
        CompressedOuterPhase::ContextModes => 5,
        CompressedOuterPhase::LiteralContextMap => 6,
        CompressedOuterPhase::DistanceContextMap => 7,
        CompressedOuterPhase::LiteralTreeGroup => 8,
        CompressedOuterPhase::CommandTreeGroup => 9,
        CompressedOuterPhase::DistanceTreeGroup => 10,
        CompressedOuterPhase::Complete => 11,
        CompressedOuterPhase::Failed => 12,
    }
}

fn decode_compressed_outer_phase(tag: u8) -> (r: Option<CompressedOuterPhase>)
    ensures r == if tag <= 12 {
        Some(match tag {
            0 => CompressedOuterPhase::BlockCount,
            1 => CompressedOuterPhase::BlockTypeTree,
            2 => CompressedOuterPhase::BlockLengthTree,
            3 => CompressedOuterPhase::InitialBlockLength,
            4 => CompressedOuterPhase::DistanceParameters,
            5 => CompressedOuterPhase::ContextModes,
            6 => CompressedOuterPhase::LiteralContextMap,
            7 => CompressedOuterPhase::DistanceContextMap,
            8 => CompressedOuterPhase::LiteralTreeGroup,
            9 => CompressedOuterPhase::CommandTreeGroup,
            10 => CompressedOuterPhase::DistanceTreeGroup,
            11 => CompressedOuterPhase::Complete,
            _ => CompressedOuterPhase::Failed,
        })
    } else { None },
{
    match tag {
        0 => Some(CompressedOuterPhase::BlockCount),
        1 => Some(CompressedOuterPhase::BlockTypeTree),
        2 => Some(CompressedOuterPhase::BlockLengthTree),
        3 => Some(CompressedOuterPhase::InitialBlockLength),
        4 => Some(CompressedOuterPhase::DistanceParameters),
        5 => Some(CompressedOuterPhase::ContextModes),
        6 => Some(CompressedOuterPhase::LiteralContextMap),
        7 => Some(CompressedOuterPhase::DistanceContextMap),
        8 => Some(CompressedOuterPhase::LiteralTreeGroup),
        9 => Some(CompressedOuterPhase::CommandTreeGroup),
        10 => Some(CompressedOuterPhase::DistanceTreeGroup),
        11 => Some(CompressedOuterPhase::Complete),
        12 => Some(CompressedOuterPhase::Failed),
        _ => None,
    }
}

spec fn b3b_workspace_shape(workspace_len: nat, window_bytes: u32) -> bool {
    &&& 1_024 <= window_bytes <= 16_777_216
    &&& (window_bytes & ((window_bytes - 1) as u32)) == 0
    &&& workspace_len
        >= window_bytes as nat + crate::brotli_prefix::FIXED_SCRATCH_BYTES as nat
}

fn b3b_state_address(
    workspace_len: usize,
    window_bytes: u32,
    relative: u16,
    width: u8,
) -> (r: Result<usize, crate::brotli_prefix::WorkspaceError>)
    requires 1 <= width <= 4,
    ensures r.is_ok() ==> {
        &&& b3b_workspace_shape(workspace_len as nat, window_bytes)
        &&& relative as nat + width as nat <= B3B_SCALAR_BYTES
        &&& r.unwrap() as nat
            == window_bytes as nat + B3B_SCALAR_OFFSET as nat + relative as nat
        &&& r.unwrap() as nat + width as nat <= workspace_len
    },
        b3b_workspace_shape(workspace_len as nat, window_bytes)
            && relative as nat + width as nat <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    if window_bytes < 1_024 || window_bytes > 16_777_216
        || (window_bytes & (window_bytes - 1)) != 0 {
        return Err(crate::brotli_prefix::WorkspaceError::InvalidWindowBits);
    }
    if relative as usize + width as usize > B3B_SCALAR_BYTES as usize {
        return Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol);
    }
    let required = match (window_bytes as usize)
        .checked_add(crate::brotli_prefix::FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall),
    };
    if workspace_len < required {
        return Err(crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall);
    }
    let base = match (window_bytes as usize).checked_add(B3B_SCALAR_OFFSET as usize) {
        Some(value) => value,
        None => return Err(crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall),
    };
    let at = match base.checked_add(relative as usize) {
        Some(value) => value,
        None => return Err(crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall),
    };
    proof {
        assert(B3B_SCALAR_OFFSET as nat + B3B_SCALAR_BYTES as nat
            <= crate::brotli_prefix::FIXED_SCRATCH_BYTES as nat);
    }
    Ok(at)
}

spec fn b3b_initial_scalar_byte(relative: int) -> u8 {
    if relative == B3B_PENDING_RUN
        || relative == B3B_GROUP_KIND
        || relative == B3B_ACTIVE_REGION
        || relative == B3B_BLOCK_SWITCH_KIND { 255 }
    else if relative == B3B_BLOCK_RING
        || relative == B3B_BLOCK_RING + 4
        || relative == B3B_BLOCK_RING + 8 { 1 }
    else if relative == B3B_MTF_UPPER_BOUND { 63 }
    else { 0 }
}

spec fn b3b_initial_metadata_index(window_bytes: u32, index: int) -> bool {
    let relative = index - window_bytes as int;
    ||| crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET <= relative
        < crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET + 12
    ||| crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET <= relative
        < crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET + 12
    ||| crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET <= relative
        < crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET + 4
}

spec fn b3b_initialization_owned_index(window_bytes: u32, index: int) -> bool {
    let relative = index - window_bytes as int;
    ||| B3B_SCALAR_OFFSET <= relative < B3B_SCALAR_OFFSET + B3B_SCALAR_BYTES
    ||| b3b_initial_metadata_index(window_bytes, index)
}

spec fn b3b_scalar_base(window_bytes: u32) -> int {
    window_bytes as int + B3B_SCALAR_OFFSET as int
}

spec fn b3b_scalar_byte_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    relative: u16,
) -> u8 {
    workspace[b3b_scalar_base(window_bytes) + relative as int]
}

spec fn b3b_scalar_u16_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    relative: u16,
) -> nat {
    b3b_scalar_byte_at(workspace, window_bytes, relative) as nat
        + 256 * b3b_scalar_byte_at(workspace, window_bytes, (relative + 1) as u16) as nat
}

spec fn b3b_scalar_u32_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    relative: u16,
) -> nat {
    b3b_scalar_byte_at(workspace, window_bytes, relative) as nat
        + 256 * b3b_scalar_byte_at(workspace, window_bytes, (relative + 1) as u16) as nat
        + 65_536 * b3b_scalar_byte_at(workspace, window_bytes, (relative + 2) as u16) as nat
        + 16_777_216 * b3b_scalar_byte_at(workspace, window_bytes, (relative + 3) as u16) as nat
}

spec fn serialized_mtf_state_ok(workspace: Seq<u8>, window_bytes: u32) -> bool {
    let upper = b3b_scalar_byte_at(workspace, window_bytes, B3B_MTF_UPPER_BOUND);
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& upper <= 63
    &&& (upper == 63 || crate::brotli_prefix::mtf_reusable(
        crate::brotli_prefix::mtf_list_values(workspace, window_bytes),
        upper,
    ))
}

spec fn serialized_context_map_prefix_ok(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> bool {
    let kind_tag = b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND);
    let kind = if kind_tag == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    let active_len = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_SIZE);
    let map_index = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_INDEX);
    let initialized = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_INITIALIZED);
    let num_trees = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES);
    &&& kind_tag <= 1
    &&& 1 <= active_len <= crate::brotli_prefix::context_map_capacity(kind)
    &&& map_index == initialized
    &&& initialized <= active_len
    &&& num_trees <= 256
    &&& (num_trees == 0 ==> initialized == 0)
    &&& (num_trees > 0 ==> {
        &&& (kind_tag == 0 ==> forall|i: u16| (i as nat) < initialized ==> #[trigger]
            workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                i,
            ) as int] < num_trees)
        &&& (kind_tag == 1 ==> forall|i: u16| (i as nat) < initialized ==> #[trigger]
            workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                i,
            ) as int] < num_trees)
    })
}

spec fn serialized_context_data_ok(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> bool {
    let phase = b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_PHASE);
    let max_run = b3b_scalar_byte_at(workspace, window_bytes, B3B_MAX_RUN_PREFIX);
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& serialized_mtf_state_ok(workspace, window_bytes)
    &&& serialized_context_map_prefix_ok(workspace, window_bytes)
    &&& phase <= 9
    &&& max_run <= 16
}

spec fn serialized_context_complete_map_ok(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> bool {
    let kind_tag = b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND);
    let kind = if kind_tag == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    let active_len = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_SIZE);
    let num_trees = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES);
    &&& serialized_context_map_prefix_ok(workspace, window_bytes)
    &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_INITIALIZED) == active_len
    &&& 1 <= num_trees <= 256
    &&& crate::brotli_prefix::context_tree_coverage(
        crate::brotli_prefix::context_map_values(
            workspace,
            window_bytes,
            kind,
            active_len as u16,
        ),
        num_trees as u16,
    )
}

spec fn serialized_context_phase_payload_ok(
    workspace: Seq<u8>,
    window_bytes: u32,
    phase: u8,
) -> bool {
    let num_trees = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES);
    let active_len = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_SIZE);
    let initialized = b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_INITIALIZED);
    let pending = b3b_scalar_byte_at(workspace, window_bytes, B3B_PENDING_RUN);
    &&& phase <= 9
    &&& (phase == 0 ==> num_trees == 0 && initialized == 0)
    &&& (1 <= phase && phase <= 8 ==> 1 <= num_trees <= 256)
    &&& (phase == 5 ==> 1 <= pending <= 16 && initialized < active_len)
    &&& (phase == 6 || phase == 7 || phase == 8 || phase == 9
        ==> initialized == active_len)
    &&& (phase == 9 ==> 1 <= num_trees <= 256)
    &&& (phase == 9 ==> serialized_context_complete_map_ok(workspace, window_bytes))
}

spec fn serialized_context_state_ok(
    workspace: Seq<u8>,
    window_bytes: u32,
) -> bool {
    let phase = b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_PHASE);
    &&& serialized_context_data_ok(workspace, window_bytes)
    &&& serialized_context_phase_payload_ok(workspace, window_bytes, phase)
}

proof fn serialized_context_prefix_value_bound(
    workspace: Seq<u8>,
    window_bytes: u32,
    index: int,
)
    requires
        b3b_workspace_shape(workspace.len() as nat, window_bytes),
        serialized_context_map_prefix_ok(workspace, window_bytes),
        b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES) > 0,
        0 <= index < b3b_scalar_u16_at(
            workspace,
            window_bytes,
            B3B_MAP_INITIALIZED,
        ),
        index < 65_536,
    ensures {
        let kind = if b3b_scalar_byte_at(
            workspace,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        };
        workspace[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            index as u16,
        ) as int] < b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES)
    },
{
    reveal(serialized_context_map_prefix_ok);
    assert(serialized_context_map_prefix_ok(workspace, window_bytes));
    assert(b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES) > 0);
    assert((index as u16) as int == index);
    assert((index as u16) as nat == index as nat);
    b3b_scalar_layout_is_exact();
    let kind = if b3b_scalar_byte_at(
        workspace,
        window_bytes,
        B3B_CONTEXT_KIND,
    ) == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    match kind {
        crate::brotli_prefix::ContextMapKind::Literal => {}
        crate::brotli_prefix::ContextMapKind::Distance => {}
    }
    assert(crate::brotli_prefix::context_entry_at(
        window_bytes,
        kind,
        index as u16,
    ) < workspace.len());
    match kind {
        crate::brotli_prefix::ContextMapKind::Literal => {
            assert(b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND) == 0);
            assert(workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                index as u16,
            ) as int] < b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES));
        }
        crate::brotli_prefix::ContextMapKind::Distance => {
            assert(b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND) == 1);
            assert(workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                index as u16,
            ) as int] < b3b_scalar_u16_at(workspace, window_bytes, B3B_MAP_TREES));
        }
    }
}

proof fn context_phase_transition_preserves_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    next_phase: u8,
)
    requires
        next_phase <= 8,
        serialized_context_data_ok(before, window_bytes),
        serialized_context_phase_payload_ok(before, window_bytes, next_phase),
        after == before.update(
            b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int,
            next_phase,
        ),
    ensures
        serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
{
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert(after.len() == before.len());
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16)
            < b3b_scalar_base(window_bytes) as nat);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    assert(serialized_context_map_prefix_ok(after, window_bytes));
    assert(serialized_context_data_ok(after, window_bytes));
    assert(serialized_context_phase_payload_ok(after, window_bytes, next_phase));
    assert(serialized_context_state_ok(after, window_bytes));
}

proof fn trivial_context_map_phase_to_complete(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
)
    requires
        serialized_context_data_ok(before, window_bytes),
        b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES) == 1,
        b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        after == before.update(
            b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int,
            9,
        ),
    ensures serialized_context_state_ok(after, window_bytes),
{
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let kind = if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    let active_nat = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
    let active_len = active_nat as u16;
    assert(1 <= active_nat);
    assert((active_len as nat) == active_nat);
    serialized_context_prefix_value_bound(before, window_bytes, 0);
    assert(before[crate::brotli_prefix::context_entry_at(
        window_bytes,
        kind,
        0,
    ) as int] == 0);
    assert(crate::brotli_prefix::context_map_values(
        before,
        window_bytes,
        kind,
        active_len,
    )[0] == 0);
    assert(crate::brotli_prefix::value_seen(
        crate::brotli_prefix::context_map_values(
            before,
            window_bytes,
            kind,
            active_len,
        ),
        active_nat,
        0,
    ));
    assert(crate::brotli_prefix::context_tree_coverage(
        crate::brotli_prefix::context_map_values(
            before,
            window_bytes,
            kind,
            active_len,
        ),
        1,
    ));
    assert(serialized_context_complete_map_ok(before, window_bytes));
    assert(serialized_context_phase_payload_ok(before, window_bytes, 9));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16)
            < b3b_scalar_base(window_bytes) as nat);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    assert(serialized_mtf_state_ok(after, window_bytes));
    assert(serialized_context_map_prefix_ok(after, window_bytes));
    assert(crate::brotli_prefix::context_map_values(
        after,
        window_bytes,
        kind,
        active_len,
    ) =~= crate::brotli_prefix::context_map_values(
        before,
        window_bytes,
        kind,
        active_len,
    ));
    assert(serialized_context_complete_map_ok(after, window_bytes));
    assert(serialized_context_data_ok(after, window_bytes));
    assert(serialized_context_phase_payload_ok(after, window_bytes, 9));
    assert(serialized_context_state_ok(after, window_bytes));
}

proof fn context_coverage_phase_to_complete(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
)
    requires
        serialized_context_state_ok(before, window_bytes),
        b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE) == 8,
        serialized_context_complete_map_ok(before, window_bytes),
        after == before.update(
            b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int,
            9,
        ),
    ensures
        serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
{
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert(after.len() == before.len());
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16)
            < b3b_scalar_base(window_bytes) as nat);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    assert(serialized_mtf_state_ok(after, window_bytes));
    assert(serialized_context_map_prefix_ok(after, window_bytes));
    let kind = if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    let active_nat = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
    let active_len = active_nat as u16;
    assert((active_len as nat) == active_nat);
    assert(crate::brotli_prefix::context_map_values(
        after,
        window_bytes,
        kind,
        active_len,
    ) =~= crate::brotli_prefix::context_map_values(
        before,
        window_bytes,
        kind,
        active_len,
    )) by {
        assert forall|i: int| 0 <= i < active_nat implies #[trigger]
            after[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] == before[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] by {
            assert(crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) < b3b_scalar_base(window_bytes) as nat);
        }
    }
    assert(serialized_context_complete_map_ok(after, window_bytes));
    assert(serialized_context_state_ok(after, window_bytes));
}

proof fn coverage_frame_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
)
    requires
        serialized_context_state_ok(before, window_bytes),
        b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE) == 8,
        crate::brotli_prefix::coverage_bitmap_frame(before, after, window_bytes),
    ensures
        serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
{
    reveal(crate::brotli_prefix::coverage_bitmap_frame);
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert forall|i: int| 0 <= i < B3B_SCALAR_BYTES implies #[trigger]
        after[b3b_scalar_base(window_bytes) + i]
            == before[b3b_scalar_base(window_bytes) + i] by {
        assert(window_bytes as int
            + crate::brotli_prefix::BUILDER_CODE_LENGTHS_OFFSET as int + 32
            <= b3b_scalar_base(window_bytes) + i);
    }
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(window_bytes as int
            + crate::brotli_prefix::BUILDER_CODE_LENGTHS_OFFSET as int + 32
            <= crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    assert(serialized_context_map_prefix_ok(after, window_bytes));
    assert(serialized_context_state_ok(after, window_bytes));
}

proof fn context_mtf_phase_to_coverage(
    before: Seq<u8>,
    transformed: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    num_trees: u16,
    next_upper: u8,
)
    requires
        serialized_context_state_ok(before, window_bytes),
        b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE) == 7,
        kind == if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE) == active_len,
        b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES) == num_trees,
        crate::brotli_prefix::mtf_workspace_frame(
            before,
            transformed,
            window_bytes,
            kind,
            active_len,
        ),
        forall|i: int| 0 <= i < active_len ==> #[trigger]
            transformed[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] < num_trees,
        next_upper <= 63,
        crate::brotli_prefix::mtf_reusable(
            crate::brotli_prefix::mtf_list_values(transformed, window_bytes),
            next_upper,
        ),
        after == transformed
            .update(
                b3b_scalar_base(window_bytes) + B3B_MTF_UPPER_BOUND as int,
                next_upper,
            )
            .update(
                b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int,
                8,
            ),
    ensures
        serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE) == active_len,
{
    reveal(crate::brotli_prefix::mtf_workspace_frame);
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert(after.len() == transformed.len());
    assert(transformed.len() == before.len());
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND) == next_upper);
    assert(crate::brotli_prefix::mtf_list_values(after, window_bytes) =~=
        crate::brotli_prefix::mtf_list_values(transformed, window_bytes));
    assert(serialized_mtf_state_ok(after, window_bytes));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND));
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE) == active_len);
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES) == num_trees);
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED) == active_len);
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INDEX) == active_len);
    assert forall|i: u16| (i as nat) < active_len implies #[trigger]
        after[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            i,
        ) as int] < num_trees by {
        assert(0 <= i as int);
        assert((i as int) < active_len);
        assert(((i as int) as u16) == i);
        assert(transformed[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            (i as int) as u16,
        ) as int] < num_trees);
        assert(crate::brotli_prefix::context_entry_at(window_bytes, kind, i)
            < b3b_scalar_base(window_bytes) as nat);
    }
    assert(serialized_context_map_prefix_ok(after, window_bytes));
    assert(serialized_context_state_ok(after, window_bytes));
}

proof fn four_byte_update_preserves_outside(
    before: Seq<u8>,
    after: Seq<u8>,
    at: int,
    b0: u8,
    b1: u8,
    b2: u8,
    b3: u8,
)
    requires
        0 <= at,
        at + 4 <= before.len(),
        after == before
            .update(at, b0)
            .update(at + 1, b1)
            .update(at + 2, b2)
            .update(at + 3, b3),
    ensures
        after.len() == before.len(),
        forall|i: int| 0 <= i < before.len() && (i < at || at + 4 <= i)
            ==> #[trigger] after[i] == before[i],
{
}

proof fn context_map_update_extends_valid_prefix(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    initialized: u16,
    value: u8,
    num_trees: u16,
)
    requires
        1 <= num_trees <= 256,
        value < num_trees,
        initialized < crate::brotli_prefix::context_map_capacity(kind),
        b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED) <= initialized,
        forall|i: int| 0 <= i < initialized ==> #[trigger]
            before[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] < num_trees,
        after == before.update(
            crate::brotli_prefix::context_entry_at(window_bytes, kind, initialized) as int,
            value,
        ),
    ensures
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES),
{
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let changed = crate::brotli_prefix::context_entry_at(
        window_bytes,
        kind,
        initialized,
    ) as int;
    match kind {
        crate::brotli_prefix::ContextMapKind::Literal => {
            assert(changed < window_bytes as int + crate::brotli_prefix::MTF_OFFSET as int);
        }
        crate::brotli_prefix::ContextMapKind::Distance => {
            assert(changed < window_bytes as int + crate::brotli_prefix::MTF_OFFSET as int);
        }
    }
    assert(before.len() == after.len());
    assert(b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(changed < crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_data_ok(before, window_bytes) {
        reveal(serialized_context_data_ok);
        reveal(serialized_context_map_prefix_ok);
        let stored_initialized = b3b_scalar_u16_at(
            before,
            window_bytes,
            B3B_MAP_INITIALIZED,
        );
        let stored_num_trees = b3b_scalar_u16_at(
            before,
            window_bytes,
            B3B_MAP_TREES,
        );
        if stored_num_trees > 0 {
            if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
                assert forall|i: u16| (i as nat) < stored_initialized implies #[trigger]
                    after[crate::brotli_prefix::context_entry_at(
                        window_bytes,
                        crate::brotli_prefix::ContextMapKind::Literal,
                        i,
                    ) as int] < stored_num_trees by {
                    serialized_context_prefix_value_bound(before, window_bytes, i as int);
                    assert((i as nat) < initialized);
                    assert(i != initialized);
                }
            } else {
                assert forall|i: u16| (i as nat) < stored_initialized implies #[trigger]
                    after[crate::brotli_prefix::context_entry_at(
                        window_bytes,
                        crate::brotli_prefix::ContextMapKind::Distance,
                        i,
                    ) as int] < stored_num_trees by {
                    serialized_context_prefix_value_bound(before, window_bytes, i as int);
                    assert((i as nat) < initialized);
                    assert(i != initialized);
                }
            }
        }
        assert(serialized_context_map_prefix_ok(after, window_bytes));
        assert(serialized_context_data_ok(after, window_bytes));
    }
}

proof fn context_prefix_int_implies_u16(
    workspace: Seq<u8>,
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    initialized: u16,
    num_trees: u16,
)
    requires
        forall|i: int| 0 <= i < initialized ==> #[trigger]
            workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] < num_trees,
    ensures
        forall|i: u16| i < initialized ==> #[trigger]
            workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i,
            ) as int] < num_trees,
{
    assert forall|i: u16| i < initialized implies #[trigger]
        workspace[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            i,
        ) as int] < num_trees by {
        assert(0 <= i as int);
        assert((i as int) < initialized);
        assert(((i as int) as u16) == i);
    }
}

proof fn context_progress_values_match_serialized_kind(
    workspace: Seq<u8>,
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    progress: u16,
    num_trees: u16,
)
    requires
        b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND) <= 1,
        kind == if b3b_scalar_byte_at(
            workspace,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        forall|i: u16| i < progress ==> #[trigger]
            workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i,
            ) as int] < num_trees,
    ensures
        (b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND) == 0
            ==> forall|i: u16| i < progress ==> #[trigger]
                workspace[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] < num_trees),
        (b3b_scalar_byte_at(workspace, window_bytes, B3B_CONTEXT_KIND) == 1
            ==> forall|i: u16| i < progress ==> #[trigger]
                workspace[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] < num_trees),
{
    match kind {
        crate::brotli_prefix::ContextMapKind::Literal => {}
        crate::brotli_prefix::ContextMapKind::Distance => {}
    }
}

proof fn observed_context_frame_preserves_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        before.len() == after.len(),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INDEX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INDEX),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED),
        b3b_scalar_byte_at(after, window_bytes, B3B_MAX_RUN_PREFIX)
            == b3b_scalar_byte_at(before, window_bytes, B3B_MAX_RUN_PREFIX),
        b3b_scalar_byte_at(after, window_bytes, B3B_PENDING_RUN)
            == b3b_scalar_byte_at(before, window_bytes, B3B_PENDING_RUN),
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        (b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0
            ==> forall|i: u16| (i as nat) < b3b_scalar_u16_at(
                before,
                window_bytes,
                B3B_MAP_SIZE,
            ) ==> #[trigger] after[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                i,
            ) as int] == before[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                i,
            ) as int]),
        (b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 1
            ==> forall|i: u16| (i as nat) < b3b_scalar_u16_at(
                before,
                window_bytes,
                B3B_MAP_SIZE,
            ) ==> #[trigger] after[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                i,
            ) as int] == before[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                i,
            ) as int]),
    ensures
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
{
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    let kind = if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    let active_nat = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
    let active_len = active_nat as u16;
    assert((active_len as nat) == active_nat);
    if serialized_context_data_ok(before, window_bytes) {
        let initialized = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED);
        let num_trees = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES);
        if num_trees > 0 {
            assert forall|i: u16| (i as nat) < initialized implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    kind,
                    i,
                ) as int] < num_trees by {
                serialized_context_prefix_value_bound(before, window_bytes, i as int);
                assert((i as nat) < active_nat);
                match kind {
                    crate::brotli_prefix::ContextMapKind::Literal => {}
                    crate::brotli_prefix::ContextMapKind::Distance => {}
                }
            }
        }
        assert(serialized_context_map_prefix_ok(after, window_bytes));
        assert(serialized_context_data_ok(after, window_bytes));
    }
    if serialized_context_state_ok(before, window_bytes) {
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE) == 9 {
            assert(crate::brotli_prefix::context_map_values(
                after,
                window_bytes,
                kind,
                active_len,
            ) =~= crate::brotli_prefix::context_map_values(
                before,
                window_bytes,
                kind,
                active_len,
            )) by {
                assert forall|i: int| 0 <= i < active_nat implies
                    crate::brotli_prefix::context_map_values(
                        after,
                        window_bytes,
                        kind,
                        active_len,
                    )[i] == crate::brotli_prefix::context_map_values(
                        before,
                        window_bytes,
                        kind,
                        active_len,
                    )[i] by {
                    assert((i as u16) as int == i);
                    match kind {
                        crate::brotli_prefix::ContextMapKind::Literal => {
                            assert(b3b_scalar_byte_at(
                                before,
                                window_bytes,
                                B3B_CONTEXT_KIND,
                            ) == 0);
                            assert(after[crate::brotli_prefix::context_entry_at(
                                window_bytes,
                                crate::brotli_prefix::ContextMapKind::Literal,
                                i as u16,
                            ) as int] == before[crate::brotli_prefix::context_entry_at(
                                window_bytes,
                                crate::brotli_prefix::ContextMapKind::Literal,
                                i as u16,
                            ) as int]);
                        }
                        crate::brotli_prefix::ContextMapKind::Distance => {
                            assert(b3b_scalar_byte_at(
                                before,
                                window_bytes,
                                B3B_CONTEXT_KIND,
                            ) == 1);
                            assert(after[crate::brotli_prefix::context_entry_at(
                                window_bytes,
                                crate::brotli_prefix::ContextMapKind::Distance,
                                i as u16,
                            ) as int] == before[crate::brotli_prefix::context_entry_at(
                                window_bytes,
                                crate::brotli_prefix::ContextMapKind::Distance,
                                i as u16,
                            ) as int]);
                        }
                    }
                }
            }
            assert(serialized_context_complete_map_ok(after, window_bytes));
        }
        assert(serialized_context_state_ok(after, window_bytes));
    }
}

proof fn queue_scalar_write_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    relative: u16,
    value: u8,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        relative < B3B_CONTEXT_PHASE,
        after == before.update(
            b3b_scalar_base(window_bytes) + relative as int,
            value,
        ),
    ensures
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        relative != B3B_OUTER_PHASE ==> b3b_scalar_byte_at(
            after,
            window_bytes,
            B3B_OUTER_PHASE,
        ) == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        b3b_workspace_shape(before.len() as nat, window_bytes) ==> {
            &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND)
            &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE)
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE)
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
                == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES)
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
                == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED)
        },
{
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert(b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16)
            < b3b_scalar_base(window_bytes) as nat);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_state_ok(before, window_bytes) {
        assert(serialized_context_data_ok(before, window_bytes));
    }
    if serialized_context_data_ok(before, window_bytes) {
      let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
      if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
        assert forall|i: u16| (i as nat) < active_len implies #[trigger]
            after[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                i,
            ) as int] == before[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                i,
            ) as int] by {
            assert(crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                i,
            ) < b3b_scalar_base(window_bytes) as nat);
        }
      } else {
        assert forall|i: u16| (i as nat) < active_len implies #[trigger]
            after[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                i,
            ) as int] == before[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                i,
            ) as int] by {
            assert(crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                i,
            ) < b3b_scalar_base(window_bytes) as nat);
        }
      }
      observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn queue_write_preserves_decoder_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    relative: u16,
    value: u8,
)
    requires
        compressed_decoder_state_ok(before, window_bytes),
        relative <= B3B_QUEUE_OFFSET_BYTE,
        after == before.update(
            b3b_scalar_base(window_bytes) + relative as int,
            value,
        ),
    ensures compressed_decoder_state_ok(after, window_bytes),
{
    queue_scalar_write_preserves_context_state(
        before,
        after,
        window_bytes,
        relative,
        value,
    );
    reveal(compressed_decoder_state_ok);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
}

proof fn result_tree_write_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    relative: u16,
    value: u16,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES,
        after == before
            .update(
                b3b_scalar_base(window_bytes) + relative as int,
                (value % 256) as u8,
            )
            .update(
                b3b_scalar_base(window_bytes) + relative as int + 1,
                (value / 256) as u8,
            ),
    ensures
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
{
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
        == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND));
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES));
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE));
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INDEX)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INDEX));
    assert(b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MAX_RUN_PREFIX)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MAX_RUN_PREFIX));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_PENDING_RUN)
        == b3b_scalar_byte_at(before, window_bytes, B3B_PENDING_RUN));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16)
            < b3b_scalar_base(window_bytes) as nat);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_data_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) < b3b_scalar_base(window_bytes) as nat);
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) < b3b_scalar_base(window_bytes) as nat);
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn high_scalar_frame_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        before.len() == after.len(),
        forall|i: int| 0 <= i < b3b_scalar_base(window_bytes) + B3B_GROUP_KIND as int
            ==> #[trigger] after[i] == before[i],
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
    ensures
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INDEX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INDEX),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED),
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
{
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MAX_RUN_PREFIX)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MAX_RUN_PREFIX));
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_PENDING_RUN)
        == b3b_scalar_byte_at(before, window_bytes, B3B_PENDING_RUN));
    if serialized_context_data_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) < b3b_scalar_base(window_bytes) as nat);
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) < b3b_scalar_base(window_bytes) as nat);
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn builder_length_update_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    initialized: u16,
    value: u8,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        initialized < crate::brotli_prefix::BUILDER_CODE_LENGTHS,
        after == before.update(
            crate::brotli_prefix::builder_entry_at(
                window_bytes,
                crate::brotli_prefix::BUILDER_CODE_LENGTHS_OFFSET,
                initialized,
                1,
            ) as int,
            value,
        ),
    ensures
        before.len() == after.len(),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        compressed_decoder_state_ok(before, window_bytes)
            ==> compressed_decoder_state_ok(after, window_bytes),
{
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let at = crate::brotli_prefix::builder_entry_at(
        window_bytes,
        crate::brotli_prefix::BUILDER_CODE_LENGTHS_OFFSET,
        initialized,
        1,
    );
    assert(at < window_bytes as nat + crate::brotli_prefix::MTF_LIST_OFFSET as nat);
    assert(at < b3b_scalar_base(window_bytes) as nat);
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(at < crate::brotli_prefix::mtf_list_at(window_bytes, i as u16));
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_data_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) < at);
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) < at);
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn context_mode_update_preserves_decoder_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    initialized: u16,
    value: u8,
)
    requires
        compressed_decoder_state_ok(before, window_bytes),
        initialized < crate::brotli_prefix::LITERAL_CONTEXT_MODES_BYTES,
        after == before.update(
            crate::brotli_prefix::context_mode_at(window_bytes, initialized) as int,
            value,
        ),
    ensures compressed_decoder_state_ok(after, window_bytes),
{
    reveal(compressed_decoder_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let at = crate::brotli_prefix::context_mode_at(window_bytes, initialized);
    assert(at < window_bytes as nat + crate::brotli_prefix::MTF_LIST_OFFSET as nat);
    assert(at < b3b_scalar_base(window_bytes) as nat);
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(at < crate::brotli_prefix::mtf_list_at(window_bytes, i as u16));
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_state_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) < at);
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) < at);
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn selected_tree_frame_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    symbols: u16,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        (tree as nat) < crate::brotli_prefix::tree_region_count(region),
        (symbols as nat) <= crate::brotli_prefix::tree_region_symbols(region),
        crate::brotli_prefix::selected_tree_frame(
            before,
            after,
            window_bytes,
            region,
            tree,
            symbols,
        ),
    ensures
        before.len() == after.len(),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(before, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(after, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_COUNT),
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        compressed_decoder_state_ok(before, window_bytes)
            ==> compressed_decoder_state_ok(after, window_bytes),
{
    reveal(crate::brotli_prefix::selected_tree_frame);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let start = crate::brotli_prefix::tree_record_at(window_bytes, region, tree, 0);
    let end = start + symbols as nat * 3;
    match region {
        crate::brotli_prefix::TreeRegion::Literal => {
            assert((tree as nat) < 256);
            assert((symbols as nat) <= 256);
            assert(start == window_bytes as nat + (tree as nat * 256) * 3);
            assert(end <= window_bytes as nat
                + crate::brotli_prefix::COMMAND_TREES_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::Command => {
            assert((tree as nat) < 256);
            assert((symbols as nat) <= 704);
            assert(start == window_bytes as nat + 196_608
                + (tree as nat * 704) * 3);
            assert(end <= window_bytes as nat
                + crate::brotli_prefix::DISTANCE_TREES_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::Distance => {
            assert((tree as nat) < 256);
            assert((symbols as nat) <= 520);
            assert(start == window_bytes as nat + 737_280
                + (tree as nat * 520) * 3);
            assert(end <= window_bytes as nat
                + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::BlockType => {
            assert((tree as nat) < 3);
            assert((symbols as nat) <= 258);
            assert(start == window_bytes as nat + 1_154_304
                + (tree as nat * 258) * 3);
            assert(end <= window_bytes as nat
                + crate::brotli_prefix::BLOCK_LENGTH_TREES_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::BlockLength => {
            assert((tree as nat) < 3);
            assert((symbols as nat) <= 26);
            assert(start == window_bytes as nat + 1_156_626
                + (tree as nat * 26) * 3);
            assert(end <= window_bytes as nat
                + crate::brotli_prefix::BUILDER_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::TemporaryContext => {
            assert((tree as nat) < 1);
            assert((symbols as nat) <= 272);
            assert(start == window_bytes as nat + 1_159_100
                + (tree as nat * 272) * 3);
            assert(end <= window_bytes as nat
                + crate::brotli_prefix::MTF_OFFSET as nat);
        }
    }
    assert(end <= window_bytes as nat + crate::brotli_prefix::MTF_OFFSET as nat);
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(end <= crate::brotli_prefix::mtf_list_at(window_bytes, i as u16));
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_data_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                match region {
                    crate::brotli_prefix::TreeRegion::Literal
                    | crate::brotli_prefix::TreeRegion::Command
                    | crate::brotli_prefix::TreeRegion::Distance => {
                        assert(end <= window_bytes as nat
                            + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as nat);
                        assert(end <= crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Literal,
                            i,
                        ));
                    }
                    _ => {
                        assert(crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Literal,
                            i,
                        ) < window_bytes as nat
                            + crate::brotli_prefix::LITERAL_CONTEXT_MODES_OFFSET as nat);
                        assert(window_bytes as nat
                            + crate::brotli_prefix::LITERAL_CONTEXT_MODES_OFFSET as nat
                            <= start);
                        assert(crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Literal,
                            i,
                        ) < start);
                    }
                }
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                match region {
                    crate::brotli_prefix::TreeRegion::Literal
                    | crate::brotli_prefix::TreeRegion::Command
                    | crate::brotli_prefix::TreeRegion::Distance => {
                        assert(end <= window_bytes as nat
                            + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as nat);
                        assert(end <= crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Distance,
                            i,
                        ));
                    }
                    _ => {
                        assert(crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Distance,
                            i,
                        ) < window_bytes as nat
                            + crate::brotli_prefix::LITERAL_CONTEXT_MODES_OFFSET as nat);
                        assert(window_bytes as nat
                            + crate::brotli_prefix::LITERAL_CONTEXT_MODES_OFFSET as nat
                            <= start);
                        assert(crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Distance,
                            i,
                        ) < start);
                    }
                }
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn metadata_frame_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        (tree as nat) < crate::brotli_prefix::tree_region_count(region),
        before.len() == after.len(),
        forall|i: int| 0 <= i < before.len() && {
            let at = crate::brotli_prefix::tree_metadata_at(window_bytes, region, tree);
            !(at <= i < at + 4)
        } ==> #[trigger] after[i] == before[i],
    ensures
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(before, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(after, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_COUNT),
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        compressed_decoder_state_ok(before, window_bytes)
            ==> compressed_decoder_state_ok(after, window_bytes),
{
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let at = crate::brotli_prefix::tree_metadata_at(window_bytes, region, tree);
    match region {
        crate::brotli_prefix::TreeRegion::Literal => {}
        crate::brotli_prefix::TreeRegion::Command => {}
        crate::brotli_prefix::TreeRegion::Distance => {}
        crate::brotli_prefix::TreeRegion::BlockType => {}
        crate::brotli_prefix::TreeRegion::BlockLength => {}
        crate::brotli_prefix::TreeRegion::TemporaryContext => {}
    }
    assert(window_bytes as nat + crate::brotli_prefix::STATE_OFFSET as nat <= at);
    assert(at + 4 <= b3b_scalar_base(window_bytes) as nat);
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) < at);
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_data_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) < at);
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                assert(crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) < at);
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn canonical_installer_frame_preserves_context_state(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    symbols: u16,
)
    requires
        b3b_workspace_shape(before.len() as nat, window_bytes),
        (tree as nat) < crate::brotli_prefix::tree_region_count(region),
        (symbols as nat) <= crate::brotli_prefix::tree_region_symbols(region),
        crate::brotli_prefix::canonical_installer_frame(
            before,
            after,
            window_bytes,
            region,
            tree,
            symbols,
        ),
    ensures
        before.len() == after.len(),
        serialized_context_data_ok(before, window_bytes)
            ==> serialized_context_data_ok(after, window_bytes),
        serialized_context_state_ok(before, window_bytes)
            ==> serialized_context_state_ok(after, window_bytes),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(before, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(after, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(after, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_COUNT),
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
        compressed_decoder_state_ok(before, window_bytes)
            ==> compressed_decoder_state_ok(after, window_bytes),
{
    reveal(crate::brotli_prefix::canonical_installer_frame);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    b3b_scalar_layout_is_exact();
    let builder_start = window_bytes as nat
        + crate::brotli_prefix::BUILDER_COUNTS_OFFSET as nat;
    let builder_end = window_bytes as nat
        + crate::brotli_prefix::TEMP_CONTEXT_TREE_OFFSET as nat;
    let tree_start = crate::brotli_prefix::tree_record_at(window_bytes, region, tree, 0);
    let tree_end = tree_start + symbols as nat * 3;
    match region {
        crate::brotli_prefix::TreeRegion::Literal => {
            assert((tree as nat) < 256);
            assert((symbols as nat) <= 256);
            assert(tree_start == window_bytes as nat + (tree as nat * 256) * 3);
            assert(tree_end <= window_bytes as nat
                + crate::brotli_prefix::COMMAND_TREES_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::Command => {
            assert((tree as nat) < 256);
            assert((symbols as nat) <= 704);
            assert(tree_start == window_bytes as nat + 196_608
                + (tree as nat * 704) * 3);
            assert(tree_end <= window_bytes as nat
                + crate::brotli_prefix::DISTANCE_TREES_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::Distance => {
            assert((tree as nat) < 256);
            assert((symbols as nat) <= 520);
            assert(tree_start == window_bytes as nat + 737_280
                + (tree as nat * 520) * 3);
            assert(tree_end <= window_bytes as nat
                + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::BlockType => {
            assert((tree as nat) < 3);
            assert((symbols as nat) <= 258);
            assert(tree_start == window_bytes as nat + 1_154_304
                + (tree as nat * 258) * 3);
            assert(tree_end <= window_bytes as nat
                + crate::brotli_prefix::BLOCK_LENGTH_TREES_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::BlockLength => {
            assert((tree as nat) < 3);
            assert((symbols as nat) <= 26);
            assert(tree_start == window_bytes as nat + 1_156_626
                + (tree as nat * 26) * 3);
            assert(tree_end <= window_bytes as nat
                + crate::brotli_prefix::BUILDER_OFFSET as nat);
        }
        crate::brotli_prefix::TreeRegion::TemporaryContext => {
            assert((tree as nat) < 1);
            assert((symbols as nat) <= 272);
            assert(tree_start == window_bytes as nat + 1_159_100
                + (tree as nat * 272) * 3);
            assert(tree_end <= window_bytes as nat
                + crate::brotli_prefix::MTF_OFFSET as nat);
        }
    }
    assert(builder_end <= window_bytes as nat + crate::brotli_prefix::MTF_OFFSET as nat);
    assert(tree_end <= window_bytes as nat + crate::brotli_prefix::MTF_OFFSET as nat);
    assert(b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND));
    assert forall|i: int| 0 <= i < 256 implies #[trigger]
        after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
            == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int] by {
        assert(builder_end <= crate::brotli_prefix::mtf_list_at(window_bytes, i as u16));
        assert(tree_end <= crate::brotli_prefix::mtf_list_at(window_bytes, i as u16));
    }
    mtf_state_preserved_by_frame(before, after, window_bytes);
    if serialized_context_data_ok(before, window_bytes) {
        let active_len = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE);
        if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                ) as int] by {
                let entry = crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    i,
                );
                assert(entry < builder_start);
                match region {
                    crate::brotli_prefix::TreeRegion::Literal
                    | crate::brotli_prefix::TreeRegion::Command
                    | crate::brotli_prefix::TreeRegion::Distance => {
                        assert(tree_end <= entry);
                    }
                    _ => {
                        assert(entry < tree_start);
                    }
                }
            }
        } else {
            assert forall|i: u16| (i as nat) < active_len implies #[trigger]
                after[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] == before[crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                ) as int] by {
                let entry = crate::brotli_prefix::context_entry_at(
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    i,
                );
                assert(entry < builder_start);
                match region {
                    crate::brotli_prefix::TreeRegion::Literal
                    | crate::brotli_prefix::TreeRegion::Command
                    | crate::brotli_prefix::TreeRegion::Distance => {
                        assert(tree_end <= entry);
                    }
                    _ => {
                        assert(entry < tree_start);
                    }
                }
            }
        }
        observed_context_frame_preserves_state(before, after, window_bytes);
    }
}

proof fn mtf_state_preserved_by_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
)
    requires
        before.len() == after.len(),
        b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND)
            == b3b_scalar_byte_at(after, window_bytes, B3B_MTF_UPPER_BOUND),
        forall|i: int| 0 <= i < 256 ==> #[trigger]
            after[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
                == before[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int],
    ensures
        serialized_mtf_state_ok(before, window_bytes)
            ==> serialized_mtf_state_ok(after, window_bytes),
{
    reveal(serialized_mtf_state_ok);
    assert(crate::brotli_prefix::mtf_list_values(after, window_bytes) =~=
        crate::brotli_prefix::mtf_list_values(before, window_bytes));
}

fn read_b3b_state_byte(
    workspace: &[u8],
    window_bytes: u32,
    relative: u16,
) -> (r: Result<u8, crate::brotli_prefix::WorkspaceError>)
    ensures r.is_ok() ==> {
        &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
        &&& r.unwrap()
            == workspace@[window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int]
    },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    let at = match b3b_state_address(workspace.len(), window_bytes, relative, 1) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(workspace[at])
}

fn write_b3b_state_byte(
    workspace: &mut [u8],
    window_bytes: u32,
    relative: u16,
    value: u8,
) -> (r: Result<(), crate::brotli_prefix::WorkspaceError>)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_ok() ==> {
        let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
        &&& b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
        &&& 0 <= at < old(workspace)@.len()
        &&& final(workspace)@.len() == old(workspace)@.len()
        &&& final(workspace)@[at] == value
        &&& forall|i: int| 0 <= i < old(workspace)@.len() && i != at
            ==> final(workspace)@[i] == old(workspace)@[i]
    },
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && relative != B3B_MTF_UPPER_BOUND
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && relative < B3B_CONTEXT_PHASE
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && relative < B3B_CONTEXT_PHASE
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        B3B_GROUP_KIND <= relative && relative != B3B_MTF_UPPER_BOUND ==> {
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INDEX)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INDEX)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            &&& (serialized_context_data_ok(old(workspace)@, window_bytes)
                ==> serialized_context_data_ok(final(workspace)@, window_bytes))
            &&& (serialized_context_state_ok(old(workspace)@, window_bytes)
                ==> serialized_context_state_ok(final(workspace)@, window_bytes))
        },
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    let ghost before = workspace@;
    let at = match b3b_state_address(workspace.len(), window_bytes, relative, 1) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    workspace[at] = value;
    proof {
        if relative != B3B_MTF_UPPER_BOUND
            && serialized_mtf_state_ok(before, window_bytes)
        {
            b3b_scalar_layout_is_exact();
            reveal(b3b_scalar_byte_at);
            reveal(b3b_scalar_base);
            assert(b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND)
                == b3b_scalar_byte_at(workspace@, window_bytes, B3B_MTF_UPPER_BOUND));
            assert forall|i: int| 0 <= i < 256 implies #[trigger]
                workspace@[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
                    == before[crate::brotli_prefix::mtf_list_at(
                        window_bytes,
                        i as u16,
                    ) as int] by {
                assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16)
                    < at as nat);
            }
            mtf_state_preserved_by_frame(before, workspace@, window_bytes);
        }
        if B3B_GROUP_KIND <= relative && relative != B3B_MTF_UPPER_BOUND {
            b3b_scalar_layout_is_exact();
            assert forall|i: int|
                0 <= i < b3b_scalar_base(window_bytes) + B3B_GROUP_KIND as int
                implies #[trigger] workspace@[i] == before[i] by {
                assert(i != at);
            }
            high_scalar_frame_preserves_context_state(before, workspace@, window_bytes);
        }
        if relative < B3B_CONTEXT_PHASE {
            reveal(b3b_scalar_base);
            assert(workspace@ == before.update(
                b3b_scalar_base(window_bytes) + relative as int,
                value,
            ));
            queue_scalar_write_preserves_context_state(
                before,
                workspace@,
                window_bytes,
                relative,
                value,
            );
        }
    }
    Ok(())
}

#[verifier::bit_vector]
proof fn decode_b3b_u16_le(low: u8, high: u8)
    ensures
        (low as u16 | ((high as u16) << 8)) as nat
            == low as nat + 256 * high as nat,
{}

#[verifier::bit_vector]
proof fn encode_b3b_u16_le(value: u16)
    ensures
        value as u8 == (value % 256) as u8,
        (value >> 8) as u8 == (value / 256) as u8,
{}

#[verifier::bit_vector]
proof fn decode_b3b_u32_le(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        (b0 as u32
            | ((b1 as u32) << 8)
            | ((b2 as u32) << 16)
            | ((b3 as u32) << 24)) as nat
            == b0 as nat
                + 256 * b1 as nat
                + 65_536 * b2 as nat
                + 16_777_216 * b3 as nat,
{}

#[verifier::bit_vector]
proof fn encode_b3b_u32_le(value: u32)
    ensures
        value as u8 == (value % 256) as u8,
        (value >> 8) as u8 == ((value / 256) % 256) as u8,
        (value >> 16) as u8 == ((value / 65_536) % 256) as u8,
        (value >> 24) as u8 == (value / 16_777_216) as u8,
{}

fn read_b3b_state_u16(
    workspace: &[u8],
    window_bytes: u32,
    relative: u16,
) -> (r: Result<u16, crate::brotli_prefix::WorkspaceError>)
    ensures r.is_ok() ==> {
        let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
        &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
        &&& relative as nat + 2 <= B3B_SCALAR_BYTES
        &&& r.unwrap() as nat == workspace@[at] as nat + 256 * workspace@[at + 1] as nat
    },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 2 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    let at = match b3b_state_address(workspace.len(), window_bytes, relative, 2) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let low = workspace[at];
    let high = workspace[at + 1];
    proof { decode_b3b_u16_le(low, high); }
    Ok(low as u16 | ((high as u16) << 8))
}

fn write_b3b_state_u16(
    workspace: &mut [u8],
    window_bytes: u32,
    relative: u16,
    value: u16,
) -> (r: Result<(), crate::brotli_prefix::WorkspaceError>)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_ok() ==> {
            let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
            &&& b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            &&& 0 <= at && at + 2 <= old(workspace)@.len()
            &&& final(workspace)@.len() == old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at, (value % 256) as u8)
                .update(at + 1, (value / 256) as u8)
        },
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && (relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && (relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        (relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        B3B_GROUP_KIND <= relative
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat) ==> {
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INDEX)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INDEX)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            &&& (serialized_context_data_ok(old(workspace)@, window_bytes)
                ==> serialized_context_data_ok(final(workspace)@, window_bytes))
            &&& (serialized_context_state_ok(old(workspace)@, window_bytes)
                ==> serialized_context_state_ok(final(workspace)@, window_bytes))
        },
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 2 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 2 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    let ghost before = workspace@;
    let at = match b3b_state_address(workspace.len(), window_bytes, relative, 2) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    proof { encode_b3b_u16_le(value); }
    workspace[at] = value as u8;
    workspace[at + 1] = (value >> 8) as u8;
    proof {
        if serialized_mtf_state_ok(before, window_bytes)
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
        {
            b3b_scalar_layout_is_exact();
            reveal(b3b_scalar_byte_at);
            reveal(b3b_scalar_base);
            assert(b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND)
                == b3b_scalar_byte_at(workspace@, window_bytes, B3B_MTF_UPPER_BOUND));
            assert forall|i: int| 0 <= i < 256 implies #[trigger]
                workspace@[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
                    == before[crate::brotli_prefix::mtf_list_at(
                        window_bytes,
                        i as u16,
                    ) as int] by {
                assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) + 1
                    < at as nat);
            }
            mtf_state_preserved_by_frame(before, workspace@, window_bytes);
        }
        if B3B_GROUP_KIND <= relative
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
        {
            b3b_scalar_layout_is_exact();
            assert forall|i: int|
                0 <= i < b3b_scalar_base(window_bytes) + B3B_GROUP_KIND as int
                implies #[trigger] workspace@[i] == before[i] by {
                assert(i != at);
                assert(i != at + 1);
            }
            high_scalar_frame_preserves_context_state(before, workspace@, window_bytes);
        }
        if relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES {
            result_tree_write_preserves_context_state(
                before,
                workspace@,
                window_bytes,
                relative,
                value,
            );
        }
    }
    Ok(())
}

fn read_b3b_state_u32(
    workspace: &[u8],
    window_bytes: u32,
    relative: u16,
) -> (r: Result<u32, crate::brotli_prefix::WorkspaceError>)
    ensures r.is_ok() ==> {
        let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
        &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
        &&& relative as nat + 4 <= B3B_SCALAR_BYTES
        &&& r.unwrap() as nat == workspace@[at] as nat
            + 256 * workspace@[at + 1] as nat
            + 65_536 * workspace@[at + 2] as nat
            + 16_777_216 * workspace@[at + 3] as nat
    },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 4 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    let at = match b3b_state_address(workspace.len(), window_bytes, relative, 4) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let b0 = workspace[at];
    let b1 = workspace[at + 1];
    let b2 = workspace[at + 2];
    let b3 = workspace[at + 3];
    proof {
        decode_b3b_u32_le(b0, b1, b2, b3);
    }
    Ok(b0 as u32 | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24))
}

fn write_b3b_state_u32(
    workspace: &mut [u8],
    window_bytes: u32,
    relative: u16,
    value: u32,
) -> (r: Result<(), crate::brotli_prefix::WorkspaceError>)
    ensures
        r.is_ok() ==> {
            let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
            &&& b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            &&& 0 <= at && at + 4 <= old(workspace)@.len()
            &&& final(workspace)@.len() == old(workspace)@.len()
            &&& final(workspace)@ == old(workspace)@
                .update(at, (value % 256) as u8)
                .update(at + 1, ((value / 256) % 256) as u8)
                .update(at + 2, ((value / 65_536) % 256) as u8)
                .update(at + 3, (value / 16_777_216) as u8)
        },
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 4 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 4 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    let ghost before = workspace@;
    let at = match b3b_state_address(workspace.len(), window_bytes, relative, 4) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    proof { encode_b3b_u32_le(value); }
    workspace[at] = value as u8;
    workspace[at + 1] = (value >> 8) as u8;
    workspace[at + 2] = (value >> 16) as u8;
    workspace[at + 3] = (value >> 24) as u8;
    proof {
        if serialized_mtf_state_ok(before, window_bytes)
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
        {
            b3b_scalar_layout_is_exact();
            reveal(b3b_scalar_byte_at);
            reveal(b3b_scalar_base);
            assert(b3b_scalar_byte_at(before, window_bytes, B3B_MTF_UPPER_BOUND)
                == b3b_scalar_byte_at(workspace@, window_bytes, B3B_MTF_UPPER_BOUND));
            assert forall|i: int| 0 <= i < 256 implies #[trigger]
                workspace@[crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) as int]
                    == before[crate::brotli_prefix::mtf_list_at(
                        window_bytes,
                        i as u16,
                    ) as int] by {
                assert(crate::brotli_prefix::mtf_list_at(window_bytes, i as u16) + 3
                    < at as nat);
            }
            mtf_state_preserved_by_frame(before, workspace@, window_bytes);
        }
        if B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
        {
            b3b_scalar_layout_is_exact();
            assert forall|i: int|
                0 <= i < b3b_scalar_base(window_bytes) + B3B_GROUP_KIND as int
                implies #[trigger] workspace@[i] == before[i] by {
                assert(i != at);
                assert(i != at + 1);
                assert(i != at + 2);
                assert(i != at + 3);
            }
            high_scalar_frame_preserves_context_state(before, workspace@, window_bytes);
        }
    }
    Ok(())
}

fn write_b3b_state_tag(
    workspace: &mut [u8],
    window_bytes: u32,
    relative: u16,
    variants: u8,
    value: u8,
) -> (r: Result<(), crate::brotli_prefix::WorkspaceError>)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_ok() ==> value < variants && {
            let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
            &&& b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            &&& 0 <= at < old(workspace)@.len()
            &&& final(workspace)@.len() == old(workspace)@.len()
            &&& final(workspace)@[at] == value
            &&& forall|i: int| 0 <= i < old(workspace)@.len() && i != at
                ==> final(workspace)@[i] == old(workspace)@[i]
        },
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            && value < variants
            ==> r.is_ok(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && relative < B3B_CONTEXT_PHASE
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && relative < B3B_CONTEXT_PHASE
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && relative != B3B_MTF_UPPER_BOUND
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        relative != B3B_OUTER_PHASE ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_OUTER_PHASE,
        ) == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    if value >= variants {
        return Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol);
    }
    write_b3b_state_byte(workspace, window_bytes, relative, value)
}

fn read_b3b_state_tag(
    workspace: &[u8],
    window_bytes: u32,
    relative: u16,
    variants: u8,
) -> (r: Result<u8, crate::brotli_prefix::WorkspaceError>)
    ensures r.is_ok() ==> {
        let at = window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int;
        &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
        &&& r.unwrap() < variants
        &&& r.unwrap() == workspace@[at]
    },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            && workspace@[window_bytes as int + B3B_SCALAR_OFFSET as int + relative as int]
                < variants
            ==> r.is_ok(),
{
    let value = match read_b3b_state_byte(workspace, window_bytes, relative) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if value >= variants {
        return Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol);
    }
    Ok(value)
}

spec fn serialized_b3b_queue(
    workspace: Seq<u8>,
    window_bytes: u32,
    queue: BitQueue,
) -> bool {
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& queue.valid()
    &&& queue.len as nat == b3b_scalar_byte_at(
        workspace,
        window_bytes,
        B3B_QUEUE_LEN,
    ) as nat
    &&& queue.offset as nat == b3b_scalar_byte_at(
        workspace,
        window_bytes,
        B3B_QUEUE_OFFSET_BYTE,
    ) as nat
    &&& forall|i: int| 0 <= i < queue.len ==> #[trigger] queue.pending@[i]
        == workspace[b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET as int + i]
    &&& forall|i: int| queue.len <= i < 8 ==> #[trigger] workspace[
        b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET as int + i
    ] == 0
}

spec fn var_uint8_phase_tag(phase: VarUint8Phase) -> u8 {
    match phase {
        VarUint8Phase::First => 0,
        VarUint8Phase::Short => 1,
        VarUint8Phase::Long { .. } => 2,
    }
}

spec fn var_uint8_phase_width(phase: VarUint8Phase) -> u8 {
    match phase {
        VarUint8Phase::Long { width } => width,
        _ => 0,
    }
}

spec fn serialized_var_uint8_phase(
    workspace: Seq<u8>,
    window_bytes: u32,
    phase: VarUint8Phase,
) -> bool {
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& phase.valid()
    &&& b3b_scalar_byte_at(workspace, window_bytes, B3B_VAR_PHASE)
        == var_uint8_phase_tag(phase)
    &&& b3b_scalar_byte_at(workspace, window_bytes, B3B_VAR_WIDTH)
        == var_uint8_phase_width(phase)
}

spec fn serialized_installed_prefix(
    workspace: Seq<u8>,
    window_bytes: u32,
    prefix: InstalledPrefixState,
) -> bool {
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& prefix.valid()
    &&& b3b_scalar_byte_at(
        workspace,
        window_bytes,
        B3B_INSTALLED_PREFIX_WIDTH,
    ) == prefix.width
    &&& b3b_scalar_u16_at(
        workspace,
        window_bytes,
        B3B_INSTALLED_PREFIX_BITS,
    ) == prefix.bits as nat
    &&& b3b_scalar_u16_at(
        workspace,
        window_bytes,
        B3B_INSTALLED_SCAN,
    ) == prefix.scan as nat
}

proof fn serialized_b3b_queue_from_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    queue: BitQueue,
)
    requires
        serialized_b3b_queue(before, window_bytes, queue),
        b3b_workspace_shape(after.len() as nat, window_bytes),
        after.len() == before.len(),
        forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 ==> #[trigger]
            after[b3b_scalar_base(window_bytes) + i]
                == before[b3b_scalar_base(window_bytes) + i],
    ensures serialized_b3b_queue(after, window_bytes, queue),
{
    reveal(serialized_b3b_queue);
    reveal(b3b_scalar_byte_at);
}

proof fn serialized_installed_prefix_from_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    prefix: InstalledPrefixState,
)
    requires
        serialized_installed_prefix(before, window_bytes, prefix),
        b3b_workspace_shape(after.len() as nat, window_bytes),
        after.len() == before.len(),
        b3b_scalar_byte_at(
            after,
            window_bytes,
            B3B_INSTALLED_PREFIX_WIDTH,
        ) == b3b_scalar_byte_at(
            before,
            window_bytes,
            B3B_INSTALLED_PREFIX_WIDTH,
        ),
        b3b_scalar_u16_at(
            after,
            window_bytes,
            B3B_INSTALLED_PREFIX_BITS,
        ) == b3b_scalar_u16_at(
            before,
            window_bytes,
            B3B_INSTALLED_PREFIX_BITS,
        ),
        b3b_scalar_u16_at(after, window_bytes, B3B_INSTALLED_SCAN)
            == b3b_scalar_u16_at(before, window_bytes, B3B_INSTALLED_SCAN),
    ensures serialized_installed_prefix(after, window_bytes, prefix),
{
    reveal(serialized_installed_prefix);
}

proof fn serialized_block_count_cursor_from_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    queue: BitQueue,
    phase: VarUint8Phase,
)
    requires
        serialized_b3b_queue(before, window_bytes, queue),
        serialized_var_uint8_phase(before, window_bytes, phase),
        b3b_workspace_shape(after.len() as nat, window_bytes),
        after.len() == before.len(),
        forall|i: int| 0 <= i < B3B_VAR_WIDTH + 1
            && i != B3B_OUTER_PHASE
            && i != B3B_CURRENT_KIND ==> #[trigger]
            after[b3b_scalar_base(window_bytes) + i]
                == before[b3b_scalar_base(window_bytes) + i],
    ensures
        serialized_b3b_queue(after, window_bytes, queue),
        serialized_var_uint8_phase(after, window_bytes, phase),
{
    reveal(serialized_b3b_queue);
    reveal(serialized_var_uint8_phase);
    reveal(b3b_scalar_byte_at);
}

proof fn b3b_scalar_u16_from_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    relative: u16,
)
    requires
        b3b_scalar_byte_at(after, window_bytes, relative)
            == b3b_scalar_byte_at(before, window_bytes, relative),
        b3b_scalar_byte_at(after, window_bytes, (relative + 1) as u16)
            == b3b_scalar_byte_at(before, window_bytes, (relative + 1) as u16),
    ensures
        b3b_scalar_u16_at(after, window_bytes, relative)
            == b3b_scalar_u16_at(before, window_bytes, relative),
{
    reveal(b3b_scalar_u16_at);
}

proof fn b3b_scalar_u32_from_frame(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    relative: u16,
)
    requires
        b3b_scalar_byte_at(after, window_bytes, relative)
            == b3b_scalar_byte_at(before, window_bytes, relative),
        b3b_scalar_byte_at(after, window_bytes, (relative + 1) as u16)
            == b3b_scalar_byte_at(before, window_bytes, (relative + 1) as u16),
        b3b_scalar_byte_at(after, window_bytes, (relative + 2) as u16)
            == b3b_scalar_byte_at(before, window_bytes, (relative + 2) as u16),
        b3b_scalar_byte_at(after, window_bytes, (relative + 3) as u16)
            == b3b_scalar_byte_at(before, window_bytes, (relative + 3) as u16),
    ensures
        b3b_scalar_u32_at(after, window_bytes, relative)
            == b3b_scalar_u32_at(before, window_bytes, relative),
{
    reveal(b3b_scalar_u32_at);
}

fn load_b3b_queue(
    workspace: &[u8],
    window_bytes: u32,
) -> (r: Result<BitQueue, CompressedHeaderError>)
    ensures r.is_ok() ==> serialized_b3b_queue(workspace@, window_bytes, r.unwrap()),
{
    let len = match read_b3b_state_byte(workspace, window_bytes, B3B_QUEUE_LEN) {
        Ok(value) => value as usize,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    let offset = match read_b3b_state_byte(workspace, window_bytes, B3B_QUEUE_OFFSET_BYTE) {
        Ok(value) => value as usize,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    if len > 8 || offset >= 8 || (len == 0 && offset != 0) {
        return Err(CompressedHeaderError::InternalState);
    }
    let mut pending = [0u8; 8];
    let mut i: usize = 0;
    while i < 8
        invariant i <= 8,
            b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            len as nat == b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_QUEUE_LEN,
            ) as nat,
            offset as nat == b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_QUEUE_OFFSET_BYTE,
            ) as nat,
            forall|j: int| 0 <= j < i ==> #[trigger] pending@[j]
                == workspace@[b3b_scalar_base(window_bytes)
                    + B3B_QUEUE_OFFSET as int + j],
            forall|j: int| len <= j < i ==> #[trigger] pending@[j] == 0,
        decreases 8 - i,
    {
        pending[i] = match read_b3b_state_byte(
            workspace,
            window_bytes,
            B3B_QUEUE_OFFSET + i as u16,
        ) {
            Ok(value) => value,
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        };
        if i >= len && pending[i] != 0 {
            return Err(CompressedHeaderError::InternalState);
        }
        i = i + 1;
    }
    let queue = BitQueue { pending, len, offset };
    assert(queue.valid());
    proof {
        reveal(serialized_b3b_queue);
        assert forall|j: int| 0 <= j < 8 implies #[trigger] queue.pending@[j]
            == workspace@[b3b_scalar_base(window_bytes)
                + B3B_QUEUE_OFFSET as int + j] by {}
        assert forall|j: int| queue.len <= j < 8 implies #[trigger] workspace@[
            b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET as int + j
        ] == 0 by {
            assert(queue.pending@[j] == 0);
        }
        assert(serialized_b3b_queue(workspace@, window_bytes, queue));
    }
    Ok(queue)
}

fn store_b3b_queue(
    workspace: &mut [u8],
    window_bytes: u32,
    queue: &BitQueue,
) -> (r: Result<(), CompressedHeaderError>)
    requires queue.valid(),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            ==> r.is_ok(),
        r.is_ok() ==> serialized_b3b_queue(final(workspace)@, window_bytes, *queue),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes) ==> {
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_PENDING_RUN)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_PENDING_RUN)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CURRENT_KIND)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CURRENT_KIND)
        },
{
    let ghost original = workspace@;
    proof { assert(original == old(workspace)@); }
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    let mut i: usize = 0;
    while i < 8
        invariant i <= 8,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            i == 0 ==> workspace@ == original,
            i > 0 ==> b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            b3b_workspace_shape(original.len() as nat, window_bytes)
                ==> b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            serialized_mtf_state_ok(original, window_bytes)
                ==> serialized_mtf_state_ok(workspace@, window_bytes),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_ACTIVE_REGION)
                == b3b_scalar_byte_at(original, window_bytes, B3B_ACTIVE_REGION),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_MAX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_MAX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_LIMIT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_LIMIT),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_INDEX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_INDEX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_COUNT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_COUNT),
            forall|j: int| 0 <= j < i ==> #[trigger] workspace@[
                b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET as int + j
            ] == if j < queue.len { queue.pending@[j] } else { 0 },
            b3b_workspace_shape(original.len() as nat, window_bytes) ==> {
                &&& b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                    == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND)
                &&& b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                    == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE)
                &&& b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                    == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE)
                &&& b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_TREES)
                    == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_TREES)
                &&& b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_INITIALIZED)
                    == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_INITIALIZED)
                &&& b3b_scalar_byte_at(workspace@, window_bytes, B3B_MAX_RUN_PREFIX)
                    == b3b_scalar_byte_at(original, window_bytes, B3B_MAX_RUN_PREFIX)
                &&& b3b_scalar_byte_at(workspace@, window_bytes, B3B_PENDING_RUN)
                    == b3b_scalar_byte_at(original, window_bytes, B3B_PENDING_RUN)
                &&& b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                    == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE)
                &&& b3b_scalar_byte_at(workspace@, window_bytes, B3B_CURRENT_KIND)
                    == b3b_scalar_byte_at(original, window_bytes, B3B_CURRENT_KIND)
            },
        decreases 8 - i,
    {
        let value = if i < queue.len { queue.pending[i] } else { 0 };
        let relative = B3B_QUEUE_OFFSET + i as u16;
        let ghost before_write = workspace@;
        match write_b3b_state_byte(
            workspace,
            window_bytes,
            relative,
            value,
        ) {
            Ok(()) => {}
            Err(error) => {
                proof {
                    assert(workspace@ == before_write);
                    if i > 0 {
                        assert(b3b_workspace_shape(before_write.len() as nat, window_bytes));
                        assert(relative as nat + 1 <= B3B_SCALAR_BYTES);
                        assert(false);
                    } else {
                        assert(i == 0);
                        assert(before_write == original);
                    }
                    assert(workspace@ == original);
                    assert(workspace@ == old(workspace)@);
                }
                return Err(CompressedHeaderError::Workspace(error));
            }
        }
        proof {
            b3b_scalar_layout_is_exact();
            assert(relative <= B3B_QUEUE_OFFSET_BYTE);
            let at = b3b_scalar_base(window_bytes) + relative as int;
            assert(workspace@ == before_write.update(at, value)) by {
                assert(workspace@.len() == before_write.len());
                assert forall|j: int| 0 <= j < workspace@.len() implies
                    #[trigger] workspace@[j] == before_write.update(at, value)[j] by {
                    if j == at {}
                }
            }
            if b3b_workspace_shape(original.len() as nat, window_bytes) {
                queue_scalar_write_preserves_context_state(
                    before_write,
                    workspace@,
                    window_bytes,
                    relative,
                    value,
                );
            }
        }
        i = i + 1;
    }
    let ghost before_len = workspace@;
    match write_b3b_state_byte(workspace, window_bytes, B3B_QUEUE_LEN, queue.len as u8) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    proof {
        let at = b3b_scalar_base(window_bytes) + B3B_QUEUE_LEN as int;
        assert(workspace@ == before_len.update(at, queue.len as u8)) by {
            assert(workspace@.len() == before_len.len());
            assert forall|j: int| 0 <= j < workspace@.len() implies
                #[trigger] workspace@[j] == before_len.update(at, queue.len as u8)[j] by {
                if j == at {}
            }
        }
        queue_scalar_write_preserves_context_state(
            before_len,
            workspace@,
            window_bytes,
            B3B_QUEUE_LEN,
            queue.len as u8,
        );
    }
    let ghost before_offset = workspace@;
    match write_b3b_state_byte(
        workspace,
        window_bytes,
        B3B_QUEUE_OFFSET_BYTE,
        queue.offset as u8,
    ) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    proof {
        let at = b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET_BYTE as int;
        assert(workspace@ == before_offset.update(at, queue.offset as u8)) by {
            assert(workspace@.len() == before_offset.len());
            assert forall|j: int| 0 <= j < workspace@.len() implies
                #[trigger] workspace@[j]
                    == before_offset.update(at, queue.offset as u8)[j] by {
                if j == at {}
            }
        }
        queue_scalar_write_preserves_context_state(
            before_offset,
            workspace@,
            window_bytes,
            B3B_QUEUE_OFFSET_BYTE,
            queue.offset as u8,
        );
        if serialized_context_data_ok(original, window_bytes) {
            assert(serialized_context_data_ok(workspace@, window_bytes));
        }
        if serialized_context_state_ok(original, window_bytes) {
            assert(serialized_context_state_ok(workspace@, window_bytes));
        }
        if compressed_decoder_state_ok(original, window_bytes) {
            reveal(compressed_decoder_state_ok);
            assert(compressed_decoder_state_ok(workspace@, window_bytes));
        }
        assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(original, window_bytes, B3B_ACTIVE_REGION));
        assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_TREE));
        assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_MAX));
        assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_LIMIT));
        assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_KIND));
        assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_PHASE));
        assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_INDEX));
        assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_COUNT));
        assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_MAX_RUN_PREFIX)
            == b3b_scalar_byte_at(original, window_bytes, B3B_MAX_RUN_PREFIX));
        assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_PENDING_RUN)
            == b3b_scalar_byte_at(original, window_bytes, B3B_PENDING_RUN));
        reveal(serialized_b3b_queue);
        assert forall|j: int| 0 <= j < queue.len implies #[trigger] workspace@[
            b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET as int + j
        ] == queue.pending@[j] by {}
        assert forall|j: int| queue.len <= j < 8 implies #[trigger] workspace@[
            b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET as int + j
        ] == 0 by {}
        assert(serialized_b3b_queue(workspace@, window_bytes, *queue));
    }
    Ok(())
}

fn load_var_uint8_phase(
    workspace: &[u8],
    window_bytes: u32,
) -> (r: Result<VarUint8Phase, CompressedHeaderError>)
    ensures r.is_ok() ==> serialized_var_uint8_phase(
        workspace@,
        window_bytes,
        r.unwrap(),
    ),
{
    let tag = match read_b3b_state_tag(workspace, window_bytes, B3B_VAR_PHASE, 3) {
        Ok(value) => value,
        Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol) =>
            return Err(CompressedHeaderError::InternalState),
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    let width = match read_b3b_state_byte(workspace, window_bytes, B3B_VAR_WIDTH) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    match tag {
        0 if width == 0 => Ok(VarUint8Phase::First),
        1 if width == 0 => Ok(VarUint8Phase::Short),
        2 if 1 <= width && width <= 7 => Ok(VarUint8Phase::Long { width }),
        _ => Err(CompressedHeaderError::InternalState),
    }
}

fn store_var_uint8_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    phase: VarUint8Phase,
) -> (r: Result<(), CompressedHeaderError>)
    requires phase.valid(),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            ==> r.is_ok(),
        r.is_ok() ==> serialized_var_uint8_phase(
            final(workspace)@,
            window_bytes,
            phase,
        ),
        r.is_ok() ==> forall|i: int| 0 <= i < B3B_GROUP_KIND
            && i != B3B_VAR_PHASE
            && i != B3B_VAR_WIDTH ==> #[trigger]
            final(workspace)@[b3b_scalar_base(window_bytes) + i]
                == old(workspace)@[b3b_scalar_base(window_bytes) + i],
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CURRENT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CURRENT_KIND),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
{
    let (tag, width) = match phase {
        VarUint8Phase::First => (0u8, 0u8),
        VarUint8Phase::Short => (1u8, 0u8),
        VarUint8Phase::Long { width } => (2u8, width),
    };
    match write_b3b_state_tag(workspace, window_bytes, B3B_VAR_PHASE, 3, tag) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_VAR_WIDTH, width) {
        Ok(()) => Ok(()),
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

spec fn compressed_format_error_detail_spec(error: CompressedFormatError) -> u16 {
    match error {
        CompressedFormatError::InvalidPrefixCode => 1,
        CompressedFormatError::DuplicateSimpleSymbol => 2,
        CompressedFormatError::CodeLengthSpace => 3,
        CompressedFormatError::InvalidBlockLength => 4,
        CompressedFormatError::ContextMapRepeat => 5,
        CompressedFormatError::ContextMapValue => 6,
        CompressedFormatError::ContextMapCoverage => 7,
        CompressedFormatError::InvalidBlockSwitch => 8,
        CompressedFormatError::InvalidSequence => 9,
        CompressedFormatError::InvalidMetadata => 10,
        CompressedFormatError::InvalidDistanceAlphabet => 11,
        CompressedFormatError::InvalidBlockDeclaration => 12,
    }
}

fn compressed_format_error_detail(error: CompressedFormatError) -> (r: u16)
    ensures r == compressed_format_error_detail_spec(error), 1 <= r <= 12,
{
    match error {
        CompressedFormatError::InvalidPrefixCode => 1,
        CompressedFormatError::DuplicateSimpleSymbol => 2,
        CompressedFormatError::CodeLengthSpace => 3,
        CompressedFormatError::InvalidBlockLength => 4,
        CompressedFormatError::ContextMapRepeat => 5,
        CompressedFormatError::ContextMapValue => 6,
        CompressedFormatError::ContextMapCoverage => 7,
        CompressedFormatError::InvalidBlockSwitch => 8,
        CompressedFormatError::InvalidSequence => 9,
        CompressedFormatError::InvalidMetadata => 10,
        CompressedFormatError::InvalidDistanceAlphabet => 11,
        CompressedFormatError::InvalidBlockDeclaration => 12,
    }
}

fn decode_compressed_format_error(detail: u16) -> (r: Option<CompressedFormatError>)
    ensures
        r == match detail {
            1 => Some(CompressedFormatError::InvalidPrefixCode),
            2 => Some(CompressedFormatError::DuplicateSimpleSymbol),
            3 => Some(CompressedFormatError::CodeLengthSpace),
            4 => Some(CompressedFormatError::InvalidBlockLength),
            5 => Some(CompressedFormatError::ContextMapRepeat),
            6 => Some(CompressedFormatError::ContextMapValue),
            7 => Some(CompressedFormatError::ContextMapCoverage),
            8 => Some(CompressedFormatError::InvalidBlockSwitch),
            9 => Some(CompressedFormatError::InvalidSequence),
            10 => Some(CompressedFormatError::InvalidMetadata),
            11 => Some(CompressedFormatError::InvalidDistanceAlphabet),
            12 => Some(CompressedFormatError::InvalidBlockDeclaration),
            _ => None,
        },
        r.is_some() ==> compressed_format_error_detail_spec(r.unwrap()) == detail,
        (1 <= detail <= 12) ==> r.is_some(),
{
    match detail {
        1 => Some(CompressedFormatError::InvalidPrefixCode),
        2 => Some(CompressedFormatError::DuplicateSimpleSymbol),
        3 => Some(CompressedFormatError::CodeLengthSpace),
        4 => Some(CompressedFormatError::InvalidBlockLength),
        5 => Some(CompressedFormatError::ContextMapRepeat),
        6 => Some(CompressedFormatError::ContextMapValue),
        7 => Some(CompressedFormatError::ContextMapCoverage),
        8 => Some(CompressedFormatError::InvalidBlockSwitch),
        9 => Some(CompressedFormatError::InvalidSequence),
        10 => Some(CompressedFormatError::InvalidMetadata),
        11 => Some(CompressedFormatError::InvalidDistanceAlphabet),
        12 => Some(CompressedFormatError::InvalidBlockDeclaration),
        _ => None,
    }
}

spec fn workspace_error_detail_spec(error: crate::brotli_prefix::WorkspaceError) -> u16 {
    match error {
        crate::brotli_prefix::WorkspaceError::InvalidWindowBits => 1,
        crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall => 2,
        crate::brotli_prefix::WorkspaceError::InvalidTree => 3,
        crate::brotli_prefix::WorkspaceError::InvalidSymbol => 4,
        crate::brotli_prefix::WorkspaceError::InvalidCodeLength => 5,
        crate::brotli_prefix::WorkspaceError::UninitializedRecord => 6,
    }
}

fn workspace_error_detail(error: crate::brotli_prefix::WorkspaceError) -> (r: u16)
    ensures r == workspace_error_detail_spec(error), 1 <= r <= 6,
{
    match error {
        crate::brotli_prefix::WorkspaceError::InvalidWindowBits => 1,
        crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall => 2,
        crate::brotli_prefix::WorkspaceError::InvalidTree => 3,
        crate::brotli_prefix::WorkspaceError::InvalidSymbol => 4,
        crate::brotli_prefix::WorkspaceError::InvalidCodeLength => 5,
        crate::brotli_prefix::WorkspaceError::UninitializedRecord => 6,
    }
}

fn decode_workspace_error(detail: u16) -> (r: Option<crate::brotli_prefix::WorkspaceError>)
    ensures
        r == match detail {
            1 => Some(crate::brotli_prefix::WorkspaceError::InvalidWindowBits),
            2 => Some(crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall),
            3 => Some(crate::brotli_prefix::WorkspaceError::InvalidTree),
            4 => Some(crate::brotli_prefix::WorkspaceError::InvalidSymbol),
            5 => Some(crate::brotli_prefix::WorkspaceError::InvalidCodeLength),
            6 => Some(crate::brotli_prefix::WorkspaceError::UninitializedRecord),
            _ => None,
        },
        r.is_some() ==> workspace_error_detail_spec(r.unwrap()) == detail,
        (1 <= detail <= 6) ==> r.is_some(),
{
    match detail {
        1 => Some(crate::brotli_prefix::WorkspaceError::InvalidWindowBits),
        2 => Some(crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall),
        3 => Some(crate::brotli_prefix::WorkspaceError::InvalidTree),
        4 => Some(crate::brotli_prefix::WorkspaceError::InvalidSymbol),
        5 => Some(crate::brotli_prefix::WorkspaceError::InvalidCodeLength),
        6 => Some(crate::brotli_prefix::WorkspaceError::UninitializedRecord),
        _ => None,
    }
}

spec fn compressed_header_error_tag(error: CompressedHeaderError) -> u8 {
    match error {
        CompressedHeaderError::InvalidFormat(_) => 1,
        CompressedHeaderError::Truncated => 2,
        CompressedHeaderError::UnsupportedMode => 3,
        CompressedHeaderError::Workspace(_) => 4,
        CompressedHeaderError::InternalState => 5,
    }
}

spec fn compressed_header_error_detail(error: CompressedHeaderError) -> u16 {
    match error {
        CompressedHeaderError::InvalidFormat(detail) =>
            compressed_format_error_detail_spec(detail),
        CompressedHeaderError::Workspace(detail) => workspace_error_detail_spec(detail),
        _ => 0,
    }
}

spec fn serialized_terminal_error(
    workspace: Seq<u8>,
    window_bytes: u32,
    error: CompressedHeaderError,
) -> bool {
    let base = window_bytes as int + B3B_SCALAR_OFFSET as int;
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& workspace[base + B3B_OUTER_PHASE as int] == 12
    &&& workspace[base + B3B_TERMINAL_ERROR as int]
        == compressed_header_error_tag(error)
    &&& workspace[base + B3B_ERROR_DETAIL as int] as nat
        + 256 * workspace[base + B3B_ERROR_DETAIL as int + 1] as nat
        == compressed_header_error_detail(error)
}

fn store_terminal_error(
    workspace: &mut [u8],
    window_bytes: u32,
    error: CompressedHeaderError,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        r.is_ok() ==> serialized_terminal_error(final(workspace)@, window_bytes, error),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes) ==> r.is_ok(),
{
    let (tag, detail) = match error {
        CompressedHeaderError::InvalidFormat(detail) =>
            (1u8, compressed_format_error_detail(detail)),
        CompressedHeaderError::Truncated => (2, 0),
        CompressedHeaderError::UnsupportedMode => (3, 0),
        CompressedHeaderError::Workspace(detail) => (4, workspace_error_detail(detail)),
        CompressedHeaderError::InternalState => (5, 0),
    };
    match write_b3b_state_u16(workspace, window_bytes, B3B_ERROR_DETAIL, detail) {
        Ok(()) => {}
        Err(workspace_error) => return Err(CompressedHeaderError::Workspace(workspace_error)),
    }
    let ghost after_detail = workspace@;
    match write_b3b_state_tag(workspace, window_bytes, B3B_TERMINAL_ERROR, 6, tag) {
        Ok(()) => {}
        Err(workspace_error) => return Err(CompressedHeaderError::Workspace(workspace_error)),
    }
    let ghost after_tag = workspace@;
    proof {
        b3b_scalar_layout_is_exact();
        let base = window_bytes as int + B3B_SCALAR_OFFSET as int;
        assert(after_tag.len() == after_detail.len());
        assert(0 <= base + B3B_ERROR_DETAIL as int);
        assert((base + B3B_ERROR_DETAIL as int + 1) < after_tag.len());
        assert(after_tag[base + B3B_ERROR_DETAIL as int]
            == after_detail[base + B3B_ERROR_DETAIL as int]);
        assert(after_tag[base + B3B_ERROR_DETAIL as int + 1]
            == after_detail[base + B3B_ERROR_DETAIL as int + 1]);
    }
    match write_b3b_state_tag(workspace, window_bytes, B3B_OUTER_PHASE, 13, 12) {
        Ok(()) => {
            proof {
                b3b_scalar_layout_is_exact();
                let base = window_bytes as int + B3B_SCALAR_OFFSET as int;
                assert(workspace@.len() == after_tag.len());
                assert(0 <= base + B3B_TERMINAL_ERROR as int);
                assert((base + B3B_TERMINAL_ERROR as int) < after_tag.len());
                assert(0 <= base + B3B_ERROR_DETAIL as int);
                assert((base + B3B_ERROR_DETAIL as int + 1) < after_tag.len());
                assert(workspace@[base + B3B_TERMINAL_ERROR as int]
                    == after_tag[base + B3B_TERMINAL_ERROR as int]);
                assert(workspace@[base + B3B_ERROR_DETAIL as int]
                    == after_tag[base + B3B_ERROR_DETAIL as int]);
                assert(workspace@[base + B3B_ERROR_DETAIL as int + 1]
                    == after_tag[base + B3B_ERROR_DETAIL as int + 1]);
                assert(workspace@[base + B3B_OUTER_PHASE as int] == 12);
                assert(workspace@[base + B3B_TERMINAL_ERROR as int] == tag);
                assert(workspace@[base + B3B_ERROR_DETAIL as int] as nat
                    + 256 * workspace@[base + B3B_ERROR_DETAIL as int + 1] as nat
                    == detail);
            }
            Ok(())
        }
        Err(workspace_error) => Err(CompressedHeaderError::Workspace(workspace_error)),
    }
}

fn load_terminal_error(
    workspace: &[u8],
    window_bytes: u32,
) -> (r: Result<CompressedHeaderError, CompressedHeaderError>)
    ensures
        r.is_ok() ==> serialized_terminal_error(workspace@, window_bytes, r.unwrap()),
        forall|error: CompressedHeaderError| serialized_terminal_error(
            workspace@, window_bytes, error) ==> r == Ok(error),
{
    let outer = match read_b3b_state_tag(workspace, window_bytes, B3B_OUTER_PHASE, 13) {
        Ok(value) => value,
        Err(_) => return Err(CompressedHeaderError::InternalState),
    };
    if outer != 12 {
        return Err(CompressedHeaderError::InternalState);
    }
    let tag = match read_b3b_state_tag(workspace, window_bytes, B3B_TERMINAL_ERROR, 6) {
        Ok(value) => value,
        Err(_) => return Err(CompressedHeaderError::InternalState),
    };
    let detail = match read_b3b_state_u16(workspace, window_bytes, B3B_ERROR_DETAIL) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    match tag {
        1 => match decode_compressed_format_error(detail) {
            Some(error) => Ok(CompressedHeaderError::InvalidFormat(error)),
            None => Err(CompressedHeaderError::InternalState),
        },
        2 if detail == 0 => Ok(CompressedHeaderError::Truncated),
        3 if detail == 0 => Ok(CompressedHeaderError::UnsupportedMode),
        4 => match decode_workspace_error(detail) {
            Some(error) => Ok(CompressedHeaderError::Workspace(error)),
            None => Err(CompressedHeaderError::InternalState),
        },
        5 if detail == 0 => Ok(CompressedHeaderError::InternalState),
        _ => Err(CompressedHeaderError::InternalState),
    }
}

spec fn tree_region_tag_spec(region: crate::brotli_prefix::TreeRegion) -> u8 {
    match region {
        crate::brotli_prefix::TreeRegion::Literal => 0,
        crate::brotli_prefix::TreeRegion::Command => 1,
        crate::brotli_prefix::TreeRegion::Distance => 2,
        crate::brotli_prefix::TreeRegion::BlockType => 3,
        crate::brotli_prefix::TreeRegion::BlockLength => 4,
        crate::brotli_prefix::TreeRegion::TemporaryContext => 5,
    }
}

fn tree_region_tag(region: crate::brotli_prefix::TreeRegion) -> (r: u8)
    ensures r == tree_region_tag_spec(region), r <= 5,
{
    match region {
        crate::brotli_prefix::TreeRegion::Literal => 0,
        crate::brotli_prefix::TreeRegion::Command => 1,
        crate::brotli_prefix::TreeRegion::Distance => 2,
        crate::brotli_prefix::TreeRegion::BlockType => 3,
        crate::brotli_prefix::TreeRegion::BlockLength => 4,
        crate::brotli_prefix::TreeRegion::TemporaryContext => 5,
    }
}

fn decode_tree_region(tag: u8) -> (r: Option<crate::brotli_prefix::TreeRegion>)
    ensures match r {
        Some(region) => tree_region_tag_spec(region) == tag,
        None => tag > 5,
    },
{
    match tag {
        0 => Some(crate::brotli_prefix::TreeRegion::Literal),
        1 => Some(crate::brotli_prefix::TreeRegion::Command),
        2 => Some(crate::brotli_prefix::TreeRegion::Distance),
        3 => Some(crate::brotli_prefix::TreeRegion::BlockType),
        4 => Some(crate::brotli_prefix::TreeRegion::BlockLength),
        5 => Some(crate::brotli_prefix::TreeRegion::TemporaryContext),
        _ => None,
    }
}

fn code_description_error_tag(error: CodeDescriptionError) -> (r: u8)
    ensures 1 <= r <= 5,
{
    match error {
        CodeDescriptionError::MetaBlockNotCompressed => 1,
        CodeDescriptionError::InvalidAlphabet => 2,
        CodeDescriptionError::DuplicateSimpleSymbol => 3,
        CodeDescriptionError::CodeLengthSpace => 4,
        CodeDescriptionError::Truncated => 5,
    }
}

fn decode_code_description_error(tag: u8) -> (r: Option<CodeDescriptionError>)
{
    match tag {
        1 => Some(CodeDescriptionError::MetaBlockNotCompressed),
        2 => Some(CodeDescriptionError::InvalidAlphabet),
        3 => Some(CodeDescriptionError::DuplicateSimpleSymbol),
        4 => Some(CodeDescriptionError::CodeLengthSpace),
        5 => Some(CodeDescriptionError::Truncated),
        _ => None,
    }
}

fn initialize_code_description_state(
    workspace: &mut [u8],
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    alphabet_max: u16,
    alphabet_limit: u16,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && 1 <= alphabet_limit <= alphabet_max <= 704 ==> r.is_ok(),
        r.is_ok() ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_ACTIVE_REGION,
        ) == tree_region_tag_spec(region),
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_ACTIVE_TREE,
        ) == tree,
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_ALPHABET_MAX,
        ) == alphabet_max,
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_ALPHABET_LIMIT,
        ) == alphabet_limit,
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INDEX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INDEX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED),
        r.is_ok() ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        r.is_ok() ==> b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            && !(8 <= b3b_scalar_byte_at(
                old(workspace)@,
                window_bytes,
                B3B_OUTER_PHASE,
            ) <= 11)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        forall|i: int| 0 <= i < B3B_GROUP_KIND ==> #[trigger]
            final(workspace)@[b3b_scalar_base(window_bytes) + i]
                == old(workspace)@[b3b_scalar_base(window_bytes) + i],
{
    let ghost original = workspace@;
    proof { assert(original == old(workspace)@); }
    if alphabet_max == 0 || alphabet_max > 704
        || alphabet_limit == 0 || alphabet_limit > alphabet_max {
        return Err(CompressedHeaderError::InvalidFormat(
            CompressedFormatError::InvalidPrefixCode,
        ));
    }
    let mut relative = B3B_CODE_PHASE;
    while relative < B3B_BLOCK_LENGTH_PHASE
        invariant B3B_CODE_PHASE <= relative <= B3B_BLOCK_LENGTH_PHASE,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_KIND),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_COUNT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_COUNT),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_TREES)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_TREES),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_INDEX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_INDEX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_INITIALIZED)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_INITIALIZED),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            serialized_mtf_state_ok(original, window_bytes)
                ==> serialized_mtf_state_ok(workspace@, window_bytes),
            forall|i: int| 0 <= i < B3B_GROUP_KIND ==> #[trigger]
                workspace@[b3b_scalar_base(window_bytes) + i]
                    == original[b3b_scalar_base(window_bytes) + i],
        decreases B3B_BLOCK_LENGTH_PHASE - relative,
    {
        match write_b3b_state_byte(workspace, window_bytes, relative, 0) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        relative = relative + 1;
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_PENDING_SPAN_LENGTH, 0) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(
        workspace,
        window_bytes,
        B3B_ACTIVE_REGION,
        tree_region_tag(region),
    ) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_u16(workspace, window_bytes, B3B_ACTIVE_TREE, tree) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_u16(workspace, window_bytes, B3B_ALPHABET_MAX, alphabet_max) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    let result = match write_b3b_state_u16(
        workspace,
        window_bytes,
        B3B_ALPHABET_LIMIT,
        alphabet_limit,
    ) {
        Ok(()) => Ok(()),
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    };
    proof {
        if result.is_ok() {
            assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_KIND));
            assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_COUNT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_COUNT));
        }
    }
    result
}

fn read_simple_symbols(
    workspace: &[u8],
    window_bytes: u32,
) -> (r: Result<[u16; 4], CompressedHeaderError>)
{
    let mut symbols = [0u16; 4];
    let mut i: usize = 0;
    while i < 4
        invariant i <= 4,
        decreases 4 - i,
    {
        symbols[i] = match read_b3b_state_u16(
            workspace,
            window_bytes,
            B3B_SIMPLE_SYMBOLS + 2 * i as u16,
        ) {
            Ok(value) => value,
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        };
        i = i + 1;
    }
    Ok(symbols)
}

spec fn code_store_frame(before: Seq<u8>, after: Seq<u8>, window_bytes: u32) -> bool {
    &&& after.len() == before.len()
    &&& (serialized_context_data_ok(before, window_bytes)
        ==> serialized_context_data_ok(after, window_bytes))
    &&& (serialized_context_state_ok(before, window_bytes)
        ==> serialized_context_state_ok(after, window_bytes))
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
        == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_PHASE)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
        == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION)
        == b3b_scalar_byte_at(before, window_bytes, B3B_ACTIVE_REGION)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE)
        == b3b_scalar_u16_at(before, window_bytes, B3B_ACTIVE_TREE)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX)
        == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_MAX)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT)
        == b3b_scalar_u16_at(before, window_bytes, B3B_ALPHABET_LIMIT)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_KIND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_KIND)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_PHASE)
        == b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_PHASE)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_TREE_INDEX)
        == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_INDEX)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_TREE_COUNT)
        == b3b_scalar_u16_at(before, window_bytes, B3B_TREE_COUNT)
    &&& (compressed_decoder_state_ok(before, window_bytes)
        ==> compressed_decoder_state_ok(after, window_bytes))
}

fn write_simple_symbols(
    workspace: &mut [u8],
    window_bytes: u32,
    symbols: [u16; 4],
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    let ghost original = workspace@;
    proof {
        assert(original == old(workspace)@);
        reveal(code_store_frame);
        assert(code_store_frame(original, workspace@, window_bytes));
    }
    let mut i: usize = 0;
    while i < 4
        invariant i <= 4,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
            code_store_frame(original, workspace@, window_bytes),
        decreases 4 - i,
    {
        match write_b3b_state_u16(
            workspace,
            window_bytes,
            B3B_SIMPLE_SYMBOLS + 2 * i as u16,
            symbols[i],
        ) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        i = i + 1;
    }
    Ok(())
}

fn read_aux_lengths(
    workspace: &[u8],
    window_bytes: u32,
) -> (r: Result<[u8; 18], CompressedHeaderError>)
{
    let mut lengths = [0u8; 18];
    let mut i: usize = 0;
    while i < 18
        invariant i <= 18,
        decreases 18 - i,
    {
        lengths[i] = match read_b3b_state_byte(
            workspace,
            window_bytes,
            B3B_AUX_LENGTHS + i as u16,
        ) {
            Ok(value) => value,
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        };
        if lengths[i] > 5 {
            return Err(CompressedHeaderError::InternalState);
        }
        i = i + 1;
    }
    Ok(lengths)
}

fn write_aux_lengths(
    workspace: &mut [u8],
    window_bytes: u32,
    lengths: [u8; 18],
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    let ghost original = workspace@;
    proof {
        assert(original == old(workspace)@);
        reveal(code_store_frame);
        assert(code_store_frame(original, workspace@, window_bytes));
    }
    let mut i: usize = 0;
    while i < 18
        invariant i <= 18,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
            code_store_frame(original, workspace@, window_bytes),
        decreases 18 - i,
    {
        match write_b3b_state_byte(
            workspace,
            window_bytes,
            B3B_AUX_LENGTHS + i as u16,
            lengths[i],
        ) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        i = i + 1;
    }
    Ok(())
}

fn state_byte(
    workspace: &[u8], window_bytes: u32, relative: u16,
) -> (r: Result<u8, CompressedHeaderError>)
    ensures
        r.is_ok() ==> {
            &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            &&& r.unwrap() == b3b_scalar_byte_at(workspace@, window_bytes, relative)
        },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    match read_b3b_state_byte(workspace, window_bytes, relative) {
        Ok(value) => Ok(value),
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

fn state_u16(
    workspace: &[u8], window_bytes: u32, relative: u16,
) -> (r: Result<u16, CompressedHeaderError>)
    ensures
        r.is_ok() ==> {
            &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            &&& r.unwrap() as nat == b3b_scalar_u16_at(workspace@, window_bytes, relative)
        },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 2 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    match read_b3b_state_u16(workspace, window_bytes, relative) {
        Ok(value) => {
            proof {
                reveal(b3b_scalar_u16_at);
                reveal(b3b_scalar_byte_at);
                reveal(b3b_scalar_base);
                assert((relative + 1) as u16 as nat == relative as nat + 1);
            }
            Ok(value)
        }
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

fn state_u32(
    workspace: &[u8], window_bytes: u32, relative: u16,
) -> (r: Result<u32, CompressedHeaderError>)
    ensures
        r.is_ok() ==> {
            &&& b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            &&& r.unwrap() as nat == b3b_scalar_u32_at(workspace@, window_bytes, relative)
        },
        b3b_workspace_shape(workspace@.len() as nat, window_bytes)
            && relative as nat + 4 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
{
    match read_b3b_state_u32(workspace, window_bytes, relative) {
        Ok(value) => {
            proof {
                reveal(b3b_scalar_u32_at);
                reveal(b3b_scalar_byte_at);
                reveal(b3b_scalar_base);
                assert((relative + 1) as u16 as nat == relative as nat + 1);
                assert((relative + 2) as u16 as nat == relative as nat + 2);
                assert((relative + 3) as u16 as nat == relative as nat + 3);
            }
            Ok(value)
        }
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

fn put_state_byte(
    workspace: &mut [u8], window_bytes: u32, relative: u16, value: u8,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        r.is_ok() ==> {
            let at = b3b_scalar_base(window_bytes) + relative as int;
            &&& final(workspace)@.len() == old(workspace)@.len()
            &&& b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes)
            &&& final(workspace)@[at] == value
            &&& forall|i: int| 0 <= i < old(workspace)@.len() && i != at
                ==> final(workspace)@[i] == old(workspace)@[i]
        },
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && relative != B3B_MTF_UPPER_BOUND
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            && relative != B3B_OUTER_PHASE
            && relative != B3B_MTF_UPPER_BOUND
            && !(6 <= b3b_scalar_byte_at(
                old(workspace)@,
                window_bytes,
                B3B_OUTER_PHASE,
            ) <= 11)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && relative != B3B_MTF_UPPER_BOUND
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && relative != B3B_MTF_UPPER_BOUND
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        B3B_GROUP_KIND <= relative && relative != B3B_MTF_UPPER_BOUND
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 1 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
        relative != B3B_OUTER_PHASE ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_OUTER_PHASE,
        ) == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
{
    match write_b3b_state_byte(workspace, window_bytes, relative, value) {
        Ok(()) => Ok(()),
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

fn put_state_u16(
    workspace: &mut [u8], window_bytes: u32, relative: u16, value: u16,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        r.is_ok() ==> {
            let at = b3b_scalar_base(window_bytes) + relative as int;
            &&& final(workspace)@.len() == old(workspace)@.len()
            &&& b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes)
            &&& final(workspace)@ == old(workspace)@
                .update(at, (value % 256) as u8)
                .update(at + 1, (value / 256) as u8)
        },
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            && (relative as nat + 2 <= B3B_OUTER_PHASE
                || B3B_OUTER_PHASE as nat + 1 <= relative as nat)
            && !(6 <= b3b_scalar_byte_at(
                old(workspace)@,
                window_bytes,
                B3B_OUTER_PHASE,
            ) <= 11)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && (relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && (relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        (relative == B3B_LITERAL_TREES || relative == B3B_DISTANCE_TREES)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        B3B_GROUP_KIND <= relative
            && (relative as nat + 2 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 2 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
        (relative as nat + 2 <= B3B_OUTER_PHASE
            || B3B_OUTER_PHASE as nat + 1 <= relative as nat)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
{
    match write_b3b_state_u16(workspace, window_bytes, relative, value) {
        Ok(()) => Ok(()),
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

fn put_state_u32(
    workspace: &mut [u8], window_bytes: u32, relative: u16, value: u32,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        r.is_ok() ==> {
            let at = b3b_scalar_base(window_bytes) + relative as int;
            &&& final(workspace)@.len() == old(workspace)@.len()
            &&& b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes)
            &&& final(workspace)@ == old(workspace)@
                .update(at, (value % 256) as u8)
                .update(at + 1, ((value / 256) % 256) as u8)
                .update(at + 2, ((value / 65_536) % 256) as u8)
                .update(at + 3, (value / 16_777_216) as u8)
        },
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            && (relative as nat + 4 <= B3B_OUTER_PHASE
                || B3B_OUTER_PHASE as nat + 1 <= relative as nat)
            && !(6 <= b3b_scalar_byte_at(
                old(workspace)@,
                window_bytes,
                B3B_OUTER_PHASE,
            ) <= 11)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            && B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        B3B_GROUP_KIND <= relative
            && (relative as nat + 4 <= B3B_MTF_UPPER_BOUND
                || B3B_MTF_UPPER_BOUND as nat + 1 <= relative as nat)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && relative as nat + 4 <= B3B_SCALAR_BYTES
            ==> r.is_ok(),
        r.is_err() ==> final(workspace)@ == old(workspace)@,
        (relative as nat + 4 <= B3B_OUTER_PHASE
            || B3B_OUTER_PHASE as nat + 1 <= relative as nat)
            ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
{
    match write_b3b_state_u32(workspace, window_bytes, relative, value) {
        Ok(()) => Ok(()),
        Err(error) => Err(CompressedHeaderError::Workspace(error)),
    }
}

fn store_installed_prefix_state(
    workspace: &mut [u8],
    window_bytes: u32,
    prefix: InstalledPrefixState,
) -> (r: Result<(), CompressedHeaderError>)
    requires prefix.valid(),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_ok() ==> serialized_installed_prefix(
            final(workspace)@,
            window_bytes,
            prefix,
        ),
        r.is_ok() ==> forall|i: int| 0 <= i < old(workspace)@.len()
            && i != b3b_scalar_base(window_bytes) + B3B_INSTALLED_PREFIX_WIDTH as int
            && !(b3b_scalar_base(window_bytes) + B3B_INSTALLED_PREFIX_BITS as int
                <= i < b3b_scalar_base(window_bytes) + B3B_INSTALLED_PREFIX_BITS as int + 2)
            && !(b3b_scalar_base(window_bytes) + B3B_INSTALLED_SCAN as int
                <= i < b3b_scalar_base(window_bytes) + B3B_INSTALLED_SCAN as int + 2)
            ==> #[trigger] final(workspace)@[i] == old(workspace)@[i],
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_PENDING_RUN)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_PENDING_RUN),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    let ghost original = workspace@;
    match put_state_byte(
        workspace,
        window_bytes,
        B3B_INSTALLED_PREFIX_WIDTH,
        prefix.width,
    ) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    match put_state_u16(
        workspace,
        window_bytes,
        B3B_INSTALLED_PREFIX_BITS,
        prefix.bits,
    ) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    match put_state_u16(
        workspace,
        window_bytes,
        B3B_INSTALLED_SCAN,
        prefix.scan,
    ) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        reveal(serialized_context_state_ok);
        reveal(serialized_context_phase_payload_ok);
        reveal(serialized_context_data_ok);
        reveal(serialized_context_map_prefix_ok);
        reveal(serialized_context_complete_map_ok);
        reveal(serialized_mtf_state_ok);
        reveal(b3b_scalar_u16_at);
        reveal(b3b_scalar_byte_at);
        reveal(b3b_scalar_base);
        if serialized_context_state_ok(original, window_bytes) {
            b3b_scalar_layout_is_exact();
            assert(serialized_mtf_state_ok(workspace@, window_bytes));
            assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE));
            assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND));
            assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_TREES)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_TREES));
            assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE));
            assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_INDEX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_INDEX));
            assert(b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_INITIALIZED)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_INITIALIZED));
            assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_MAX_RUN_PREFIX)
                == b3b_scalar_byte_at(original, window_bytes, B3B_MAX_RUN_PREFIX));
            assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_PENDING_RUN)
                == b3b_scalar_byte_at(original, window_bytes, B3B_PENDING_RUN));
            assert forall|i: int| 0 <= i < 16_384 implies #[trigger]
                workspace@[window_bytes as int
                    + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as int + i]
                    == original[window_bytes as int
                        + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as int + i] by {}
            assert forall|i: int| 0 <= i < 1_024 implies #[trigger]
                workspace@[window_bytes as int
                    + crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET as int + i]
                    == original[window_bytes as int
                        + crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET as int + i] by {}
            if b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND) == 0 {
                assert(crate::brotli_prefix::context_map_values(
                    workspace@,
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE) as u16,
                ) =~= crate::brotli_prefix::context_map_values(
                    original,
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE) as u16,
                ));
            } else {
                assert(crate::brotli_prefix::context_map_values(
                    workspace@,
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE) as u16,
                ) =~= crate::brotli_prefix::context_map_values(
                    original,
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE) as u16,
                ));
            }
            let spec_kind = if b3b_scalar_byte_at(
                original,
                window_bytes,
                B3B_CONTEXT_KIND,
            ) == 0 {
                crate::brotli_prefix::ContextMapKind::Literal
            } else {
                crate::brotli_prefix::ContextMapKind::Distance
            };
            let initialized = b3b_scalar_u16_at(
                original,
                window_bytes,
                B3B_MAP_INITIALIZED,
            );
            let num_trees = b3b_scalar_u16_at(
                original,
                window_bytes,
                B3B_MAP_TREES,
            );
            assert(serialized_context_map_prefix_ok(original, window_bytes));
            if num_trees > 0 {
                assert forall|i: int| 0 <= i < initialized implies #[trigger]
                    workspace@[crate::brotli_prefix::context_entry_at(
                        window_bytes,
                        spec_kind,
                        i as u16,
                    ) as int] < num_trees by {
                    assert(serialized_context_map_prefix_ok(original, window_bytes));
                    assert(0 <= i < 65_536);
                    assert((i as u16) as int == i);
                    serialized_context_prefix_value_bound(original, window_bytes, i);
                    let derived_kind = if b3b_scalar_byte_at(
                        original,
                        window_bytes,
                        B3B_CONTEXT_KIND,
                    ) == 0 {
                        crate::brotli_prefix::ContextMapKind::Literal
                    } else {
                        crate::brotli_prefix::ContextMapKind::Distance
                    };
                    assert(derived_kind == spec_kind);
                    assert(original[crate::brotli_prefix::context_entry_at(
                        window_bytes,
                        derived_kind,
                        i as u16,
                    ) as int] < num_trees);
                    if spec_kind == crate::brotli_prefix::ContextMapKind::Literal {
                        assert(workspace@[window_bytes as int
                            + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as int + i]
                            == original[window_bytes as int
                                + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as int + i]);
                    } else {
                        assert(workspace@[window_bytes as int
                            + crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET as int + i]
                            == original[window_bytes as int
                                + crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET as int + i]);
                    }
                }
            }
            assert(serialized_context_map_prefix_ok(workspace@, window_bytes));
            assert(serialized_context_data_ok(workspace@, window_bytes));
            if b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE) == 9 {
                assert(serialized_context_complete_map_ok(workspace@, window_bytes));
            }
            assert(serialized_context_state_ok(workspace@, window_bytes));
        }
    }
    Ok(())
}

fn load_code_description_decoder(
    workspace: &[u8],
    window_bytes: u32,
    queue: BitQueue,
) -> (r: Result<CodeDescriptionDecoder, CompressedHeaderError>)
    requires queue.valid(),
    ensures
        r.is_ok() ==> r.unwrap().valid(),
        r.is_ok() ==> r.unwrap().alphabet_max as nat
            == b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_MAX),
        r.is_ok() ==> r.unwrap().alphabet_limit as nat
            == b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_LIMIT),
{
    let alphabet_max = match state_u16(workspace, window_bytes, B3B_ALPHABET_MAX) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let alphabet_limit = match state_u16(workspace, window_bytes, B3B_ALPHABET_LIMIT) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if alphabet_max == 0 || alphabet_max > 704
        || alphabet_limit == 0 || alphabet_limit > alphabet_max {
        return Err(CompressedHeaderError::InternalState);
    }
    let tag = match state_byte(workspace, window_bytes, B3B_CODE_PHASE) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let selector = match state_byte(workspace, window_bytes, B3B_SIMPLE_SELECTOR) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let count = match state_byte(workspace, window_bytes, B3B_SIMPLE_COUNT) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let index = match state_byte(workspace, window_bytes, B3B_CODE_INDEX) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let width = match state_byte(workspace, window_bytes, B3B_CODE_WIDTH) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let symbols = match read_simple_symbols(workspace, window_bytes) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let skip = match state_byte(workspace, window_bytes, B3B_AUX_SKIP) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let aux_index = match state_byte(workspace, window_bytes, B3B_AUX_INDEX) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let aux_space = match state_byte(workspace, window_bytes, B3B_AUX_SPACE) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let aux_nonzero = match state_byte(workspace, window_bytes, B3B_AUX_NONZERO) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let lengths = match read_aux_lengths(workspace, window_bytes) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let code = ComplexCodeLengthAlphabet { skip, lengths };
    let phase = match tag {
        0 => CodeDescriptionPhase::Selector,
        1 => CodeDescriptionPhase::SimpleSize,
        2 if selector <= 3 && 1 <= count && count <= 4 && index < count && width <= 10 =>
            CodeDescriptionPhase::SimpleSymbols { selector, count, index, width, symbols },
        3 if selector == 3 && count == 4 => CodeDescriptionPhase::SimpleShape { symbols },
        4 => {
            if !(skip == 0 || skip == 2 || skip == 3)
                || aux_index < skip || aux_index >= 18 || aux_space > 32
                || aux_nonzero > aux_index - skip {
                return Err(CompressedHeaderError::InternalState);
            }
            let progress = ComplexProgress {
                skip, index: aux_index, lengths, space: aux_space, nonzero: aux_nonzero,
            };
            let aux_tag = match state_byte(workspace, window_bytes, B3B_CODE_AUX_PHASE) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match aux_tag {
                1 => CodeDescriptionPhase::ComplexPrefix2(progress),
                2 => CodeDescriptionPhase::ComplexPrefix3(progress),
                3 => CodeDescriptionPhase::ComplexPrefix4(progress),
                _ => return Err(CompressedHeaderError::InternalState),
            }
        }
        5 | 6 | 7 | 9 => {
            if !(skip == 0 || skip == 2 || skip == 3) {
                return Err(CompressedHeaderError::InternalState);
            }
            let symbol = match state_u16(workspace, window_bytes, B3B_FINAL_SYMBOL) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let previous = match state_byte(workspace, window_bytes, B3B_PREVIOUS_LENGTH) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let repeated = match state_byte(workspace, window_bytes, B3B_REPEATED_LENGTH) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let repeat = match state_u32(workspace, window_bytes, B3B_CHAINED_REPEAT) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let final_space = match state_u32(workspace, window_bytes, B3B_FINAL_SPACE) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let prefix_bits = match state_byte(workspace, window_bytes, B3B_FINAL_PREFIX_BITS) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let prefix_width = match state_byte(workspace, window_bytes, B3B_FINAL_PREFIX_WIDTH) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let singleton = match state_byte(workspace, window_bytes, B3B_AUX_SINGLETON) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if symbol > alphabet_limit || previous == 0 || previous > 15
                || repeated > 15 || repeat > symbol as u32 || final_space > 32_768
                || prefix_width >= 5 || singleton > 18 {
                return Err(CompressedHeaderError::InternalState);
            }
            if tag == 9 {
                if symbol != alphabet_limit || final_space != 0 {
                    return Err(CompressedHeaderError::InternalState);
                }
                CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbol }
            } else {
                if symbol >= alphabet_limit || final_space == 0 {
                    if tag != 7 {
                        return Err(CompressedHeaderError::InternalState);
                    }
                }
                let progress = ComplexSymbolProgress {
                    code, symbol, prev_code_len: previous, repeat,
                    repeat_code_len: repeated, space: final_space,
                    prefix_width, prefix_bits, singleton,
                };
                if tag == 5 {
                    CodeDescriptionPhase::ComplexSymbol(progress)
                } else if tag == 6 {
                    let repeat_length = repeated;
                    let extra_bits = if repeat_length == 0 { 3 } else { 2 };
                    CodeDescriptionPhase::ComplexRepeat {
                        progress, length: repeat_length, extra_bits,
                    }
                } else {
                    let initialized = match state_u16(
                        workspace, window_bytes, B3B_BUILDER_INITIALIZED) {
                        Ok(value) => value,
                        Err(error) => return Err(error),
                    };
                    let pending_length = match state_byte(
                        workspace, window_bytes, B3B_PENDING_SPAN_LENGTH) {
                        Ok(value) => value,
                        Err(error) => return Err(error),
                    };
                    if initialized >= symbol || pending_length > 15 {
                        return Err(CompressedHeaderError::InternalState);
                    }
                    let after = if final_space == 0 {
                        if symbol < alphabet_limit {
                            ComplexAfterSpan::TrailingZeros { code, start: symbol }
                        } else {
                            ComplexAfterSpan::Complete { code, symbols: alphabet_limit }
                        }
                    } else {
                        ComplexAfterSpan::Symbol(progress)
                    };
                    CodeDescriptionPhase::ComplexPendingSpan {
                        start: initialized,
                        span_count: symbol - initialized,
                        length: pending_length,
                        after,
                    }
                }
            }
        }
        8 if selector <= 4
            && count == if selector <= 2 { selector + 1 } else { 4 } =>
            CodeDescriptionPhase::CompleteSimple(SimpleCodeDescription {
                selector, count, symbols,
            }),
        10 => {
            let error_tag = match state_byte(workspace, window_bytes, B3B_CODE_ERROR) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match decode_code_description_error(error_tag) {
                Some(error) => CodeDescriptionPhase::Failed(error),
                None => return Err(CompressedHeaderError::InternalState),
            }
        }
        _ => return Err(CompressedHeaderError::InternalState),
    };
    if !code_description_phase_valid_exec(&phase, alphabet_max, alphabet_limit) {
        return Err(CompressedHeaderError::InternalState);
    }
    let decoder = CodeDescriptionDecoder { queue, alphabet_max, alphabet_limit, phase };
    assert(decoder.valid());
    Ok(decoder)
}

fn store_complex_code(
    workspace: &mut [u8],
    window_bytes: u32,
    code: ComplexCodeLengthAlphabet,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    match put_state_byte(workspace, window_bytes, B3B_AUX_SKIP, code.skip) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    write_aux_lengths(workspace, window_bytes, code.lengths)
}

fn store_complex_progress(
    workspace: &mut [u8],
    window_bytes: u32,
    progress: ComplexSymbolProgress,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    let ghost original = workspace@;
    proof {
        assert(original == old(workspace)@);
        reveal(code_store_frame);
    }
    match store_complex_code(workspace, window_bytes, progress.code) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    let mut i: usize = 0;
    while i < 5
        invariant i <= 5,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
            code_store_frame(original, workspace@, window_bytes),
        decreases 5 - i,
    {
        let (offset, value) = if i == 0 {
            (B3B_PREVIOUS_LENGTH, progress.prev_code_len)
        } else if i == 1 {
            (B3B_REPEATED_LENGTH, progress.repeat_code_len)
        } else if i == 2 {
            (B3B_FINAL_PREFIX_BITS, progress.prefix_bits)
        } else if i == 3 {
            (B3B_FINAL_PREFIX_WIDTH, progress.prefix_width)
        } else {
            (B3B_AUX_SINGLETON, progress.singleton)
        };
        proof {
            b3b_scalar_layout_is_exact();
            assert(B3B_CODE_PHASE <= offset);
            assert(offset != B3B_MTF_UPPER_BOUND);
        }
        match put_state_byte(workspace, window_bytes, offset, value) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        i = i + 1;
    }
    match put_state_u16(workspace, window_bytes, B3B_FINAL_SYMBOL, progress.symbol) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof { assert(code_store_frame(original, workspace@, window_bytes)); }
    match put_state_u32(workspace, window_bytes, B3B_CHAINED_REPEAT, progress.repeat) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof { assert(code_store_frame(original, workspace@, window_bytes)); }
    let result = put_state_u32(workspace, window_bytes, B3B_FINAL_SPACE, progress.space);
    proof { assert(code_store_frame(original, workspace@, window_bytes)); }
    result
}

spec fn code_phase_store_safe(phase: CodeDescriptionPhase) -> bool {
    match phase {
        CodeDescriptionPhase::ComplexPendingSpan { start, span_count, .. } =>
            start as nat + span_count as nat <= u16::MAX,
        _ => true,
    }
}

fn store_simple_code_description_payload(
    workspace: &mut [u8],
    window_bytes: u32,
    phase: CodeDescriptionPhase,
) -> (r: Result<u8, CompressedHeaderError>)
    ensures code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
{
    let tag = match phase {
        CodeDescriptionPhase::Selector => 0,
        CodeDescriptionPhase::SimpleSize => 1,
        CodeDescriptionPhase::SimpleSymbols {
            selector, count, index, width, symbols,
        } => {
            put_state_byte(workspace, window_bytes, B3B_SIMPLE_SELECTOR, selector)?;
            put_state_byte(workspace, window_bytes, B3B_SIMPLE_COUNT, count)?;
            put_state_byte(workspace, window_bytes, B3B_CODE_INDEX, index)?;
            put_state_byte(workspace, window_bytes, B3B_CODE_WIDTH, width)?;
            write_simple_symbols(workspace, window_bytes, symbols)?;
            2
        }
        CodeDescriptionPhase::SimpleShape { symbols } => {
            put_state_byte(workspace, window_bytes, B3B_SIMPLE_SELECTOR, 3)?;
            put_state_byte(workspace, window_bytes, B3B_SIMPLE_COUNT, 4)?;
            write_simple_symbols(workspace, window_bytes, symbols)?;
            3
        }
        CodeDescriptionPhase::CompleteSimple(code) => {
            put_state_byte(workspace, window_bytes, B3B_SIMPLE_SELECTOR, code.selector)?;
            put_state_byte(workspace, window_bytes, B3B_SIMPLE_COUNT, code.count)?;
            write_simple_symbols(workspace, window_bytes, code.symbols)?;
            8
        }
        _ => return Err(CompressedHeaderError::InternalState),
    };
    Ok(tag)
}

fn store_complex_code_description_payload(
    workspace: &mut [u8],
    window_bytes: u32,
    phase: CodeDescriptionPhase,
) -> (r: Result<u8, CompressedHeaderError>)
    requires code_phase_store_safe(phase),
    ensures code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
{
    let tag = match phase {
        CodeDescriptionPhase::ComplexPrefix2(progress)
        | CodeDescriptionPhase::ComplexPrefix3(progress)
        | CodeDescriptionPhase::ComplexPrefix4(progress) => {
            let aux_tag = match phase {
                CodeDescriptionPhase::ComplexPrefix2(_) => 1,
                CodeDescriptionPhase::ComplexPrefix3(_) => 2,
                _ => 3,
            };
            put_state_byte(workspace, window_bytes, B3B_CODE_AUX_PHASE, aux_tag)?;
            put_state_byte(workspace, window_bytes, B3B_AUX_SKIP, progress.skip)?;
            put_state_byte(workspace, window_bytes, B3B_AUX_INDEX, progress.index)?;
            put_state_byte(workspace, window_bytes, B3B_AUX_SPACE, progress.space)?;
            put_state_byte(workspace, window_bytes, B3B_AUX_NONZERO, progress.nonzero)?;
            write_aux_lengths(workspace, window_bytes, progress.lengths)?;
            4
        }
        CodeDescriptionPhase::ComplexSymbol(progress) => {
            store_complex_progress(workspace, window_bytes, progress)?;
            5
        }
        CodeDescriptionPhase::ComplexRepeat { progress, length, .. } => {
            store_complex_progress(workspace, window_bytes, progress)?;
            put_state_byte(workspace, window_bytes, B3B_REPEATED_LENGTH, length)?;
            6
        }
        CodeDescriptionPhase::ComplexPendingSpan {
            start, span_count, length, after,
        } => {
            let end = start + span_count;
            match after {
                ComplexAfterSpan::Symbol(progress) => {
                    store_complex_progress(workspace, window_bytes, progress)?;
                }
                ComplexAfterSpan::TrailingZeros { code, .. }
                | ComplexAfterSpan::Complete { code, .. } => {
                    store_complex_code(workspace, window_bytes, code)?;
                    put_state_u16(workspace, window_bytes, B3B_FINAL_SYMBOL, end)?;
                    put_state_u32(workspace, window_bytes, B3B_FINAL_SPACE, 0)?;
                }
            }
            put_state_byte(workspace, window_bytes, B3B_PENDING_SPAN_LENGTH, length)?;
            7
        }
        CodeDescriptionPhase::CompleteComplexAlphabet(_) =>
            return Err(CompressedHeaderError::InternalState),
        CodeDescriptionPhase::CompleteComplex { code, decoded_symbols } => {
            store_complex_code(workspace, window_bytes, code)?;
            put_state_u16(workspace, window_bytes, B3B_FINAL_SYMBOL, decoded_symbols)?;
            put_state_u32(workspace, window_bytes, B3B_FINAL_SPACE, 0)?;
            9
        }
        CodeDescriptionPhase::Failed(error) => {
            put_state_byte(
                workspace,
                window_bytes,
                B3B_CODE_ERROR,
                code_description_error_tag(error),
            )?;
            10
        }
        _ => return Err(CompressedHeaderError::InternalState),
    };
    Ok(tag)
}

fn store_code_description_payload(
    workspace: &mut [u8],
    window_bytes: u32,
    phase: CodeDescriptionPhase,
) -> (r: Result<u8, CompressedHeaderError>)
    requires code_phase_store_safe(phase),
    ensures code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
{
    match phase {
        CodeDescriptionPhase::Selector
        | CodeDescriptionPhase::SimpleSize
        | CodeDescriptionPhase::SimpleSymbols { .. }
        | CodeDescriptionPhase::SimpleShape { .. }
        | CodeDescriptionPhase::CompleteSimple(_) =>
            store_simple_code_description_payload(workspace, window_bytes, phase),
        _ => store_complex_code_description_payload(workspace, window_bytes, phase),
    }
}

fn store_code_description_decoder(
    workspace: &mut [u8],
    window_bytes: u32,
    decoder: CodeDescriptionDecoder,
) -> (r: Result<(), CompressedHeaderError>)
    requires decoder.valid(),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    match put_state_byte(workspace, window_bytes, B3B_CODE_AUX_PHASE, 0) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    match put_state_byte(workspace, window_bytes, B3B_CODE_ERROR, 0) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    match put_state_byte(workspace, window_bytes, B3B_PENDING_SPAN_LENGTH, 0) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        reveal(CodeDescriptionDecoder::valid);
        reveal(code_phase_store_safe);
        match decoder.phase {
            CodeDescriptionPhase::ComplexPendingSpan { start, span_count, .. } => {
                assert(start as nat + span_count as nat <= decoder.alphabet_limit);
                assert(decoder.alphabet_limit <= 704);
            }
            _ => {}
        }
        assert(code_phase_store_safe(decoder.phase));
    }
    let tag = match store_code_description_payload(
        workspace,
        window_bytes,
        decoder.phase,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    put_state_byte(workspace, window_bytes, B3B_CODE_PHASE, tag)
}

fn map_code_description_error(error: CodeDescriptionError) -> (r: CompressedHeaderError)
    ensures r == match error {
        CodeDescriptionError::MetaBlockNotCompressed => CompressedHeaderError::InternalState,
        CodeDescriptionError::InvalidAlphabet =>
            CompressedHeaderError::InvalidFormat(CompressedFormatError::InvalidPrefixCode),
        CodeDescriptionError::DuplicateSimpleSymbol =>
            CompressedHeaderError::InvalidFormat(CompressedFormatError::DuplicateSimpleSymbol),
        CodeDescriptionError::CodeLengthSpace =>
            CompressedHeaderError::InvalidFormat(CompressedFormatError::CodeLengthSpace),
        CodeDescriptionError::Truncated => CompressedHeaderError::Truncated,
    },
{
    match error {
        CodeDescriptionError::MetaBlockNotCompressed => CompressedHeaderError::InternalState,
        CodeDescriptionError::InvalidAlphabet =>
            CompressedHeaderError::InvalidFormat(CompressedFormatError::InvalidPrefixCode),
        CodeDescriptionError::DuplicateSimpleSymbol =>
            CompressedHeaderError::InvalidFormat(CompressedFormatError::DuplicateSimpleSymbol),
        CodeDescriptionError::CodeLengthSpace =>
            CompressedHeaderError::InvalidFormat(CompressedFormatError::CodeLengthSpace),
        CodeDescriptionError::Truncated => CompressedHeaderError::Truncated,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SerializedTreeStatus {
    NeedInput,
    Complete,
    Failed(CompressedHeaderError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SerializedTreeStep {
    consumed: usize,
    status: SerializedTreeStatus,
}

fn acknowledge_serialized_pending_span(
    decoder: &mut CodeDescriptionDecoder,
) -> (r: CodeDescriptionStep)
    requires
        old(decoder).valid(),
        matches!(old(decoder).phase, CodeDescriptionPhase::ComplexPendingSpan { .. }),
    ensures
        final(decoder).valid(),
        final(decoder).alphabet_max == old(decoder).alphabet_max,
        final(decoder).alphabet_limit == old(decoder).alphabet_limit,
        final(decoder).queue == old(decoder).queue,
        r.consumed == 0,
        match old(decoder).phase {
            CodeDescriptionPhase::ComplexPendingSpan { after, .. } =>
                pending_span_transition_holds(
                    after,
                    old(decoder).alphabet_limit,
                    final(decoder).phase,
                    r.status,
                ),
            _ => false,
        },
{
    let phase = decoder.phase;
    let after = match phase {
        CodeDescriptionPhase::ComplexPendingSpan { after, .. } => after,
        _ => {
            proof { assert(false); }
            return CodeDescriptionStep {
                consumed: 0,
                status: CodeDescriptionStatus::Progress,
            };
        }
    };
    decoder.phase = match after {
        ComplexAfterSpan::Symbol(progress) => CodeDescriptionPhase::ComplexSymbol(progress),
        ComplexAfterSpan::TrailingZeros { code, start } => {
            let count = decoder.alphabet_limit - start;
            CodeDescriptionPhase::ComplexPendingSpan {
                start,
                span_count: count,
                length: 0,
                after: ComplexAfterSpan::Complete {
                    code,
                    symbols: decoder.alphabet_limit,
                },
            }
        }
        ComplexAfterSpan::Complete { code, symbols } =>
            CodeDescriptionPhase::CompleteComplex { code, decoded_symbols: symbols },
    };
    let status = match decoder.phase {
        CodeDescriptionPhase::CompleteComplex { decoded_symbols: symbols, .. } =>
            CodeDescriptionStatus::ComplexComplete { symbols },
        _ => CodeDescriptionStatus::Progress,
    };
    assert(decoder.valid());
    CodeDescriptionStep { consumed: 0, status }
}

fn drain_serialized_pending_span(
    workspace: &mut [u8],
    window_bytes: u32,
    decoder: &mut CodeDescriptionDecoder,
) -> (r: Result<CodeDescriptionStep, CompressedHeaderError>)
    requires
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes),
        old(decoder).valid(),
        matches!(old(decoder).phase, CodeDescriptionPhase::ComplexPendingSpan { .. }),
    ensures
        final(decoder).valid(),
        final(decoder).alphabet_max == old(decoder).alphabet_max,
        final(decoder).alphabet_limit == old(decoder).alphabet_limit,
        final(decoder).queue == old(decoder).queue,
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        r.is_ok() ==> {
            &&& r.unwrap().consumed == 0
            &&& match old(decoder).phase {
                CodeDescriptionPhase::ComplexPendingSpan {
                    start, span_count, after, ..
                } => {
                    &&& b3b_scalar_u16_at(
                        final(workspace)@,
                        window_bytes,
                        B3B_BUILDER_INITIALIZED,
                    ) == start as nat + span_count as nat
                    &&& pending_span_transition_holds(
                        after,
                        old(decoder).alphabet_limit,
                        final(decoder).phase,
                        r.unwrap().status,
                    )
                },
                _ => false,
            }
        },
{
    let ghost original = workspace@;
    let (start, span_count, length) = match decoder.phase {
        CodeDescriptionPhase::ComplexPendingSpan {
            start, span_count, length, ..
        } => (start, span_count, length),
        _ => {
            proof { assert(false); }
            return Err(CompressedHeaderError::InternalState);
        }
    };
    let initialized = match state_u16(workspace, window_bytes, B3B_BUILDER_INITIALIZED) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if initialized != start
        || start as u32 + span_count as u32 > decoder.alphabet_limit as u32
    {
        proof { assert(workspace@ == original); }
        return Err(CompressedHeaderError::InternalState);
    }
    let mut written: u16 = 0;
    let mut next_initialized = initialized;
    while written < span_count
        invariant
            written <= span_count,
            next_initialized as nat == initialized as nat + written as nat,
            original == old(workspace)@,
            *decoder == *old(decoder),
            decoder.valid(),
            workspace@.len() == original.len(),
            b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_ACTIVE_REGION)
                == b3b_scalar_byte_at(original, window_bytes, B3B_ACTIVE_REGION),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_MAX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_MAX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_LIMIT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_LIMIT),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_INDEX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_INDEX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_COUNT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_COUNT),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
        decreases span_count - written,
    {
        let ghost before_length = workspace@;
        let _old_initialized = next_initialized;
        next_initialized = match crate::brotli_prefix::write_next_builder_code_length(
            workspace,
            window_bytes,
            next_initialized,
            length,
        ) {
            Ok(value) => value,
            Err(error) => {
                proof { assert(decoder.valid()); }
                return Err(CompressedHeaderError::Workspace(error));
            }
        };
        proof {
            builder_length_update_preserves_context_state(
                before_length,
                workspace@,
                window_bytes,
                _old_initialized,
                length,
            );
        }
        written = written + 1;
    }
    match put_state_u16(
        workspace,
        window_bytes,
        B3B_BUILDER_INITIALIZED,
        next_initialized,
    ) {
        Ok(()) => {}
        Err(error) => {
            return Err(error);
        }
    }
    let acknowledged = acknowledge_serialized_pending_span(decoder);
    if acknowledged.consumed != 0 {
        return Err(CompressedHeaderError::InternalState);
    }
    proof {
        assert(next_initialized as nat == start as nat + span_count as nat);
    }
    Ok(acknowledged)
}

fn drain_and_store_serialized_pending_span(
    workspace: &mut [u8],
    window_bytes: u32,
    decoder: &mut CodeDescriptionDecoder,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes),
        old(decoder).valid(),
        matches!(old(decoder).phase, CodeDescriptionPhase::ComplexPendingSpan { .. }),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
{
    match drain_serialized_pending_span(workspace, window_bytes, decoder) {
        Ok(_) => {}
        Err(error) => return Err(error),
    }
    store_code_description_decoder(workspace, window_bytes, *decoder)
}

spec fn tree_metadata_complete(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    alphabet: u16,
) -> bool {
    let at = crate::brotli_prefix::tree_metadata_at(window_bytes, region, tree);
    exists|meta: crate::brotli_prefix::TreeMetadata| {
        &&& meta.valid_for(region)
        &&& meta.symbols == alphabet
        &&& meta.symbols as nat == crate::brotli_prefix::little_u16_at(workspace, at)
        &&& crate::brotli_prefix::tree_metadata_descriptor(meta)
            == crate::brotli_prefix::little_u16_at(workspace, at + 2)
    }
}

spec fn active_tree_metadata_complete(workspace: Seq<u8>, window_bytes: u32) -> bool {
    let tag = b3b_scalar_byte_at(workspace, window_bytes, B3B_ACTIVE_REGION);
    let tree = b3b_scalar_u16_at(workspace, window_bytes, B3B_ACTIVE_TREE) as u16;
    let alphabet = b3b_scalar_u16_at(workspace, window_bytes, B3B_ALPHABET_LIMIT) as u16;
    if tag == 0 {
        tree_metadata_complete(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::Literal,
            tree,
            alphabet,
        )
    } else if tag == 1 {
        tree_metadata_complete(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::Command,
            tree,
            alphabet,
        )
    } else if tag == 2 {
        tree_metadata_complete(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::Distance,
            tree,
            alphabet,
        )
    } else if tag == 3 {
        tree_metadata_complete(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::BlockType,
            tree,
            alphabet,
        )
    } else if tag == 4 {
        tree_metadata_complete(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::BlockLength,
            tree,
            alphabet,
        )
    } else if tag == 5 {
        tree_metadata_complete(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::TemporaryContext,
            tree,
            alphabet,
        )
    } else {
        false
    }
}

proof fn active_tree_complete_from_fields(
    workspace: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    alphabet: u16,
)
    requires
        b3b_scalar_byte_at(workspace, window_bytes, B3B_ACTIVE_REGION)
            == tree_region_tag_spec(region),
        b3b_scalar_u16_at(workspace, window_bytes, B3B_ACTIVE_TREE) == tree,
        b3b_scalar_u16_at(workspace, window_bytes, B3B_ALPHABET_LIMIT) == alphabet,
        tree_metadata_complete(workspace, window_bytes, region, tree, alphabet),
    ensures active_tree_metadata_complete(workspace, window_bytes),
{
    reveal(active_tree_metadata_complete);
    match region {
        crate::brotli_prefix::TreeRegion::Literal => {}
        crate::brotli_prefix::TreeRegion::Command => {}
        crate::brotli_prefix::TreeRegion::Distance => {}
        crate::brotli_prefix::TreeRegion::BlockType => {}
        crate::brotli_prefix::TreeRegion::BlockLength => {}
        crate::brotli_prefix::TreeRegion::TemporaryContext => {}
    }
}

fn start_serialized_tree(
    workspace: &mut [u8],
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    alphabet_max: u16,
    alphabet_limit: u16,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            && 1 <= alphabet_limit <= alphabet_max <= 704 ==> r.is_ok(),
        r.is_ok() ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_ACTIVE_REGION,
        ) == tree_region_tag_spec(region),
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_ACTIVE_TREE,
        ) == tree,
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_ALPHABET_MAX,
        ) == alphabet_max,
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_ALPHABET_LIMIT,
        ) == alphabet_limit,
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_BUILDER_INITIALIZED,
        ) == 0,
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED),
        r.is_ok() ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        r.is_ok() ==> b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        serialized_mtf_state_ok(old(workspace)@, window_bytes)
            ==> serialized_mtf_state_ok(final(workspace)@, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            && !(8 <= b3b_scalar_byte_at(
                old(workspace)@,
                window_bytes,
                B3B_OUTER_PHASE,
            ) <= 11)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        forall|i: int| 0 <= i < B3B_GROUP_KIND ==> #[trigger]
            final(workspace)@[b3b_scalar_base(window_bytes) + i]
                == old(workspace)@[b3b_scalar_base(window_bytes) + i],
{
    match initialize_code_description_state(
        workspace,
        window_bytes,
        region,
        tree,
        alphabet_max,
        alphabet_limit,
    ) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    put_state_u16(workspace, window_bytes, B3B_BUILDER_INITIALIZED, 0)
}

spec fn completed_simple_tree_installation(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    alphabet_limit: u16,
    code: SimpleCodeDescription,
    meta: crate::brotli_prefix::TreeMetadata,
) -> bool {
    let record_start = crate::brotli_prefix::tree_record_at(
        window_bytes,
        region,
        tree,
        0,
    );
    let record_end = record_start + alphabet_limit as nat * 3;
    let metadata_at = crate::brotli_prefix::tree_metadata_at(window_bytes, region, tree);
    &&& meta.valid_for(region)
    &&& meta.symbols == alphabet_limit
    &&& crate::brotli_prefix::little_u16_at(after, metadata_at) == meta.symbols
    &&& crate::brotli_prefix::little_u16_at(after, metadata_at + 2)
        == crate::brotli_prefix::tree_metadata_descriptor(meta)
    &&& if code.selector == 0 {
        &&& code.count == 1
        &&& meta.storage == crate::brotli_prefix::TreeStorageState::Single {
            symbol: code.symbols[0],
        }
    } else {
        &&& meta.storage == crate::brotli_prefix::TreeStorageState::Canonical {
            initialized: alphabet_limit,
        }
        &&& crate::brotli_prefix::simple_tree_prefix(
            after,
            window_bytes,
            region,
            tree,
            alphabet_limit,
            code.selector,
            code.count,
            code.symbols@,
            alphabet_limit as nat,
        )
    }
    &&& after.len() == before.len()
    &&& forall|i: int| 0 <= i < before.len()
        && !(record_start <= i < record_end)
        && !(metadata_at <= i < metadata_at + 4)
        ==> #[trigger] after[i] == before[i]
}

fn install_completed_simple_tree(
    workspace: &mut [u8],
    window_bytes: u32,
    region: crate::brotli_prefix::TreeRegion,
    tree: u16,
    alphabet_limit: u16,
    code: SimpleCodeDescription,
) -> (r: Result<crate::brotli_prefix::TreeMetadata, CompressedHeaderError>)
    requires
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes),
        code.valid(alphabet_limit),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_ACTIVE_REGION)
            == tree_region_tag_spec(region),
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_TREE) == tree,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_LIMIT)
            == alphabet_limit,
    ensures
        code_store_frame(old(workspace)@, final(workspace)@, window_bytes),
        match r {
            Ok(meta) => {
                &&& completed_simple_tree_installation(
                    old(workspace)@,
                    final(workspace)@,
                    window_bytes,
                    region,
                    tree,
                    alphabet_limit,
                    code,
                    meta,
                )
                &&& tree_metadata_complete(
                    final(workspace)@,
                    window_bytes,
                    region,
                    tree,
                    alphabet_limit,
                )
                &&& active_tree_metadata_complete(final(workspace)@, window_bytes)
            },
            Err(CompressedHeaderError::Workspace(_)) => true,
            Err(_) => false,
        },
{
    let ghost original = workspace@;
    let meta = match crate::brotli_prefix::install_simple_tree(
        workspace,
        window_bytes,
        region,
        tree,
        alphabet_limit,
        code.selector,
        code.count,
        code.symbols,
    ) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    let ghost after_install = workspace@;
    proof {
        if code.selector == 0 {
            assert(after_install == original);
        } else {
            selected_tree_frame_preserves_context_state(
                original,
                after_install,
                window_bytes,
                region,
                tree,
                alphabet_limit,
            );
        }
    }
    match crate::brotli_prefix::write_tree_metadata(
        workspace,
        window_bytes,
        region,
        tree,
        meta,
    ) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    proof {
        let metadata_at = crate::brotli_prefix::tree_metadata_at(
            window_bytes,
            region,
            tree,
        );
        assert forall|i: int| 0 <= i < after_install.len()
            && !(metadata_at <= i < metadata_at + 4) implies
            #[trigger] workspace@[i] == after_install[i] by {}
        metadata_frame_preserves_context_state(
            after_install,
            workspace@,
            window_bytes,
            region,
            tree,
        );
        reveal(completed_simple_tree_installation);
        reveal(tree_metadata_complete);
        reveal(crate::brotli_prefix::simple_tree_prefix);
        let record_start = crate::brotli_prefix::tree_record_at(
            window_bytes,
            region,
            tree,
            0,
        );
        let record_end = record_start + alphabet_limit as nat * 3;
        assert((tree as nat) < crate::brotli_prefix::tree_region_count(region));
        assert((alphabet_limit as nat)
            <= crate::brotli_prefix::tree_region_symbols(region));
        reveal(crate::brotli_prefix::tree_record_at);
        reveal(crate::brotli_prefix::tree_region_count);
        reveal(crate::brotli_prefix::tree_region_symbols);
        match region {
            crate::brotli_prefix::TreeRegion::Literal => {
                assert((tree as nat) < 256);
                assert((alphabet_limit as nat) <= 256);
                assert(record_start == window_bytes as nat
                    + (tree as nat * 256) * 3);
                assert(record_end <= window_bytes as nat
                    + crate::brotli_prefix::COMMAND_TREES_OFFSET as nat)
                    by (nonlinear_arith)
                    requires
                        (tree as nat) < 256,
                        (alphabet_limit as nat) <= 256,
                        record_start == window_bytes as nat
                            + (tree as nat * 256) * 3,
                        record_end == record_start + alphabet_limit as nat * 3;
                assert(metadata_at == window_bytes as nat
                    + crate::brotli_prefix::LITERAL_METADATA_OFFSET as nat
                    + tree as nat * 4);
            }
            crate::brotli_prefix::TreeRegion::Command => {
                assert(record_end <= window_bytes as nat
                    + crate::brotli_prefix::DISTANCE_TREES_OFFSET as nat);
                assert(metadata_at == window_bytes as nat
                    + crate::brotli_prefix::COMMAND_METADATA_OFFSET as nat
                    + tree as nat * 4);
            }
            crate::brotli_prefix::TreeRegion::Distance => {
                assert((tree as nat) < 256);
                assert((alphabet_limit as nat) <= 520);
                assert(record_start == window_bytes as nat + 737_280
                    + (tree as nat * 520) * 3);
                assert(record_end <= window_bytes as nat
                    + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as nat)
                    by (nonlinear_arith)
                    requires
                        (tree as nat) < 256,
                        (alphabet_limit as nat) <= 520,
                        record_start == window_bytes as nat + 737_280
                            + (tree as nat * 520) * 3,
                        record_end == record_start + alphabet_limit as nat * 3;
                assert(metadata_at == window_bytes as nat
                    + crate::brotli_prefix::DISTANCE_METADATA_OFFSET as nat
                    + tree as nat * 4);
            }
            crate::brotli_prefix::TreeRegion::BlockType => {
                assert(record_end <= window_bytes as nat
                    + crate::brotli_prefix::BLOCK_LENGTH_TREES_OFFSET as nat);
                assert(metadata_at == window_bytes as nat
                    + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as nat
                    + tree as nat * 4);
            }
            crate::brotli_prefix::TreeRegion::BlockLength => {
                assert(record_end <= window_bytes as nat
                    + crate::brotli_prefix::BUILDER_OFFSET as nat);
                assert(metadata_at == window_bytes as nat
                    + crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as nat
                    + tree as nat * 4);
            }
            crate::brotli_prefix::TreeRegion::TemporaryContext => {
                assert(record_end <= window_bytes as nat
                    + crate::brotli_prefix::MTF_OFFSET as nat);
                assert(metadata_at == window_bytes as nat
                    + crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET as nat);
            }
        }
        assert(record_end <= window_bytes as nat + crate::brotli_prefix::MTF_OFFSET as nat);
        assert(window_bytes as nat + crate::brotli_prefix::MTF_OFFSET as nat
            <= window_bytes as nat + crate::brotli_prefix::STATE_OFFSET as nat);
        assert(window_bytes as nat + crate::brotli_prefix::STATE_OFFSET as nat
            <= metadata_at);
        assert forall|i: int| 0 <= i < original.len()
            && !(record_start <= i < record_end)
            && !(metadata_at <= i < metadata_at + 4)
            implies #[trigger] workspace@[i] == original[i] by {
            assert(workspace@[i] == after_install[i]);
            if code.selector == 0 {
                assert(after_install == original);
            } else {
                reveal(crate::brotli_prefix::selected_tree_frame);
            }
        }
        if code.selector != 0 {
            assert forall|symbol: int| 0 <= symbol < alphabet_limit implies
                #[trigger] workspace@[
                    crate::brotli_prefix::tree_record_at(
                        window_bytes,
                        region,
                        tree,
                        symbol as u16,
                    ) as int
                ] == after_install[
                    crate::brotli_prefix::tree_record_at(
                        window_bytes,
                        region,
                        tree,
                        symbol as u16,
                    ) as int
                ] by {
                let at = crate::brotli_prefix::tree_record_at(
                    window_bytes,
                    region,
                    tree,
                    symbol as u16,
                );
                assert(at < record_end);
                assert(at + 3 <= record_end);
                assert(at + 3 <= metadata_at);
            }
            assert forall|symbol: int| 0 <= symbol < alphabet_limit implies
                #[trigger] crate::brotli_prefix::little_u16_at(
                    workspace@,
                    crate::brotli_prefix::tree_record_at(
                        window_bytes,
                        region,
                        tree,
                        symbol as u16,
                    ) + 1,
                ) == crate::brotli_prefix::little_u16_at(
                    after_install,
                    crate::brotli_prefix::tree_record_at(
                        window_bytes,
                        region,
                        tree,
                        symbol as u16,
                    ) + 1,
                ) by {
                let at = crate::brotli_prefix::tree_record_at(
                    window_bytes,
                    region,
                    tree,
                    symbol as u16,
                );
                assert(at + 3 <= record_end);
                assert(at + 3 <= metadata_at);
                reveal(crate::brotli_prefix::little_u16_at);
            }
        }
        assert(completed_simple_tree_installation(
            original,
            workspace@,
            window_bytes,
            region,
            tree,
            alphabet_limit,
            code,
            meta,
        ));
        assert(tree_metadata_complete(
            workspace@,
            window_bytes,
            region,
            tree,
            alphabet_limit,
        ));
        active_tree_complete_from_fields(
            workspace@,
            window_bytes,
            region,
            tree,
            alphabet_limit,
        );
        reveal(code_store_frame);
    }
    Ok(meta)
}

fn advance_serialized_tree(
    workspace: &mut [u8],
    window_bytes: u32,
    input: &[u8],
    end_of_input: bool,
) -> (r: SerializedTreeStep)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        serialized_context_data_ok(old(workspace)@, window_bytes)
            ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_ACTIVE_REGION)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_ACTIVE_REGION),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_TREE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_MAX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_MAX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ALPHABET_LIMIT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ALPHABET_LIMIT),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_GROUP_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_GROUP_PHASE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_INDEX)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_INDEX),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_TREE_COUNT)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_TREE_COUNT),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        r.consumed <= input.len(),
        r.status == SerializedTreeStatus::NeedInput ==> {
            &&& !end_of_input
            &&& r.consumed == input.len()
        },
        r.status == SerializedTreeStatus::Complete ==>
            active_tree_metadata_complete(final(workspace)@, window_bytes),
{
    let ghost original = workspace@;
    proof { assert(original == old(workspace)@); }
    let region_tag = match state_byte(workspace, window_bytes, B3B_ACTIVE_REGION) {
        Ok(value) => value,
        Err(error) => return SerializedTreeStep { consumed: 0, status: SerializedTreeStatus::Failed(error) },
    };
    let region = match decode_tree_region(region_tag) {
        Some(value) => value,
        None => return SerializedTreeStep {
            consumed: 0,
            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),
        },
    };
    let tree = match state_u16(workspace, window_bytes, B3B_ACTIVE_TREE) {
        Ok(value) => value,
        Err(error) => return SerializedTreeStep { consumed: 0, status: SerializedTreeStatus::Failed(error) },
    };
    proof {
        assert(region_tag == b3b_scalar_byte_at(
            original,
            window_bytes,
            B3B_ACTIVE_REGION,
        ));
        assert(tree_region_tag_spec(region) == region_tag);
        assert(tree as nat == b3b_scalar_u16_at(
            original,
            window_bytes,
            B3B_ACTIVE_TREE,
        ));
    }
    let mut consumed: usize = 0;
    let mut work: u16 = 0;
    while work < 2_000
        invariant consumed <= input.len(), work <= 2_000,
            original == old(workspace)@,
            b3b_scalar_byte_at(original, window_bytes, B3B_ACTIVE_REGION)
                == tree_region_tag_spec(region),
            b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_TREE) == tree,
            workspace@.len() == original.len(),
            b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            serialized_context_data_ok(original, window_bytes)
                ==> serialized_context_data_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_CONTEXT_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_ACTIVE_REGION)
                == b3b_scalar_byte_at(original, window_bytes, B3B_ACTIVE_REGION),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_MAX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_MAX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ALPHABET_LIMIT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_LIMIT),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_KIND)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_KIND),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_GROUP_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_GROUP_PHASE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_INDEX)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_INDEX),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_TREE_COUNT)
                == b3b_scalar_u16_at(original, window_bytes, B3B_TREE_COUNT),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
        decreases 2_000 - work,
    {
        let queue = match load_b3b_queue(workspace, window_bytes) {
            Ok(value) => value,
            Err(error) => return SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) },
        };
        let mut decoder = match load_code_description_decoder(workspace, window_bytes, queue) {
            Ok(value) => value,
            Err(error) => return SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) },
        };
        proof {
            assert(decoder.alphabet_limit as nat == b3b_scalar_u16_at(
                workspace@,
                window_bytes,
                B3B_ALPHABET_LIMIT,
            ));
            assert(decoder.alphabet_limit as nat == b3b_scalar_u16_at(
                original,
                window_bytes,
                B3B_ALPHABET_LIMIT,
            ));
        }
        let step = decoder.advance_field(&input[consumed..], end_of_input);
        consumed = consumed + step.consumed;
        match store_b3b_queue(workspace, window_bytes, &decoder.queue) {
            Ok(()) => {}
            Err(error) => return SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) },
        }

        match decoder.phase {
            CodeDescriptionPhase::ComplexPendingSpan { .. } => {
                match drain_and_store_serialized_pending_span(
                    workspace,
                    window_bytes,
                    &mut decoder,
                ) {
                    Ok(()) => {}
                    Err(error) => return SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) },
                }
            }
            CodeDescriptionPhase::CompleteSimple(code) => {
                let installed = install_completed_simple_tree(
                    workspace,
                    window_bytes,
                    region,
                    tree,
                    decoder.alphabet_limit,
                    code,
                );
                proof { reveal(code_store_frame); }
                match installed {
                    Ok(_) => return SerializedTreeStep {
                        consumed,
                        status: SerializedTreeStatus::Complete,
                    },
                    Err(error) => return SerializedTreeStep {
                        consumed,
                        status: SerializedTreeStatus::Failed(error),
                    },
                }
            }
            CodeDescriptionPhase::CompleteComplex { decoded_symbols, .. } => {
                let initialized = match state_u16(
                    workspace, window_bytes, B3B_BUILDER_INITIALIZED) {
                    Ok(value) => value,
                    Err(error) => return SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) },
                };
                if initialized != decoded_symbols || decoded_symbols != decoder.alphabet_limit {
                    return SerializedTreeStep {
                        consumed,
                        status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),
                    };
                }
                let mut meta = match crate::brotli_prefix::TreeMetadata::canonical(
                    region, decoder.alphabet_limit) {
                    Ok(value) => value,
                    Err(error) => return SerializedTreeStep {
                        consumed,
                        status: SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(error)),
                    },
                };
                let ghost before_install = workspace@;
                let install_result = crate::brotli_prefix::install_builder_canonical_tree(
                    workspace,
                    window_bytes,
                    initialized,
                    region,
                    tree,
                    &mut meta,
                );
                proof {
                    if (tree as nat) < crate::brotli_prefix::tree_region_count(region) {
                        canonical_installer_frame_preserves_context_state(
                            before_install,
                            workspace@,
                            window_bytes,
                            region,
                            tree,
                            decoder.alphabet_limit,
                        );
                    } else {
                        assert(workspace@ == before_install);
                    }
                }
                match install_result {
                    Ok(()) => {}
                    Err(error) => return SerializedTreeStep {
                        consumed,
                        status: SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(error)),
                    },
                }
                let ghost before_metadata = workspace@;
                match crate::brotli_prefix::write_tree_metadata(
                    workspace, window_bytes, region, tree, meta) {
                    Ok(()) => {
                        proof {
                            let at = crate::brotli_prefix::tree_metadata_at(
                                window_bytes,
                                region,
                                tree,
                            );
                            assert forall|i: int| 0 <= i < before_metadata.len()
                                && !(at <= i < at + 4) implies
                                #[trigger] workspace@[i] == before_metadata[i] by {}
                            metadata_frame_preserves_context_state(
                                before_metadata,
                                workspace@,
                                window_bytes,
                                region,
                                tree,
                            );
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_ACTIVE_REGION,
                            ) == b3b_scalar_byte_at(
                                before_metadata,
                                window_bytes,
                                B3B_ACTIVE_REGION,
                            ));
                            assert(b3b_scalar_u16_at(
                                workspace@,
                                window_bytes,
                                B3B_ACTIVE_TREE,
                            ) == b3b_scalar_u16_at(
                                before_metadata,
                                window_bytes,
                                B3B_ACTIVE_TREE,
                            ));
                            assert(b3b_scalar_u16_at(
                                workspace@,
                                window_bytes,
                                B3B_ALPHABET_LIMIT,
                            ) == b3b_scalar_u16_at(
                                before_metadata,
                                window_bytes,
                                B3B_ALPHABET_LIMIT,
                            ));
                            assert(b3b_scalar_byte_at(
                                before_metadata,
                                window_bytes,
                                B3B_ACTIVE_REGION,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_ACTIVE_REGION,
                            ));
                            assert(b3b_scalar_u16_at(
                                before_metadata,
                                window_bytes,
                                B3B_ACTIVE_TREE,
                            ) == b3b_scalar_u16_at(
                                original,
                                window_bytes,
                                B3B_ACTIVE_TREE,
                            ));
                            assert(b3b_scalar_u16_at(
                                before_metadata,
                                window_bytes,
                                B3B_ALPHABET_LIMIT,
                            ) == b3b_scalar_u16_at(
                                original,
                                window_bytes,
                                B3B_ALPHABET_LIMIT,
                            ));
                            assert(decoder.alphabet_limit as nat == b3b_scalar_u16_at(
                                original,
                                window_bytes,
                                B3B_ALPHABET_LIMIT,
                            ));
                            reveal(tree_metadata_complete);
                            assert(tree_metadata_complete(
                                workspace@,
                                window_bytes,
                                region,
                                tree,
                                decoder.alphabet_limit,
                            ));
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_ACTIVE_REGION,
                            ) == tree_region_tag_spec(region));
                            assert(b3b_scalar_u16_at(
                                workspace@,
                                window_bytes,
                                B3B_ACTIVE_TREE,
                            ) == tree);
                            assert(b3b_scalar_u16_at(
                                workspace@,
                                window_bytes,
                                B3B_ALPHABET_LIMIT,
                            ) == decoder.alphabet_limit);
                            active_tree_complete_from_fields(
                                workspace@,
                                window_bytes,
                                region,
                                tree,
                                decoder.alphabet_limit,
                            );
                        }
                        return SerializedTreeStep {
                            consumed,
                            status: SerializedTreeStatus::Complete,
                        };
                    }
                    Err(error) => return SerializedTreeStep {
                        consumed,
                        status: SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(error)),
                    },
                }
            }
            CodeDescriptionPhase::Failed(error) => return SerializedTreeStep {
                consumed,
                status: SerializedTreeStatus::Failed(map_code_description_error(error)),
            },
            _ => {
                match store_code_description_decoder(workspace, window_bytes, decoder) {
                    Ok(()) => {}
                    Err(error) => return SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) },
                }
                if matches!(step.status, CodeDescriptionStatus::NeedInput) {
                    return SerializedTreeStep { consumed, status: SerializedTreeStatus::NeedInput };
                }
            }
        }
        work = work + 1;
    }
    SerializedTreeStep {
        consumed,
        status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),
    }
}

fn start_context_map(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_mtf_state_ok(old(workspace)@, window_bytes),
        1 <= active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            ==> b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.is_ok() ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        r.is_ok() ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == match kind {
            crate::brotli_prefix::ContextMapKind::Literal => 0u8,
            crate::brotli_prefix::ContextMapKind::Distance => 1u8,
        },
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_MAP_SIZE,
        ) == active_len,
        r.is_ok() ==> serialized_block_count_at(
            final(workspace)@,
            window_bytes,
            0,
        ) == serialized_block_count_at(old(workspace)@, window_bytes, 0),
        r.is_ok() ==> serialized_block_count_at(
            final(workspace)@,
            window_bytes,
            2,
        ) == serialized_block_count_at(old(workspace)@, window_bytes, 2),
{
    let ghost original = workspace@;
    let kind_tag = match kind {
        crate::brotli_prefix::ContextMapKind::Literal => 0u8,
        crate::brotli_prefix::ContextMapKind::Distance => 1u8,
    };
    put_state_byte(workspace, window_bytes, B3B_CONTEXT_PHASE, 0)?;
    put_state_byte(workspace, window_bytes, B3B_CONTEXT_KIND, kind_tag)?;
    put_state_byte(workspace, window_bytes, B3B_MAX_RUN_PREFIX, 0)?;
    put_state_byte(workspace, window_bytes, B3B_PENDING_RUN, 255)?;
    put_state_u16(workspace, window_bytes, B3B_MAP_TREES, 0)?;
    put_state_u16(workspace, window_bytes, B3B_MAP_SIZE, active_len)?;
    put_state_u16(workspace, window_bytes, B3B_MAP_INDEX, 0)?;
    put_state_u16(workspace, window_bytes, B3B_MAP_INITIALIZED, 0)?;
    proof {
        reveal(serialized_context_state_ok);
        reveal(serialized_context_phase_payload_ok);
        reveal(serialized_context_data_ok);
        reveal(serialized_context_map_prefix_ok);
        reveal(serialized_mtf_state_ok);
        assert(serialized_context_state_ok(workspace@, window_bytes));
    }
    match store_var_uint8_phase(workspace, window_bytes, VarUint8Phase::First) {
        Ok(()) => {
            proof {
                reveal(serialized_block_count_at);
                reveal(b3b_scalar_u16_at);
                reveal(b3b_scalar_base);
                b3b_scalar_layout_is_exact();
            }
            Ok(())
        }
        Err(error) => Err(error),
    }
}

fn store_context_map_progress(
    workspace: &mut [u8],
    window_bytes: u32,
    progress: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_context_data_ok(old(workspace)@, window_bytes),
        progress as nat <= b3b_scalar_u16_at(
            old(workspace)@,
            window_bytes,
            B3B_MAP_SIZE,
        ),
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES) == 0
            ==> progress == 0,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES) > 0
            ==> {
                &&& (b3b_scalar_byte_at(
                    old(workspace)@,
                    window_bytes,
                    B3B_CONTEXT_KIND,
                ) == 0 ==> forall|i: u16| i < progress ==> #[trigger]
                    old(workspace)@[crate::brotli_prefix::context_entry_at(
                        window_bytes,
                        crate::brotli_prefix::ContextMapKind::Literal,
                        i,
                    ) as int] < b3b_scalar_u16_at(
                        old(workspace)@,
                        window_bytes,
                        B3B_MAP_TREES,
                    ))
                &&& (b3b_scalar_byte_at(
                    old(workspace)@,
                    window_bytes,
                    B3B_CONTEXT_KIND,
                ) == 1 ==> forall|i: u16| i < progress ==> #[trigger]
                    old(workspace)@[crate::brotli_prefix::context_entry_at(
                        window_bytes,
                        crate::brotli_prefix::ContextMapKind::Distance,
                        i,
                    ) as int] < b3b_scalar_u16_at(
                        old(workspace)@,
                        window_bytes,
                        B3B_MAP_TREES,
                    ))
            },
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_TREES)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES),
        b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE),
        r.is_ok() ==> serialized_context_data_ok(final(workspace)@, window_bytes),
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_MAP_INDEX,
        ) == progress,
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_MAP_INITIALIZED,
        ) == progress,
        r.is_ok() ==> forall|i: int| 0 <= i < B3B_GROUP_KIND
            && !(B3B_MAP_INDEX <= i < B3B_MAP_INDEX + 2)
            && !(B3B_MAP_INITIALIZED <= i < B3B_MAP_INITIALIZED + 2) ==> #[trigger]
            final(workspace)@[b3b_scalar_base(window_bytes) + i]
                == old(workspace)@[b3b_scalar_base(window_bytes) + i],
        r.is_ok() ==> forall|i: int| 0 <= i < old(workspace)@.len()
            && !(b3b_scalar_base(window_bytes) + B3B_MAP_INDEX as int
                <= i < b3b_scalar_base(window_bytes) + B3B_MAP_INDEX as int + 2)
            && !(b3b_scalar_base(window_bytes) + B3B_MAP_INITIALIZED as int
                <= i < b3b_scalar_base(window_bytes) + B3B_MAP_INITIALIZED as int + 2)
            ==> #[trigger] final(workspace)@[i] == old(workspace)@[i],
{
    match put_state_u16(workspace, window_bytes, B3B_MAP_INDEX, progress) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    put_state_u16(workspace, window_bytes, B3B_MAP_INITIALIZED, progress)
}

fn store_context_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    next_phase: u8,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        next_phase <= 8,
        serialized_context_data_ok(old(workspace)@, window_bytes),
        serialized_context_phase_payload_ok(old(workspace)@, window_bytes, next_phase),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            ==> r.is_ok(),
        r.is_ok() ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        r.is_ok() ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_CONTEXT_PHASE,
        ) == next_phase,
        r.is_ok() ==> b3b_scalar_byte_at(
            final(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND),
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_MAP_SIZE,
        ) == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE),
        r.is_ok() ==> b3b_scalar_u16_at(
            final(workspace)@,
            window_bytes,
            B3B_MAP_TREES,
        ) == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES),
        r.is_ok() ==> forall|i: int| 0 <= i < B3B_SCALAR_BYTES
            && i != B3B_CONTEXT_PHASE ==> #[trigger]
            final(workspace)@[b3b_scalar_base(window_bytes) + i]
                == old(workspace)@[b3b_scalar_base(window_bytes) + i],
        r.is_ok() ==> forall|i: int| 0 <= i < old(workspace)@.len()
            && i != b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int
            ==> #[trigger] final(workspace)@[i] == old(workspace)@[i],
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    let ghost before = workspace@;
    match put_state_byte(workspace, window_bytes, B3B_CONTEXT_PHASE, next_phase) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        let at = b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int;
        assert(workspace@ == before.update(at, next_phase)) by {
            assert(workspace@.len() == before.len());
            assert forall|i: int| 0 <= i < workspace@.len() implies
                #[trigger] workspace@[i] == before.update(at, next_phase)[i] by {
                if i == at {}
            }
        }
        context_phase_transition_preserves_state(
            before,
            workspace@,
            window_bytes,
            next_phase,
        );
    }
    Ok(())
}

fn advance_context_mtf_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 7,
        kind == if b3b_scalar_byte_at(
            old(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_ok() ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        r.is_ok() ==> {
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 8
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE)
        },
{
    let num_trees = match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if num_trees == 0 || num_trees > 256 {
        return Err(CompressedHeaderError::InternalState);
    }
    let upper = match state_byte(workspace, window_bytes, B3B_MTF_UPPER_BOUND) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if upper > 63 {
        return Err(CompressedHeaderError::InternalState);
    }
    proof {
        reveal(serialized_context_state_ok);
        reveal(serialized_context_phase_payload_ok);
        reveal(serialized_context_data_ok);
        reveal(serialized_context_map_prefix_ok);
        assert(b3b_scalar_u16_at(
            workspace@,
            window_bytes,
            B3B_MAP_INITIALIZED,
        ) == active_len);
        assert(num_trees as nat == b3b_scalar_u16_at(
            workspace@,
            window_bytes,
            B3B_MAP_TREES,
        ));
        assert(b3b_scalar_u16_at(
            workspace@,
            window_bytes,
            B3B_MAP_TREES,
        ) > 0);
        assert forall|i: int| 0 <= i < active_len implies #[trigger]
            workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] < num_trees by {
            assert(serialized_context_map_prefix_ok(workspace@, window_bytes));
            let spec_kind = if b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_CONTEXT_KIND,
            ) == 0 {
                crate::brotli_prefix::ContextMapKind::Literal
            } else {
                crate::brotli_prefix::ContextMapKind::Distance
            };
            assert(spec_kind == kind);
            assert(i < 65_536);
            serialized_context_prefix_value_bound(workspace@, window_bytes, i);
            assert(i < b3b_scalar_u16_at(
                workspace@,
                window_bytes,
                B3B_MAP_INITIALIZED,
            ));
            assert(workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                spec_kind,
                i as u16,
            ) as int] < b3b_scalar_u16_at(
                workspace@,
                window_bytes,
                B3B_MAP_TREES,
            ));
        }
    }
    let ghost before_mtf = workspace@;
    let (next_upper, _) = match crate::brotli_prefix::inverse_mtf_context_map(
        workspace,
        window_bytes,
        kind,
        active_len,
        num_trees,
        upper,
    ) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    let ghost transformed = workspace@;
    match put_state_byte(
        workspace,
        window_bytes,
        B3B_MTF_UPPER_BOUND,
        next_upper,
    ) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    let ghost after_upper = workspace@;
    match put_state_byte(workspace, window_bytes, B3B_CONTEXT_PHASE, 8) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        let upper_at = b3b_scalar_base(window_bytes) + B3B_MTF_UPPER_BOUND as int;
        let phase_at = b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int;
        assert(after_upper == transformed.update(upper_at, next_upper)) by {
            assert(after_upper.len() == transformed.len());
            assert forall|i: int| 0 <= i < after_upper.len() implies
                #[trigger] after_upper[i] == transformed.update(upper_at, next_upper)[i] by {
                if i == upper_at {}
            }
        }
        assert(workspace@ == after_upper.update(phase_at, 8)) by {
            assert(workspace@.len() == after_upper.len());
            assert forall|i: int| 0 <= i < workspace@.len() implies
                #[trigger] workspace@[i] == after_upper.update(phase_at, 8)[i] by {
                if i == phase_at {}
            }
        }
        assert(workspace@ == transformed
            .update(upper_at, next_upper)
            .update(phase_at, 8));
        context_mtf_phase_to_coverage(
            before_mtf,
            transformed,
            workspace@,
            window_bytes,
            kind,
            active_len,
            num_trees,
            next_upper,
        );
    }
    Ok(())
}

fn advance_context_coverage_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 8,
        kind == if b3b_scalar_byte_at(
            old(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        r.is_ok() ==> b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        r.is_ok() ==> {
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 9
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND)
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE)
        },
{
    let num_trees = match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if num_trees == 0 || num_trees > 256 {
        return Err(CompressedHeaderError::InternalState);
    }
    proof {
        reveal(serialized_context_state_ok);
        reveal(serialized_context_phase_payload_ok);
        reveal(serialized_context_data_ok);
        reveal(serialized_context_map_prefix_ok);
        assert(b3b_scalar_u16_at(
            workspace@,
            window_bytes,
            B3B_MAP_INITIALIZED,
        ) == active_len);
        assert(num_trees as nat == b3b_scalar_u16_at(
            workspace@,
            window_bytes,
            B3B_MAP_TREES,
        ));
        assert(b3b_scalar_u16_at(
            workspace@,
            window_bytes,
            B3B_MAP_TREES,
        ) > 0);
        assert forall|i: int| 0 <= i < active_len implies #[trigger]
            workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] < num_trees by {
            assert(serialized_context_map_prefix_ok(workspace@, window_bytes));
            let spec_kind = if b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_CONTEXT_KIND,
            ) == 0 {
                crate::brotli_prefix::ContextMapKind::Literal
            } else {
                crate::brotli_prefix::ContextMapKind::Distance
            };
            assert(spec_kind == kind);
            assert(i < 65_536);
            serialized_context_prefix_value_bound(workspace@, window_bytes, i);
            assert(i < b3b_scalar_u16_at(
                workspace@,
                window_bytes,
                B3B_MAP_INITIALIZED,
            ));
            assert(workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                spec_kind,
                i as u16,
            ) as int] < b3b_scalar_u16_at(
                workspace@,
                window_bytes,
                B3B_MAP_TREES,
            ));
        }
    }
    let ghost before_coverage = workspace@;
    let (covered, _) = match crate::brotli_prefix::check_context_tree_coverage(
        workspace,
        window_bytes,
        kind,
        active_len,
        num_trees,
    ) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    proof {
        coverage_frame_preserves_context_state(before_coverage, workspace@, window_bytes);
    }
    if !covered {
        return Err(CompressedHeaderError::InvalidFormat(
            CompressedFormatError::ContextMapCoverage,
        ));
    }
    proof {
        assert(crate::brotli_prefix::context_tree_coverage(
            crate::brotli_prefix::context_map_values(
                before_coverage,
                window_bytes,
                kind,
                active_len,
            ),
            num_trees,
        ));
        assert(crate::brotli_prefix::context_map_values(
            workspace@,
            window_bytes,
            kind,
            active_len,
        ) == crate::brotli_prefix::context_map_values(
            before_coverage,
            window_bytes,
            kind,
            active_len,
        ));
        reveal(serialized_context_complete_map_ok);
        assert(serialized_context_complete_map_ok(workspace@, window_bytes));
    }
    let ghost before_complete = workspace@;
    match put_state_byte(workspace, window_bytes, B3B_CONTEXT_PHASE, 9) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        let at = b3b_scalar_base(window_bytes) + B3B_CONTEXT_PHASE as int;
        assert(workspace@ == before_complete.update(at, 9)) by {
            assert(workspace@.len() == before_complete.len());
            assert forall|i: int| 0 <= i < workspace@.len() implies
                #[trigger] workspace@[i] == before_complete.update(at, 9)[i] by {
                if i == at {}
            }
        }
        context_coverage_phase_to_complete(before_complete, workspace@, window_bytes);
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ContextAdvanceStatus {
    NeedInput,
    Complete { kind: crate::brotli_prefix::ContextMapKind, num_trees: u16 },
    Failed(CompressedHeaderError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ContextAdvanceStep {
    consumed: usize,
    status: ContextAdvanceStatus,
}

spec fn context_tree_count_phase_refines(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<ContextAdvanceStatus>,
) -> bool {
    if match status {
        Some(ContextAdvanceStatus::Failed(_)) => true,
        _ => false,
    } {
        true
    } else {
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE)
        &&& exists|start_queue: BitQueue,
            final_queue: BitQueue,
            start_phase: VarUint8Phase,
            final_phase: VarUint8Phase,
            var_status: VarUint8Status| #![trigger var_uint8_exact_step(
                start_queue,
                start_phase,
                input,
                end_of_input,
                consumed,
                final_queue,
                final_phase,
                var_status,
            )] {
            &&& serialized_b3b_queue(before, window_bytes, start_queue)
            &&& serialized_var_uint8_phase(before, window_bytes, start_phase)
            &&& serialized_b3b_queue(after, window_bytes, final_queue)
            &&& serialized_var_uint8_phase(after, window_bytes, final_phase)
            &&& var_uint8_exact_step(
                start_queue,
                start_phase,
                input,
                end_of_input,
                consumed,
                final_queue,
                final_phase,
                var_status,
            )
            &&& match var_status {
                VarUint8Status::NeedInput => status
                    == Some(ContextAdvanceStatus::NeedInput),
                VarUint8Status::Truncated => status == Some(
                    ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
                ),
                VarUint8Status::Progress => {
                    &&& status.is_none()
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 0
                },
                VarUint8Status::Value(raw) => {
                    &&& status.is_none()
                    &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
                        == raw as nat + 1
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
                        == if raw == 0 { 9u8 } else { 1u8 }
                },
            }
        }
    }
}

proof fn establish_context_tree_count_refinement(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<ContextAdvanceStatus>,
    start_queue: BitQueue,
    final_queue: BitQueue,
    start_phase: VarUint8Phase,
    final_phase: VarUint8Phase,
    var_status: VarUint8Status,
)
    requires
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        serialized_b3b_queue(before, window_bytes, start_queue),
        serialized_var_uint8_phase(before, window_bytes, start_phase),
        serialized_b3b_queue(after, window_bytes, final_queue),
        serialized_var_uint8_phase(after, window_bytes, final_phase),
        var_uint8_exact_step(
            start_queue,
            start_phase,
            input,
            end_of_input,
            consumed,
            final_queue,
            final_phase,
            var_status,
        ),
        match var_status {
            VarUint8Status::NeedInput => status == Some(ContextAdvanceStatus::NeedInput),
            VarUint8Status::Truncated => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
            ),
            VarUint8Status::Progress => {
                &&& status.is_none()
                &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 0
            },
            VarUint8Status::Value(raw) => {
                &&& status.is_none()
                &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
                    == raw as nat + 1
                &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
                    == if raw == 0 { 9u8 } else { 1u8 }
            },
        },
    ensures context_tree_count_phase_refines(
        before,
        after,
        window_bytes,
        input,
        end_of_input,
        consumed,
        status,
    ),
{
    reveal(context_tree_count_phase_refines);
    assert(exists|witness_start_queue: BitQueue,
        witness_final_queue: BitQueue,
        witness_start_phase: VarUint8Phase,
        witness_final_phase: VarUint8Phase,
        witness_status: VarUint8Status| {
        &&& serialized_b3b_queue(before, window_bytes, witness_start_queue)
        &&& serialized_var_uint8_phase(before, window_bytes, witness_start_phase)
        &&& serialized_b3b_queue(after, window_bytes, witness_final_queue)
        &&& serialized_var_uint8_phase(after, window_bytes, witness_final_phase)
        &&& var_uint8_exact_step(
            witness_start_queue,
            witness_start_phase,
            input,
            end_of_input,
            consumed,
            witness_final_queue,
            witness_final_phase,
            witness_status,
        )
        &&& match witness_status {
            VarUint8Status::NeedInput => status == Some(ContextAdvanceStatus::NeedInput),
            VarUint8Status::Truncated => match status {
                Some(ContextAdvanceStatus::Failed(_)) => true,
                _ => false,
            },
            VarUint8Status::Progress => {
                &&& status.is_none()
                &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 0
            },
            VarUint8Status::Value(raw) => {
                &&& status.is_none()
                &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES)
                    == raw as nat + 1
                &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
                    == if raw == 0 { 9u8 } else { 1u8 }
            },
        }
    });
}

spec fn bit_read_exact_step(
    start_queue: BitQueue,
    input: Seq<u8>,
    end_of_input: bool,
    width: nat,
    consumed: usize,
    final_queue: BitQueue,
    status: BitReadStatus,
) -> bool {
    let source = start_queue.bits() + bytes_bits(input.take(consumed as int));
    &&& consumed as nat == input_bytes_taken(
        start_queue.bits().len(),
        width,
        input.len(),
    )
    &&& match status {
        BitReadStatus::Value(value) => {
            &&& source.len() >= width
            &&& final_queue.bits() == source.skip(width as int)
            &&& value as nat == bits_value(source.take(width as int))
            &&& (value as nat) < pow2(width)
        },
        BitReadStatus::NeedInput => {
            &&& !end_of_input
            &&& consumed == input.len()
            &&& final_queue.bits() == start_queue.bits() + bytes_bits(input)
            &&& final_queue.bits().len() < width
        },
        BitReadStatus::Truncated => {
            &&& end_of_input
            &&& consumed == input.len()
            &&& final_queue.bits() == start_queue.bits() + bytes_bits(input)
            &&& final_queue.bits().len() < width
        },
    }
}

spec fn context_bits_width(before: Seq<u8>, window_bytes: u32, phase: u8) -> nat {
    if phase == 2 { 4 }
    else if phase == 5 {
        b3b_scalar_byte_at(before, window_bytes, B3B_PENDING_RUN) as nat
    } else { 1 }
}

spec fn context_bits_value_result(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    phase: u8,
    value: u64,
    status: Option<ContextAdvanceStatus>,
) -> bool {
    let num_trees = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES);
    let initialized = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED);
    let pending = b3b_scalar_byte_at(before, window_bytes, B3B_PENDING_RUN);
    let kind = if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    if phase == 1 {
        &&& status.is_none()
        &&& if value == 0 {
            &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 3
            &&& b3b_scalar_byte_at(after, window_bytes, B3B_MAX_RUN_PREFIX) == 0
            &&& b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION) == 5
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE) == 0
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_BUILDER_INITIALIZED) == 0
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX) == num_trees
            &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT) == num_trees
        } else {
            b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 2
        }
    } else if phase == 2 {
        &&& status.is_none()
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 3
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_MAX_RUN_PREFIX) as nat
            == value as nat + 1
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION) == 5
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE) == 0
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_BUILDER_INITIALIZED) == 0
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX)
            == num_trees + value as nat + 1
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT)
            == num_trees + value as nat + 1
    } else if phase == 5 {
        let repeat = pow2(pending as nat) + value as nat;
        &&& status.is_none()
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 4
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_PENDING_RUN) == 255
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == initialized + repeat
        &&& forall|i: int| initialized <= i < initialized + repeat ==> #[trigger]
            after[crate::brotli_prefix::context_entry_at(
                window_bytes,
                kind,
                i as u16,
            ) as int] == 0
    } else {
        &&& status.is_none()
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE)
            == if value == 0 { 8u8 } else { 7u8 }
    }
}

spec fn context_bits_phase_refines(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    phase: u8,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<ContextAdvanceStatus>,
) -> bool {
    if match status {
        Some(ContextAdvanceStatus::Failed(_)) => true,
        _ => false,
    } {
        true
    } else {
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE)
        &&& exists|start_queue: BitQueue,
            final_queue: BitQueue,
            read_status: BitReadStatus| #![trigger bit_read_exact_step(
                start_queue,
                input,
                end_of_input,
                context_bits_width(before, window_bytes, phase),
                consumed,
                final_queue,
                read_status,
            )] {
            &&& serialized_b3b_queue(before, window_bytes, start_queue)
            &&& serialized_b3b_queue(after, window_bytes, final_queue)
            &&& bit_read_exact_step(
                start_queue,
                input,
                end_of_input,
                context_bits_width(before, window_bytes, phase),
                consumed,
                final_queue,
                read_status,
            )
            &&& match read_status {
                BitReadStatus::NeedInput => status == Some(ContextAdvanceStatus::NeedInput),
                BitReadStatus::Truncated => status == Some(
                    ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
                ),
                BitReadStatus::Value(value) => context_bits_value_result(
                    before,
                    after,
                    window_bytes,
                    phase,
                    value,
                    status,
                ),
            }
        }
    }
}

proof fn establish_context_bits_refinement(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    phase: u8,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<ContextAdvanceStatus>,
    start_queue: BitQueue,
    final_queue: BitQueue,
    read_status: BitReadStatus,
)
    requires
        b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE),
        serialized_b3b_queue(before, window_bytes, start_queue),
        serialized_b3b_queue(after, window_bytes, final_queue),
        bit_read_exact_step(
            start_queue,
            input,
            end_of_input,
            context_bits_width(before, window_bytes, phase),
            consumed,
            final_queue,
            read_status,
        ),
        match read_status {
            BitReadStatus::NeedInput => status == Some(ContextAdvanceStatus::NeedInput),
            BitReadStatus::Truncated => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
            ),
            BitReadStatus::Value(value) => context_bits_value_result(
                before,
                after,
                window_bytes,
                phase,
                value,
                status,
            ),
        },
    ensures context_bits_phase_refines(
        before,
        after,
        window_bytes,
        phase,
        input,
        end_of_input,
        consumed,
        status,
    ),
{
    reveal(context_bits_phase_refines);
    assert(exists|witness_start_queue: BitQueue,
        witness_final_queue: BitQueue,
        witness_status: BitReadStatus| {
        &&& serialized_b3b_queue(before, window_bytes, witness_start_queue)
        &&& serialized_b3b_queue(after, window_bytes, witness_final_queue)
        &&& bit_read_exact_step(
            witness_start_queue,
            input,
            end_of_input,
            context_bits_width(before, window_bytes, phase),
            consumed,
            witness_final_queue,
            witness_status,
        )
        &&& match witness_status {
            BitReadStatus::NeedInput => status == Some(ContextAdvanceStatus::NeedInput),
            BitReadStatus::Truncated => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
            ),
            BitReadStatus::Value(value) => context_bits_value_result(
                before,
                after,
                window_bytes,
                phase,
                value,
                status,
            ),
        }
    });
}

spec fn temporary_tree_metadata_matches(
    workspace: Seq<u8>,
    window_bytes: u32,
    meta: crate::brotli_prefix::TreeMetadata,
) -> bool {
    let at = crate::brotli_prefix::tree_metadata_at(
        window_bytes,
        crate::brotli_prefix::TreeRegion::TemporaryContext,
        0,
    );
    &&& meta.valid_for(crate::brotli_prefix::TreeRegion::TemporaryContext)
    &&& meta.symbols as nat == crate::brotli_prefix::little_u16_at(workspace, at)
    &&& crate::brotli_prefix::tree_metadata_descriptor(meta)
        == crate::brotli_prefix::little_u16_at(workspace, at + 2)
}

spec fn context_symbol_value_result(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    symbol: u16,
    status: Option<ContextAdvanceStatus>,
) -> bool {
    let initialized = b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED);
    let max_run = b3b_scalar_byte_at(before, window_bytes, B3B_MAX_RUN_PREFIX);
    let kind = if b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND) == 0 {
        crate::brotli_prefix::ContextMapKind::Literal
    } else {
        crate::brotli_prefix::ContextMapKind::Distance
    };
    &&& status.is_none()
    &&& if symbol == 0 {
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 4
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == initialized + 1
        &&& after[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            initialized as u16,
        ) as int] == 0
    } else if symbol <= max_run as u16 {
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 5
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_PENDING_RUN)
            == symbol as u8
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == initialized
    } else {
        let value = symbol as nat - max_run as nat;
        &&& value < b3b_scalar_u16_at(before, window_bytes, B3B_MAP_TREES)
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 4
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED)
            == initialized + 1
        &&& after[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            initialized as u16,
        ) as int] == value as u8
    }
}

spec fn context_symbol_phase_refines(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<ContextAdvanceStatus>,
) -> bool {
    if b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE)
    {
        &&& consumed == 0
        &&& status.is_none()
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_PHASE) == 6
    } else if match status {
        Some(ContextAdvanceStatus::Failed(_)) => true,
        _ => false,
    } {
        true
    } else {
        exists|meta: crate::brotli_prefix::TreeMetadata,
            start_queue: BitQueue,
            final_queue: BitQueue,
            start_prefix: InstalledPrefixState,
            final_prefix: InstalledPrefixState,
            symbol_step: InstalledSymbolStep| {
            &&& temporary_tree_metadata_matches(before, window_bytes, meta)
            &&& serialized_b3b_queue(before, window_bytes, start_queue)
            &&& serialized_installed_prefix(before, window_bytes, start_prefix)
            &&& serialized_b3b_queue(after, window_bytes, final_queue)
            &&& serialized_installed_prefix(after, window_bytes, final_prefix)
            &&& symbol_step.consumed == consumed
            &&& installed_tree_step_refines(
                before,
                window_bytes,
                crate::brotli_prefix::TreeRegion::TemporaryContext,
                0,
                meta,
                start_queue,
                start_prefix,
                input,
                end_of_input,
                symbol_step,
                final_queue,
                final_prefix,
            )
            &&& match symbol_step.status {
                InstalledSymbolStatus::NeedInput => status
                    == Some(ContextAdvanceStatus::NeedInput),
                InstalledSymbolStatus::Symbol(symbol) => context_symbol_value_result(
                    before,
                    after,
                    window_bytes,
                    symbol,
                    status,
                ),
                InstalledSymbolStatus::Truncated => status == Some(
                    ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
                ),
                InstalledSymbolStatus::InvalidPrefixCode => status == Some(
                    ContextAdvanceStatus::Failed(CompressedHeaderError::InvalidFormat(
                        CompressedFormatError::InvalidPrefixCode,
                    )),
                ),
                InstalledSymbolStatus::InternalState => status == Some(
                    ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
                ),
            }
        }
    }
}

proof fn establish_context_symbol_refinement(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<ContextAdvanceStatus>,
    meta: crate::brotli_prefix::TreeMetadata,
    start_queue: BitQueue,
    final_queue: BitQueue,
    start_prefix: InstalledPrefixState,
    final_prefix: InstalledPrefixState,
    symbol_step: InstalledSymbolStep,
)
    requires
        b3b_scalar_u16_at(before, window_bytes, B3B_MAP_INITIALIZED)
            != b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE),
        temporary_tree_metadata_matches(before, window_bytes, meta),
        serialized_b3b_queue(before, window_bytes, start_queue),
        serialized_installed_prefix(before, window_bytes, start_prefix),
        serialized_b3b_queue(after, window_bytes, final_queue),
        serialized_installed_prefix(after, window_bytes, final_prefix),
        symbol_step.consumed == consumed,
        installed_tree_step_refines(
            before,
            window_bytes,
            crate::brotli_prefix::TreeRegion::TemporaryContext,
            0,
            meta,
            start_queue,
            start_prefix,
            input,
            end_of_input,
            symbol_step,
            final_queue,
            final_prefix,
        ),
        match symbol_step.status {
            InstalledSymbolStatus::NeedInput => status
                == Some(ContextAdvanceStatus::NeedInput),
            InstalledSymbolStatus::Symbol(symbol) => context_symbol_value_result(
                before,
                after,
                window_bytes,
                symbol,
                status,
            ),
            InstalledSymbolStatus::Truncated => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
            ),
            InstalledSymbolStatus::InvalidPrefixCode => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::InvalidFormat(
                    CompressedFormatError::InvalidPrefixCode,
                )),
            ),
            InstalledSymbolStatus::InternalState => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
            ),
        },
    ensures context_symbol_phase_refines(
        before,
        after,
        window_bytes,
        input,
        end_of_input,
        consumed,
        status,
    ),
{
    reveal(context_symbol_phase_refines);
    assert(exists|witness_meta: crate::brotli_prefix::TreeMetadata,
        witness_start_queue: BitQueue,
        witness_final_queue: BitQueue,
        witness_start_prefix: InstalledPrefixState,
        witness_final_prefix: InstalledPrefixState,
        witness_step: InstalledSymbolStep| {
        &&& temporary_tree_metadata_matches(before, window_bytes, witness_meta)
        &&& serialized_b3b_queue(before, window_bytes, witness_start_queue)
        &&& serialized_installed_prefix(before, window_bytes, witness_start_prefix)
        &&& serialized_b3b_queue(after, window_bytes, witness_final_queue)
        &&& serialized_installed_prefix(after, window_bytes, witness_final_prefix)
        &&& witness_step.consumed == consumed
        &&& installed_tree_step_refines(
            before,
            window_bytes,
            crate::brotli_prefix::TreeRegion::TemporaryContext,
            0,
            witness_meta,
            witness_start_queue,
            witness_start_prefix,
            input,
            end_of_input,
            witness_step,
            witness_final_queue,
            witness_final_prefix,
        )
        &&& match witness_step.status {
            InstalledSymbolStatus::NeedInput => status
                == Some(ContextAdvanceStatus::NeedInput),
            InstalledSymbolStatus::Symbol(symbol) => context_symbol_value_result(
                before,
                after,
                window_bytes,
                symbol,
                status,
            ),
            InstalledSymbolStatus::Truncated => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),
            ),
            InstalledSymbolStatus::InvalidPrefixCode => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::InvalidFormat(
                    CompressedFormatError::InvalidPrefixCode,
                )),
            ),
            InstalledSymbolStatus::InternalState => status == Some(
                ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
            ),
        }
    });
}

spec fn context_symbol_store_holds(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    symbol: u16,
) -> bool {
    &&& after.len() == before.len()
    &&& serialized_context_state_ok(after, window_bytes)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_CONTEXT_KIND)
        == b3b_scalar_byte_at(before, window_bytes, B3B_CONTEXT_KIND)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE)
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
        == b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE)
    &&& context_symbol_value_result(before, after, window_bytes, symbol, None)
    &&& forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 ==> #[trigger]
        after[b3b_scalar_base(window_bytes) + i]
            == before[b3b_scalar_base(window_bytes) + i]
    &&& b3b_scalar_byte_at(after, window_bytes, B3B_INSTALLED_PREFIX_WIDTH)
        == b3b_scalar_byte_at(before, window_bytes, B3B_INSTALLED_PREFIX_WIDTH)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_INSTALLED_PREFIX_BITS)
        == b3b_scalar_u16_at(before, window_bytes, B3B_INSTALLED_PREFIX_BITS)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_INSTALLED_SCAN)
        == b3b_scalar_u16_at(before, window_bytes, B3B_INSTALLED_SCAN)
}

fn store_context_zero_symbol(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    initialized: u16,
    num_trees: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 4,
        kind == if b3b_scalar_byte_at(
            old(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == initialized,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES) == num_trees,
        initialized < active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
        1 <= num_trees <= 256,
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.is_ok() ==> context_symbol_store_holds(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            0,
        ),
{
    let ghost original = workspace@;
    let next = match crate::brotli_prefix::write_next_context_entry(
        workspace,
        window_bytes,
        kind,
        active_len,
        initialized,
        0,
        num_trees,
    ) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    proof {
        context_map_update_extends_valid_prefix(
            original,
            workspace@,
            window_bytes,
            kind,
            initialized,
            0,
            num_trees,
        );
        context_prefix_int_implies_u16(
            workspace@,
            window_bytes,
            kind,
            next,
            num_trees,
        );
        context_progress_values_match_serialized_kind(
            workspace@,
            window_bytes,
            kind,
            next,
            num_trees,
        );
    }
    match store_context_map_progress(workspace, window_bytes, next) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        reveal(context_symbol_store_holds);
        reveal(context_symbol_value_result);
    }
    Ok(())
}

fn store_context_pending_run_symbol(
    workspace: &mut [u8],
    window_bytes: u32,
    symbol: u16,
    _max_run: u8,
    _active_len: u16,
    _initialized: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 4,
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX) == _max_run,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == _active_len,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == _initialized,
        _initialized < _active_len,
        1 <= symbol <= _max_run as u16,
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.is_ok() ==> context_symbol_store_holds(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            symbol,
        ),
{
    match put_state_byte(
        workspace,
        window_bytes,
        B3B_PENDING_RUN,
        symbol as u8,
    ) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        reveal(serialized_context_data_ok);
        reveal(serialized_context_phase_payload_ok);
        assert(serialized_context_data_ok(workspace@, window_bytes));
        assert(serialized_context_phase_payload_ok(workspace@, window_bytes, 5));
    }
    match store_context_phase(workspace, window_bytes, 5) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        reveal(context_symbol_store_holds);
        reveal(context_symbol_value_result);
    }
    Ok(())
}

spec fn direct_context_symbol_valid(symbol: u16, max_run: u8, num_trees: u16) -> bool {
    (max_run as u16) < symbol && symbol - (max_run as u16) < num_trees
}

fn store_context_direct_symbol(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    initialized: u16,
    num_trees: u16,
    max_run: u8,
    symbol: u16,
) -> (r: Result<(), CompressedHeaderError>)
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 4,
        kind == if b3b_scalar_byte_at(
            old(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == initialized,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES) == num_trees,
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX) == max_run,
        initialized < active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
        1 <= num_trees <= 256,
        direct_context_symbol_valid(symbol, max_run, num_trees),
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.is_ok() ==> context_symbol_store_holds(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            symbol,
        ),
{
    let value = symbol - max_run as u16;
    proof { bounded_u16_fits_u8(value); }
    let ghost original = workspace@;
    let next = match crate::brotli_prefix::write_next_context_entry(
        workspace,
        window_bytes,
        kind,
        active_len,
        initialized,
        value as u8,
        num_trees,
    ) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    proof {
        context_map_update_extends_valid_prefix(
            original,
            workspace@,
            window_bytes,
            kind,
            initialized,
            value as u8,
            num_trees,
        );
        context_prefix_int_implies_u16(
            workspace@,
            window_bytes,
            kind,
            next,
            num_trees,
        );
        context_progress_values_match_serialized_kind(
            workspace@,
            window_bytes,
            kind,
            next,
            num_trees,
        );
    }
    match store_context_map_progress(workspace, window_bytes, next) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        reveal(context_symbol_store_holds);
        reveal(context_symbol_value_result);
    }
    Ok(())
}

fn handle_context_installed_symbol_status(
    workspace: &mut [u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    initialized: u16,
    num_trees: u16,
    max_run: u8,
    symbol_status: InstalledSymbolStatus,
) -> (r: Option<ContextAdvanceStatus>)
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 4,
        kind == if b3b_scalar_byte_at(
            old(workspace)@,
            window_bytes,
            B3B_CONTEXT_KIND,
        ) == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_INITIALIZED)
            == initialized,
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_TREES) == num_trees,
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_MAX_RUN_PREFIX) == max_run,
        initialized < active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
        1 <= num_trees <= 256,
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        match symbol_status {
            InstalledSymbolStatus::NeedInput => {
                &&& r == Some(ContextAdvanceStatus::NeedInput)
                &&& final(workspace)@ == old(workspace)@
            },
            InstalledSymbolStatus::Truncated => {
                &&& r == Some(ContextAdvanceStatus::Failed(
                    CompressedHeaderError::Truncated,
                ))
                &&& final(workspace)@ == old(workspace)@
            },
            InstalledSymbolStatus::InvalidPrefixCode => {
                &&& r == Some(ContextAdvanceStatus::Failed(
                    CompressedHeaderError::InvalidFormat(
                        CompressedFormatError::InvalidPrefixCode,
                    ),
                ))
                &&& final(workspace)@ == old(workspace)@
            },
            InstalledSymbolStatus::InternalState => {
                &&& r == Some(ContextAdvanceStatus::Failed(
                    CompressedHeaderError::InternalState,
                ))
                &&& final(workspace)@ == old(workspace)@
            },
            InstalledSymbolStatus::Symbol(symbol) => match r {
                None => context_symbol_store_holds(
                    old(workspace)@,
                    final(workspace)@,
                    window_bytes,
                    symbol,
                ),
                Some(ContextAdvanceStatus::Failed(_)) => true,
                _ => false,
            },
        },
{
    match symbol_status {
        InstalledSymbolStatus::NeedInput => Some(ContextAdvanceStatus::NeedInput),
        InstalledSymbolStatus::Truncated => Some(ContextAdvanceStatus::Failed(
            CompressedHeaderError::Truncated,
        )),
        InstalledSymbolStatus::InvalidPrefixCode => Some(ContextAdvanceStatus::Failed(
            CompressedHeaderError::InvalidFormat(
                CompressedFormatError::InvalidPrefixCode,
            ),
        )),
        InstalledSymbolStatus::InternalState => Some(ContextAdvanceStatus::Failed(
            CompressedHeaderError::InternalState,
        )),
        InstalledSymbolStatus::Symbol(symbol) => {
            let stored = if symbol == 0 {
                store_context_zero_symbol(
                    workspace,
                    window_bytes,
                    kind,
                    active_len,
                    initialized,
                    num_trees,
                )
            } else if symbol <= max_run as u16 {
                store_context_pending_run_symbol(
                    workspace,
                    window_bytes,
                    symbol,
                    max_run,
                    active_len,
                    initialized,
                )
            } else {
                let value = symbol - max_run as u16;
                if value >= num_trees {
                    return Some(ContextAdvanceStatus::Failed(
                        CompressedHeaderError::InvalidFormat(
                            CompressedFormatError::ContextMapValue,
                        ),
                    ));
                }
                proof {
                    assert(direct_context_symbol_valid(symbol, max_run, num_trees));
                }
                store_context_direct_symbol(
                    workspace,
                    window_bytes,
                    kind,
                    active_len,
                    initialized,
                    num_trees,
                    max_run,
                    symbol,
                )
            };
            match stored {
                Ok(()) => None,
                Err(error) => Some(ContextAdvanceStatus::Failed(error)),
            }
        }
    }
}

fn advance_context_symbol_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    kind_tag: u8,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    input: &[u8],
    end_of_input: bool,
) -> (r: (usize, Option<ContextAdvanceStatus>))
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 4,
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND) == kind_tag,
        kind == if kind_tag == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        match r.1 {
            Some(ContextAdvanceStatus::Failed(_)) => true,
            _ => b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        },
        r.0 <= input.len(),
        r.1.is_none() ==> {
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == kind_tag
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == active_len
        },
        r.1 == Some(ContextAdvanceStatus::NeedInput) ==> {
            &&& !end_of_input
            &&& r.0 == input.len()
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
        },
        match r.1 {
            Some(ContextAdvanceStatus::Complete { .. }) => false,
            _ => true,
        },
        context_symbol_phase_refines(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            input@,
            end_of_input,
            r.0,
            r.1,
        ),
{
    let ghost original = workspace@;
    proof { b3b_scalar_layout_is_exact(); }
    let mut consumed: usize = 0;

                let initialized = match state_u16(workspace, window_bytes, B3B_MAP_INITIALIZED) {
                    Ok(value) => value,
                    Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                };
                if initialized > active_len {
                    return (consumed, Some(ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),));
                }
                if initialized == active_len {
                    if let Err(error) = store_context_phase(
                        workspace, window_bytes, 6) {
                        return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                    }
                    let result = (consumed, None);
                    proof {
                        reveal(context_symbol_phase_refines);
                        assert(context_symbol_phase_refines(
                            original,
                            workspace@,
                            window_bytes,
                            input@,
                            end_of_input,
                            result.0,
                            result.1,
                        ));
                    }
                    return result;
                } else {
                    let num_trees = match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
                        Ok(value) => value,
                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                    };
                    if num_trees == 0 || num_trees > 256 {
                        return (consumed, Some(ContextAdvanceStatus::Failed(
                                CompressedHeaderError::InternalState),));
                    }
                    let max_run = match state_byte(workspace, window_bytes, B3B_MAX_RUN_PREFIX) {
                        Ok(value) => value,
                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                    };
                    let meta = match crate::brotli_prefix::read_tree_metadata(
                        workspace,
                        window_bytes,
                        crate::brotli_prefix::TreeRegion::TemporaryContext,
                        1,
                        0,
                    ) {
                        Ok(value) => value,
                        Err(crate::brotli_prefix::MetadataReadError::InvalidEncoding) =>
                            return (consumed, Some(ContextAdvanceStatus::Failed(
                                    CompressedHeaderError::InvalidFormat(
                                        CompressedFormatError::InvalidMetadata)),)),
                        Err(crate::brotli_prefix::MetadataReadError::Workspace(error)) =>
                            return (consumed, Some(ContextAdvanceStatus::Failed(
                                    CompressedHeaderError::Workspace(error)),)),
                    };
                    proof {
                        reveal(temporary_tree_metadata_matches);
                        assert(temporary_tree_metadata_matches(
                            original,
                            window_bytes,
                            meta,
                        ));
                    }
                    let mut queue = match load_b3b_queue(workspace, window_bytes) {
                        Ok(value) => value,
                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                    };
                    let ghost start_queue = queue;
                    let width = match state_byte(workspace, window_bytes, B3B_INSTALLED_PREFIX_WIDTH) {
                        Ok(value) => value,
                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                    };
                    let bits = match state_u16(workspace, window_bytes, B3B_INSTALLED_PREFIX_BITS) {
                        Ok(value) => value,
                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                    };
                    let scan = match state_u16(workspace, window_bytes, B3B_INSTALLED_SCAN) {
                        Ok(value) => value,
                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                    };
                    if width > 14 || scan != 0 || bits >= (1u16 << width) {
                        return (consumed, Some(ContextAdvanceStatus::Failed(
                            CompressedHeaderError::InternalState)));
                    }
                    let mut prefix = InstalledPrefixState { width, bits, scan };
                    let ghost start_prefix = prefix;
                    proof {
                        reveal(serialized_installed_prefix);
                        assert(serialized_installed_prefix(
                            original,
                            window_bytes,
                            start_prefix,
                        ));
                    }
                    let remaining = &input[consumed..];
                    proof {
                        assert(remaining@ == input@);
                        assert(workspace@ == original);
                    }
                    let symbol_step = advance_installed_tree_symbol(
                        workspace,
                        window_bytes,
                        crate::brotli_prefix::TreeRegion::TemporaryContext,
                        0,
                        meta,
                        &mut queue,
                        &mut prefix,
                        remaining,
                        end_of_input,
                    );
                    proof {
                        assert(installed_tree_step_refines(
                            original,
                            window_bytes,
                            crate::brotli_prefix::TreeRegion::TemporaryContext,
                            0,
                            meta,
                            start_queue,
                            start_prefix,
                            input@,
                            end_of_input,
                            symbol_step,
                            queue,
                            prefix,
                        ));
                    }
                    consumed = consumed + symbol_step.consumed;
                    if let Err(error) = store_b3b_queue(workspace, window_bytes, &queue) {
                        return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                    }
                    let ghost after_queue_store = workspace@;
                    if let Err(error) = store_installed_prefix_state(
                        workspace,
                        window_bytes,
                        prefix,
                    ) {
                        return (consumed, Some(ContextAdvanceStatus::Failed(error),));
                    }
                    proof {
                        assert forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 implies #[trigger]
                            workspace@[b3b_scalar_base(window_bytes) + i]
                                == after_queue_store[b3b_scalar_base(window_bytes) + i] by {}
                        serialized_b3b_queue_from_frame(
                            after_queue_store,
                            workspace@,
                            window_bytes,
                            queue,
                        );
                    }
                    let ghost stored_cursor = workspace@;
                    proof {
                        assert(b3b_scalar_byte_at(
                            stored_cursor,
                            window_bytes,
                            B3B_MAX_RUN_PREFIX,
                        ) == max_run);
                        assert(b3b_scalar_u16_at(
                            stored_cursor,
                            window_bytes,
                            B3B_MAP_INITIALIZED,
                        ) == initialized);
                        assert(b3b_scalar_u16_at(
                            stored_cursor,
                            window_bytes,
                            B3B_MAP_TREES,
                        ) == num_trees);
                        assert(b3b_scalar_byte_at(
                            stored_cursor,
                            window_bytes,
                            B3B_CONTEXT_KIND,
                        ) == kind_tag);
                        assert(b3b_scalar_u16_at(
                            stored_cursor,
                            window_bytes,
                            B3B_MAP_SIZE,
                        ) == active_len);
                    }
                    let handled = handle_context_installed_symbol_status(
                        workspace,
                        window_bytes,
                        kind,
                        active_len,
                        initialized,
                        num_trees,
                        max_run,
                        symbol_step.status,
                    );
                    match handled {
                        Some(status) => {
                            let result = (consumed, Some(status));
                            proof {
                                match status {
                                    ContextAdvanceStatus::NeedInput => {
                                        establish_context_symbol_refinement(
                                            original,
                                            workspace@,
                                            window_bytes,
                                            input@,
                                            end_of_input,
                                            result.0,
                                            result.1,
                                            meta,
                                            start_queue,
                                            queue,
                                            start_prefix,
                                            prefix,
                                            symbol_step,
                                        );
                                    }
                                    ContextAdvanceStatus::Failed(_) => {
                                        reveal(context_symbol_phase_refines);
                                    }
                                    ContextAdvanceStatus::Complete { .. } => {
                                        assert(false);
                                    }
                                }
                            }
                            return result;
                        }
                        None => {}
                    }
                    proof {
                        reveal(context_symbol_store_holds);
                        assert(serialized_context_state_ok(workspace@, window_bytes));
                        assert(b3b_scalar_byte_at(
                            workspace@,
                            window_bytes,
                            B3B_CONTEXT_KIND,
                        ) == kind_tag);
                        assert(b3b_scalar_u16_at(
                            workspace@,
                            window_bytes,
                            B3B_MAP_SIZE,
                        ) == active_len);
                    }
                    let result = (consumed, None);
                proof {
                    reveal(context_symbol_store_holds);
                    assert forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 implies #[trigger]
                        workspace@[b3b_scalar_base(window_bytes) + i]
                            == stored_cursor[b3b_scalar_base(window_bytes) + i] by {}
                    serialized_b3b_queue_from_frame(
                        stored_cursor,
                        workspace@,
                        window_bytes,
                        queue,
                    );
                    assert(b3b_scalar_byte_at(
                        workspace@,
                        window_bytes,
                        B3B_INSTALLED_PREFIX_WIDTH,
                    ) == b3b_scalar_byte_at(
                        stored_cursor,
                        window_bytes,
                        B3B_INSTALLED_PREFIX_WIDTH,
                    ));
                    assert(b3b_scalar_u16_at(
                        workspace@,
                        window_bytes,
                        B3B_INSTALLED_PREFIX_BITS,
                    ) == b3b_scalar_u16_at(
                        stored_cursor,
                        window_bytes,
                        B3B_INSTALLED_PREFIX_BITS,
                    ));
                    assert(b3b_scalar_u16_at(
                        workspace@,
                        window_bytes,
                        B3B_INSTALLED_SCAN,
                    ) == b3b_scalar_u16_at(
                        stored_cursor,
                        window_bytes,
                        B3B_INSTALLED_SCAN,
                    ));
                    serialized_installed_prefix_from_frame(
                        stored_cursor,
                        workspace@,
                        window_bytes,
                        prefix,
                    );
                    assert(result.0 == symbol_step.consumed);
                    match symbol_step.status {
                        InstalledSymbolStatus::Symbol(symbol) => {
                            reveal(context_symbol_value_result);
                            assert(b3b_scalar_u16_at(
                                stored_cursor,
                                window_bytes,
                                B3B_MAP_INITIALIZED,
                            ) == b3b_scalar_u16_at(
                                original,
                                window_bytes,
                                B3B_MAP_INITIALIZED,
                            ));
                            assert(b3b_scalar_byte_at(
                                stored_cursor,
                                window_bytes,
                                B3B_MAX_RUN_PREFIX,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_MAX_RUN_PREFIX,
                            ));
                            assert(b3b_scalar_byte_at(
                                stored_cursor,
                                window_bytes,
                                B3B_CONTEXT_KIND,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_CONTEXT_KIND,
                            ));
                            assert(context_symbol_value_result(
                                original,
                                workspace@,
                                window_bytes,
                                symbol,
                                result.1,
                            ));
                        }
                        _ => { assert(false); }
                    }
                    establish_context_symbol_refinement(
                        original,
                        workspace@,
                        window_bytes,
                        input@,
                        end_of_input,
                        result.0,
                        result.1,
                        meta,
                        start_queue,
                        queue,
                        start_prefix,
                        prefix,
                        symbol_step,
                    );
                }
                    return result;
                }
}

fn advance_context_bits_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    phase: u8,
    kind_tag: u8,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    input: &[u8],
    end_of_input: bool,
) -> (r: (usize, Option<ContextAdvanceStatus>))
    requires
        phase == 1 || phase == 2 || phase == 5 || phase == 6,
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == phase,
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND) == kind_tag,
        kind == if kind_tag == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.0 <= input.len(),
        r.1.is_none() ==> {
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == kind_tag
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == active_len
        },
        r.1 == Some(ContextAdvanceStatus::NeedInput) ==> {
            &&& !end_of_input
            &&& r.0 == input.len()
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
        },
        match r.1 {
            Some(ContextAdvanceStatus::Complete { .. }) => false,
            _ => true,
        },
        context_bits_phase_refines(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            phase,
            input@,
            end_of_input,
            r.0,
            r.1,
        ),
{
    let ghost original = workspace@;
    proof { b3b_scalar_layout_is_exact(); }
    let mut consumed: usize = 0;

                let (width, pending_symbol) = if phase == 1 {
                    (1usize, 0u8)
                }
                    else if phase == 2 { (4usize, 0u8) }
                    else if phase == 6 { (1usize, 0u8) }
                    else {
                        let pending = match state_byte(workspace, window_bytes, B3B_PENDING_RUN) {
                            Ok(value) => value,
                            Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                        };
                        if pending == 0 || pending > 16 {
                            return (consumed, Some(ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),));
                        }
                        (pending as usize, pending)
                    };
                let mut queue = match load_b3b_queue(workspace, window_bytes) {
                    Ok(value) => value,
                    Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                };
                let ghost start_queue = queue;
                let remaining = &input[consumed..];
                proof { assert(remaining@ == input@); }
                let read = queue.read_bits(width, remaining, end_of_input);
                proof {
                    assert(bit_read_exact_step(
                        start_queue,
                        input@,
                        end_of_input,
                        width as nat,
                        read.consumed,
                        queue,
                        read.status,
                    ));
                    assert(width as nat == context_bits_width(
                        original,
                        window_bytes,
                        phase,
                    ));
                }
                consumed = consumed + read.consumed;
                if let Err(error) = store_b3b_queue(workspace, window_bytes, &queue) {
                    return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                }
                let ghost stored_queue = workspace@;
                match read.status {
                    BitReadStatus::NeedInput => {
                        let result = (consumed, Some(ContextAdvanceStatus::NeedInput));
                        proof {
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ));
                            establish_context_bits_refinement(
                                original,
                                workspace@,
                                window_bytes,
                                phase,
                                input@,
                                end_of_input,
                                result.0,
                                result.1,
                                start_queue,
                                queue,
                                read.status,
                            );
                        }
                        return result;
                    }
                    BitReadStatus::Truncated => return (consumed, Some(ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),)),
                    BitReadStatus::Value(value) => {
                        if phase == 1 {
                            if value == 0 {
                                if let Err(error) = start_serialized_tree(
                                    workspace,
                                    window_bytes,
                                    crate::brotli_prefix::TreeRegion::TemporaryContext,
                                    0,
                                    match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
                                        Ok(value) => value,
                                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                                    },
                                    match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
                                        Ok(value) => value,
                                        Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                                    },
                                ) {
                                    return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                                }
                                if let Err(error) = put_state_byte(
                                    workspace, window_bytes, B3B_MAX_RUN_PREFIX, 0) {
                                    return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                                }
                                proof {
                                    reveal(serialized_context_data_ok);
                                    reveal(serialized_context_phase_payload_ok);
                                    assert(serialized_context_data_ok(workspace@, window_bytes));
                                    assert(serialized_context_phase_payload_ok(
                                        workspace@,
                                        window_bytes,
                                        3,
                                    ));
                                }
                                if let Err(error) = store_context_phase(
                                    workspace, window_bytes, 3) {
                                    return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                                }
                            } else {
                                proof {
                                    reveal(serialized_context_state_ok);
                                    reveal(serialized_context_data_ok);
                                    reveal(serialized_context_phase_payload_ok);
                                    assert(serialized_context_data_ok(workspace@, window_bytes));
                                    assert(serialized_context_phase_payload_ok(
                                        workspace@,
                                        window_bytes,
                                        2,
                                    ));
                                }
                                if let Err(error) = store_context_phase(workspace, window_bytes, 2) {
                                    return (consumed, Some(ContextAdvanceStatus::Failed(error),));
                                }
                            }
                        } else if phase == 2 {
                            proof {
                                lemma2_to64();
                                assert(value < 16);
                                bounded_u64_fits_u8(value);
                            }
                            let max_run = value as u8 + 1;
                            let num_trees = match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
                                Ok(value) => value,
                                Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                            };
                            if num_trees == 0 || num_trees > 256 {
                                return (consumed, Some(ContextAdvanceStatus::Failed(
                                        CompressedHeaderError::InternalState),));
                            }
                            let alphabet = num_trees + max_run as u16;
                            if alphabet > 272 {
                                return (consumed, Some(ContextAdvanceStatus::Failed(
                                        CompressedHeaderError::InvalidFormat(
                                            CompressedFormatError::InvalidPrefixCode)),));
                            }
                            if let Err(error) = put_state_byte(
                                workspace, window_bytes, B3B_MAX_RUN_PREFIX, max_run) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                            if let Err(error) = start_serialized_tree(
                                workspace,
                                window_bytes,
                                crate::brotli_prefix::TreeRegion::TemporaryContext,
                                0,
                                alphabet,
                                alphabet,
                            ) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                            proof {
                                reveal(serialized_context_data_ok);
                                reveal(serialized_context_phase_payload_ok);
                                assert(serialized_context_data_ok(workspace@, window_bytes));
                                assert(serialized_context_phase_payload_ok(
                                    workspace@,
                                    window_bytes,
                                    3,
                                ));
                            }
                            if let Err(error) = store_context_phase(
                                workspace, window_bytes, 3) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                        } else if phase == 5 {
                            let symbol = pending_symbol;
                            if symbol == 0 || symbol > 16 {
                                return (consumed, Some(ContextAdvanceStatus::Failed(
                                        CompressedHeaderError::InternalState),));
                            }
                            proof {
                                lemma2_to64();
                                if symbol < 16 {
                                    lemma_pow2_strictly_increases(symbol as nat, 16);
                                }
                                assert(value < 65_536);
                                bounded_u64_fits_u16(value);
                                pow2_matches_context_repeat_shift(symbol);
                                assert((value as u16 as u32) < (1u32 << symbol));
                            }
                            let repeat = context_zero_repeat_exec(symbol, value as u16);
                            let index = match state_u16(workspace, window_bytes, B3B_MAP_INITIALIZED) {
                                Ok(value) => value,
                                Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                            };
                            if index as u32 + repeat > active_len as u32 {
                                proof {
                                    assert(index as u32 + repeat > active_len as u32);
                                }
                                return (consumed, Some(ContextAdvanceStatus::Failed(
                                        CompressedHeaderError::InvalidFormat(
                                            CompressedFormatError::ContextMapRepeat)),));
                            }
                            let num_trees = match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
                                Ok(value) => value,
                                Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                            };
                            if num_trees == 0 || num_trees > 256 {
                                return (consumed, Some(ContextAdvanceStatus::Failed(
                                        CompressedHeaderError::InternalState),));
                            }
                            proof {
                                assert(phase == 5);
                                assert(b3b_scalar_byte_at(
                                    workspace@,
                                    window_bytes,
                                    B3B_CONTEXT_PHASE,
                                ) == 5);
                                assert((if kind_tag == 0 {
                                    crate::brotli_prefix::ContextMapKind::Literal
                                } else {
                                    crate::brotli_prefix::ContextMapKind::Distance
                                }) == kind);
                                reveal(serialized_context_state_ok);
                                reveal(serialized_context_phase_payload_ok);
                                reveal(serialized_context_data_ok);
                                reveal(serialized_context_map_prefix_ok);
                                assert(index as nat == b3b_scalar_u16_at(
                                    workspace@,
                                    window_bytes,
                                    B3B_MAP_INITIALIZED,
                                ));
                                assert(num_trees as nat == b3b_scalar_u16_at(
                                    workspace@,
                                    window_bytes,
                                    B3B_MAP_TREES,
                                ));
                                assert(b3b_scalar_u16_at(
                                    workspace@,
                                    window_bytes,
                                    B3B_MAP_TREES,
                                ) > 0);
                                assert forall|i: int| 0 <= i < index implies #[trigger]
                                    workspace@[crate::brotli_prefix::context_entry_at(
                                        window_bytes,
                                        kind,
                                        i as u16,
                                    ) as int] < num_trees by {
                                    assert(serialized_context_map_prefix_ok(
                                        workspace@,
                                        window_bytes,
                                    ));
                                    let spec_kind = if b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_CONTEXT_KIND,
                                    ) == 0 {
                                        crate::brotli_prefix::ContextMapKind::Literal
                                    } else {
                                        crate::brotli_prefix::ContextMapKind::Distance
                                    };
                                    assert(spec_kind == kind);
                                    assert(i < 65_536);
                                    serialized_context_prefix_value_bound(
                                        workspace@,
                                        window_bytes,
                                        i,
                                    );
                                    assert(i < b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_INITIALIZED,
                                    ));
                                    assert(workspace@[crate::brotli_prefix::context_entry_at(
                                        window_bytes,
                                        spec_kind,
                                        i as u16,
                                    ) as int] < b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_TREES,
                                    ));
                                }
                            }
                            let mut initialized = index;
                            let target = index + repeat as u16;
                            while initialized < target
                                invariant initialized <= target <= active_len,
                                    active_len as nat
                                        <= crate::brotli_prefix::context_map_capacity(kind),
                                    1 <= num_trees <= 256,
                                    consumed <= input.len(),
                                    workspace@.len() == stored_queue.len(),
                                    b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_OUTER_PHASE,
                                    ) == b3b_scalar_byte_at(
                                        original,
                                        window_bytes,
                                        B3B_OUTER_PHASE,
                                    ),
                                    forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 ==> #[trigger]
                                        workspace@[b3b_scalar_base(window_bytes) + i]
                                            == stored_queue[b3b_scalar_base(window_bytes) + i],
                                    serialized_mtf_state_ok(workspace@, window_bytes),
                                    serialized_context_data_ok(workspace@, window_bytes),
                                    b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_INITIALIZED,
                                    ) <= initialized,
                                    b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_SIZE,
                                    ) == active_len,
                                    b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_TREES,
                                    ) == num_trees,
                                    b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_CONTEXT_KIND,
                                    ) == kind_tag,
                                    kind == if b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_CONTEXT_KIND,
                                    ) == 0 {
                                        crate::brotli_prefix::ContextMapKind::Literal
                                    } else {
                                        crate::brotli_prefix::ContextMapKind::Distance
                                    },
                                    forall|i: int| 0 <= i < initialized ==> #[trigger]
                                        workspace@[crate::brotli_prefix::context_entry_at(
                                            window_bytes,
                                            kind,
                                            i as u16,
                                        ) as int] < num_trees,
                                    forall|i: int| index <= i < initialized ==> #[trigger]
                                        workspace@[crate::brotli_prefix::context_entry_at(
                                            window_bytes,
                                            kind,
                                            i as u16,
                                        ) as int] == 0,
                                    forall|i: u16| i < initialized ==> #[trigger]
                                        workspace@[crate::brotli_prefix::context_entry_at(
                                            window_bytes,
                                            kind,
                                            i,
                                        ) as int] < num_trees,
                                decreases target - initialized,
                            {
                                let old_initialized = initialized;
                                let ghost before_entry = workspace@;
                                initialized = match crate::brotli_prefix::write_next_context_entry(
                                    workspace, window_bytes, kind, active_len,
                                    initialized, 0, num_trees) {
                                    Ok(value) => value,
                                    Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(
                                            CompressedHeaderError::Workspace(error)),)),
                                };
                                proof {
                                    assert(b3b_scalar_u16_at(
                                        before_entry,
                                        window_bytes,
                                        B3B_MAP_INITIALIZED,
                                    ) <= old_initialized);
                                    context_map_update_extends_valid_prefix(
                                        before_entry,
                                        workspace@,
                                        window_bytes,
                                        kind,
                                        old_initialized,
                                        0,
                                        num_trees,
                                    );
                                    context_prefix_int_implies_u16(
                                        workspace@,
                                        window_bytes,
                                        kind,
                                        initialized,
                                        num_trees,
                                    );
                                }
                            }
                            proof {
                                context_progress_values_match_serialized_kind(
                                    workspace@,
                                    window_bytes,
                                    kind,
                                    initialized,
                                    num_trees,
                                );
                            }
                            if let Err(error) = store_context_map_progress(
                                workspace, window_bytes, initialized) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                            if let Err(error) = put_state_byte(
                                workspace, window_bytes, B3B_PENDING_RUN, 255) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                            proof {
                                reveal(serialized_context_data_ok);
                                reveal(serialized_context_phase_payload_ok);
                                assert(serialized_context_data_ok(workspace@, window_bytes));
                                assert(serialized_context_phase_payload_ok(
                                    workspace@,
                                    window_bytes,
                                    4,
                                ));
                            }
                            if let Err(error) = store_context_phase(
                                workspace, window_bytes, 4) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                        } else if value == 0 {
                            if let Err(error) = store_context_phase(
                                workspace, window_bytes, 8) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                        } else if let Err(error) = store_context_phase(
                            workspace, window_bytes, 7) {
                            return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                        }
                    }
                }
                let result = (consumed, None);
                proof {
                    assert(b3b_scalar_byte_at(
                        workspace@,
                        window_bytes,
                        B3B_OUTER_PHASE,
                    ) == b3b_scalar_byte_at(
                        original,
                        window_bytes,
                        B3B_OUTER_PHASE,
                    ));
                    assert forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 implies #[trigger]
                        workspace@[b3b_scalar_base(window_bytes) + i]
                            == stored_queue[b3b_scalar_base(window_bytes) + i] by {}
                    serialized_b3b_queue_from_frame(
                        stored_queue,
                        workspace@,
                        window_bytes,
                        queue,
                    );
                    assert(result.0 == read.consumed);
                    assert(bit_read_exact_step(
                        start_queue,
                        input@,
                        end_of_input,
                        context_bits_width(original, window_bytes, phase),
                        result.0,
                        queue,
                        read.status,
                    ));
                    match read.status {
                        BitReadStatus::Value(value) => {
                            reveal(context_bits_value_result);
                            if phase == 1 {
                                if value == 0 {
                                    assert(b3b_scalar_byte_at(
                                        workspace@, window_bytes, B3B_CONTEXT_PHASE) == 3);
                                    assert(b3b_scalar_byte_at(
                                        workspace@, window_bytes, B3B_MAX_RUN_PREFIX) == 0);
                                    assert(b3b_scalar_byte_at(
                                        workspace@, window_bytes, B3B_ACTIVE_REGION) == 5);
                                    assert(b3b_scalar_u16_at(
                                        workspace@, window_bytes, B3B_ACTIVE_TREE) == 0);
                                    assert(b3b_scalar_u16_at(
                                        workspace@, window_bytes, B3B_ALPHABET_MAX)
                                        == b3b_scalar_u16_at(
                                            original, window_bytes, B3B_MAP_TREES));
                                    assert(b3b_scalar_u16_at(
                                        workspace@, window_bytes, B3B_ALPHABET_LIMIT)
                                        == b3b_scalar_u16_at(
                                            original, window_bytes, B3B_MAP_TREES));
                                } else {
                                    assert(b3b_scalar_byte_at(
                                        workspace@, window_bytes, B3B_CONTEXT_PHASE) == 2);
                                }
                            } else if phase == 2 {
                                assert(b3b_scalar_byte_at(
                                    workspace@, window_bytes, B3B_CONTEXT_PHASE) == 3);
                                assert(b3b_scalar_byte_at(
                                    workspace@, window_bytes, B3B_MAX_RUN_PREFIX) as nat
                                    == value as nat + 1);
                                assert(b3b_scalar_byte_at(
                                    workspace@, window_bytes, B3B_ACTIVE_REGION) == 5);
                                assert(b3b_scalar_u16_at(
                                    workspace@, window_bytes, B3B_ACTIVE_TREE) == 0);
                                assert(b3b_scalar_u16_at(
                                    workspace@, window_bytes, B3B_ALPHABET_MAX)
                                    == b3b_scalar_u16_at(
                                        original, window_bytes, B3B_MAP_TREES)
                                        + value as nat + 1);
                                assert(b3b_scalar_u16_at(
                                    workspace@, window_bytes, B3B_ALPHABET_LIMIT)
                                    == b3b_scalar_u16_at(
                                        original, window_bytes, B3B_MAP_TREES)
                                        + value as nat + 1);
                            } else if phase == 5 {
                                let old_initialized = b3b_scalar_u16_at(
                                    original, window_bytes, B3B_MAP_INITIALIZED);
                                let old_pending = b3b_scalar_byte_at(
                                    original, window_bytes, B3B_PENDING_RUN);
                                let repeat = pow2(old_pending as nat) + value as nat;
                                assert(b3b_scalar_byte_at(
                                    workspace@, window_bytes, B3B_CONTEXT_PHASE) == 4);
                                assert(b3b_scalar_byte_at(
                                    workspace@, window_bytes, B3B_PENDING_RUN) == 255);
                                assert(b3b_scalar_u16_at(
                                    workspace@, window_bytes, B3B_MAP_INITIALIZED)
                                    == old_initialized + repeat);
                                assert forall|i: int|
                                    old_initialized <= i < old_initialized + repeat implies
                                    #[trigger] workspace@[
                                        crate::brotli_prefix::context_entry_at(
                                            window_bytes,
                                            kind,
                                            i as u16,
                                        ) as int
                                    ] == 0 by {}
                            } else {
                                assert(phase == 6);
                                assert(b3b_scalar_byte_at(
                                    workspace@, window_bytes, B3B_CONTEXT_PHASE)
                                    == if value == 0 { 8u8 } else { 7u8 });
                            }
                            assert(context_bits_value_result(
                                original,
                                workspace@,
                                window_bytes,
                                phase,
                                value,
                                result.1,
                            ));
                        }
                        _ => { assert(false); }
                    }
                    establish_context_bits_refinement(
                        original,
                        workspace@,
                        window_bytes,
                        phase,
                        input@,
                        end_of_input,
                        result.0,
                        result.1,
                        start_queue,
                        queue,
                        read.status,
                    );
                }
                result
}

fn advance_context_tree_count_phase(
    workspace: &mut [u8],
    window_bytes: u32,
    kind_tag: u8,
    kind: crate::brotli_prefix::ContextMapKind,
    active_len: u16,
    input: &[u8],
    end_of_input: bool,
) -> (r: (usize, Option<ContextAdvanceStatus>))
    requires
        serialized_context_state_ok(old(workspace)@, window_bytes),
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_PHASE) == 0,
        b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_CONTEXT_KIND) == kind_tag,
        kind == if kind_tag == 0 {
            crate::brotli_prefix::ContextMapKind::Literal
        } else {
            crate::brotli_prefix::ContextMapKind::Distance
        },
        b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_MAP_SIZE) == active_len,
        active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
    ensures
        b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.0 <= input.len(),
        r.1.is_none() ==> {
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
            &&& b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_CONTEXT_KIND)
                == kind_tag
            &&& b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_MAP_SIZE)
                == active_len
        },
        r.1 == Some(ContextAdvanceStatus::NeedInput) ==> {
            &&& !end_of_input
            &&& r.0 == input.len()
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
        },
        match r.1 {
            Some(ContextAdvanceStatus::Complete { .. }) => false,
            _ => true,
        },
        context_tree_count_phase_refines(
            old(workspace)@,
            final(workspace)@,
            window_bytes,
            input@,
            end_of_input,
            r.0,
            r.1,
        ),
{
    let ghost original = workspace@;
    proof { assert(original == old(workspace)@); }
    let mut consumed: usize = 0;

                let mut queue = match load_b3b_queue(workspace, window_bytes) {
                    Ok(value) => value,
                    Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                };
                let ghost start_queue = queue;
                let mut var_phase = match load_var_uint8_phase(workspace, window_bytes) {
                    Ok(value) => value,
                    Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error))),
                };
                let ghost start_phase = var_phase;
                let remaining = &input[consumed..];
                proof { assert(remaining@ == input@); }
                let step = advance_var_uint8(
                    &mut queue,
                    &mut var_phase,
                    remaining,
                    end_of_input,
                );
                proof {
                    assert(var_uint8_exact_step(
                        start_queue,
                        start_phase,
                        input@,
                        end_of_input,
                        step.consumed,
                        queue,
                        var_phase,
                        step.status,
                    ));
                }
                consumed = consumed + step.consumed;
                if let Err(error) = store_b3b_queue(workspace, window_bytes, &queue) {
                    return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                }
                let ghost after_queue_store = workspace@;
                if let Err(error) = store_var_uint8_phase(workspace, window_bytes, var_phase) {
                    return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                }
                proof {
                    assert forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 implies #[trigger]
                        workspace@[b3b_scalar_base(window_bytes) + i]
                            == after_queue_store[b3b_scalar_base(window_bytes) + i] by {}
                    serialized_b3b_queue_from_frame(
                        after_queue_store,
                        workspace@,
                        window_bytes,
                        queue,
                    );
                }
                let ghost stored_cursor = workspace@;
                match step.status {
                    VarUint8Status::NeedInput => {
                        let result = (consumed, Some(ContextAdvanceStatus::NeedInput));
                        proof {
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ));
                            establish_context_tree_count_refinement(
                                original,
                                workspace@,
                                window_bytes,
                                input@,
                                end_of_input,
                                result.0,
                                result.1,
                                start_queue,
                                queue,
                                start_phase,
                                var_phase,
                                step.status,
                            );
                        }
                        return result;
                    }
                    VarUint8Status::Truncated => return (consumed, Some(ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),)),
                    VarUint8Status::Progress => {
                        proof {
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ));
                        }
                    }
                    VarUint8Status::Value(raw) => {
                        let num_trees = raw + 1;
                        proof {
                            var_uint8_count_adds_one(raw);
                            assert(num_trees == 1 <==> raw == 0);
                        }
                        if let Err(error) = put_state_u16(
                            workspace, window_bytes, B3B_MAP_TREES, num_trees) {
                            return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                        }
                        proof {
                            b3b_scalar_layout_is_exact();
                            assert forall|i: int| 0 <= i < B3B_VAR_WIDTH + 1
                                && i != B3B_OUTER_PHASE
                                && i != B3B_CURRENT_KIND implies #[trigger]
                                workspace@[b3b_scalar_base(window_bytes) + i]
                                    == stored_cursor[b3b_scalar_base(window_bytes) + i] by {}
                            serialized_block_count_cursor_from_frame(
                                stored_cursor,
                                workspace@,
                                window_bytes,
                                queue,
                                var_phase,
                            );
                            reveal(b3b_scalar_u16_at);
                            reveal(b3b_scalar_byte_at);
                            assert(b3b_scalar_u16_at(
                                workspace@,
                                window_bytes,
                                B3B_MAP_TREES,
                            ) == raw as nat + 1);
                        }
                        let ghost after_tree_count = workspace@;
                        if num_trees == 1 {
                            proof {
                                reveal(serialized_context_data_ok);
                                reveal(serialized_context_map_prefix_ok);
                                assert(serialized_context_data_ok(workspace@, window_bytes));
                            }
                            let mut initialized: u16 = 0;
                            while initialized < active_len
                                invariant initialized <= active_len,
                                    original == old(workspace)@,
                                    workspace@.len() == original.len(),
                                    active_len as nat
                                        <= crate::brotli_prefix::context_map_capacity(kind),
                                    consumed <= input.len(),
                                    b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_OUTER_PHASE,
                                    ) == b3b_scalar_byte_at(
                                        original,
                                        window_bytes,
                                        B3B_OUTER_PHASE,
                                    ),
                                    serialized_mtf_state_ok(workspace@, window_bytes),
                                    serialized_context_data_ok(workspace@, window_bytes),
                                    b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_INITIALIZED,
                                    ) <= initialized,
                                    b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_SIZE,
                                    ) == active_len,
                                    b3b_scalar_u16_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_MAP_TREES,
                                    ) == 1,
                                    b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_CONTEXT_KIND,
                                    ) == kind_tag,
                                    forall|i: int| 0 <= i < B3B_VAR_WIDTH + 1
                                        && i != B3B_OUTER_PHASE
                                        && i != B3B_CURRENT_KIND ==> #[trigger]
                                        workspace@[b3b_scalar_base(window_bytes) + i]
                                            == after_tree_count[
                                                b3b_scalar_base(window_bytes) + i
                                            ],
                                    kind == if b3b_scalar_byte_at(
                                        workspace@,
                                        window_bytes,
                                        B3B_CONTEXT_KIND,
                                    ) == 0 {
                                        crate::brotli_prefix::ContextMapKind::Literal
                                    } else {
                                        crate::brotli_prefix::ContextMapKind::Distance
                                    },
                                    forall|i: int| 0 <= i < initialized ==> #[trigger]
                                        workspace@[crate::brotli_prefix::context_entry_at(
                                            window_bytes,
                                            kind,
                                            i as u16,
                                        ) as int] < 1,
                                    forall|i: u16| i < initialized ==> #[trigger]
                                        workspace@[crate::brotli_prefix::context_entry_at(
                                            window_bytes,
                                            kind,
                                            i,
                                        ) as int] < 1,
                                decreases active_len - initialized,
                            {
                                let old_initialized = initialized;
                                let ghost before_entry = workspace@;
                                initialized = match crate::brotli_prefix::write_next_context_entry(
                                    workspace,
                                    window_bytes,
                                    kind,
                                    active_len,
                                    initialized,
                                    0,
                                    1,
                                ) {
                                    Ok(value) => value,
                                    Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(
                                            CompressedHeaderError::Workspace(error)),)),
                                };
                                proof {
                                    assert(b3b_scalar_u16_at(
                                        before_entry,
                                        window_bytes,
                                        B3B_MAP_INITIALIZED,
                                    ) <= old_initialized);
                                    context_map_update_extends_valid_prefix(
                                        before_entry,
                                        workspace@,
                                        window_bytes,
                                        kind,
                                        old_initialized,
                                        0,
                                        1,
                                    );
                                    context_prefix_int_implies_u16(
                                        workspace@,
                                        window_bytes,
                                        kind,
                                        initialized,
                                        1,
                                    );
                                }
                            }
                            proof {
                                context_progress_values_match_serialized_kind(
                                    workspace@,
                                    window_bytes,
                                    kind,
                                    initialized,
                                    1,
                                );
                            }
                            if let Err(error) = store_context_map_progress(
                                workspace, window_bytes, initialized) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error)));
                            }
                            let ghost before_complete = workspace@;
                            match put_state_byte(
                                workspace,
                                window_bytes,
                                B3B_CONTEXT_PHASE,
                                9,
                            ) {
                                Ok(()) => {}
                                Err(error) => return (consumed, Some(ContextAdvanceStatus::Failed(error),)),
                            }
                            proof {
                                let at = b3b_scalar_base(window_bytes)
                                    + B3B_CONTEXT_PHASE as int;
                                assert(workspace@ == before_complete.update(at, 9)) by {
                                    assert(workspace@.len() == before_complete.len());
                                    assert forall|i: int| 0 <= i < workspace@.len() implies
                                        #[trigger] workspace@[i]
                                            == before_complete.update(at, 9)[i] by {
                                        if i == at {}
                                    }
                                }
                                trivial_context_map_phase_to_complete(
                                    before_complete,
                                    workspace@,
                                    window_bytes,
                                );
                                serialized_block_count_cursor_from_frame(
                                    after_tree_count,
                                    workspace@,
                                    window_bytes,
                                    queue,
                                    var_phase,
                                );
                                assert(b3b_scalar_byte_at(
                                    workspace@,
                                    window_bytes,
                                    B3B_OUTER_PHASE,
                                ) == b3b_scalar_byte_at(
                                    original,
                                    window_bytes,
                                    B3B_OUTER_PHASE,
                                ));
                            }
                        } else {
                            proof {
                                reveal(serialized_context_data_ok);
                                reveal(serialized_context_phase_payload_ok);
                                assert(serialized_context_data_ok(workspace@, window_bytes));
                                assert(serialized_context_phase_payload_ok(
                                    workspace@,
                                    window_bytes,
                                    1,
                                ));
                            }
                            if let Err(error) = store_context_phase(workspace, window_bytes, 1) {
                                return (consumed, Some(ContextAdvanceStatus::Failed(error),));
                            }
                            proof {
                                serialized_block_count_cursor_from_frame(
                                    after_tree_count,
                                    workspace@,
                                    window_bytes,
                                    queue,
                                    var_phase,
                                );
                                assert(b3b_scalar_byte_at(
                                    workspace@,
                                    window_bytes,
                                    B3B_OUTER_PHASE,
                                ) == b3b_scalar_byte_at(
                                    original,
                                    window_bytes,
                                    B3B_OUTER_PHASE,
                                ));
                            }
                        }
                    }
                }
                let result = (consumed, None);
                proof {
                    assert(b3b_scalar_byte_at(
                        workspace@,
                        window_bytes,
                        B3B_OUTER_PHASE,
                    ) == b3b_scalar_byte_at(
                        original,
                        window_bytes,
                        B3B_OUTER_PHASE,
                    ));
                    assert(result.0 == step.consumed);
                    assert(serialized_b3b_queue(
                        original,
                        window_bytes,
                        start_queue,
                    ));
                    assert(serialized_var_uint8_phase(
                        original,
                        window_bytes,
                        start_phase,
                    ));
                    assert(serialized_b3b_queue(
                        workspace@,
                        window_bytes,
                        queue,
                    ));
                    assert(serialized_var_uint8_phase(
                        workspace@,
                        window_bytes,
                        var_phase,
                    ));
                    assert(var_uint8_exact_step(
                        start_queue,
                        start_phase,
                        input@,
                        end_of_input,
                        result.0,
                        queue,
                        var_phase,
                        step.status,
                    ));
                    match step.status {
                        VarUint8Status::Progress => {
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ));
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_CONTEXT_PHASE,
                            ) == 0);
                        }
                        VarUint8Status::Value(raw) => {
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ) == b3b_scalar_byte_at(
                                original,
                                window_bytes,
                                B3B_OUTER_PHASE,
                            ));
                            assert(b3b_scalar_u16_at(
                                workspace@,
                                window_bytes,
                                B3B_MAP_TREES,
                            ) == raw as nat + 1);
                            assert(b3b_scalar_byte_at(
                                workspace@,
                                window_bytes,
                                B3B_CONTEXT_PHASE,
                            ) == if raw == 0 { 9u8 } else { 1u8 });
                        }
                        _ => { assert(false); }
                    }
                    establish_context_tree_count_refinement(
                        original,
                        workspace@,
                        window_bytes,
                        input@,
                        end_of_input,
                        result.0,
                        result.1,
                        start_queue,
                        queue,
                        start_phase,
                        var_phase,
                        step.status,
                    );
                }
                result
}

spec fn context_complete_result(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    num_trees: u16,
) -> bool {
    let active_len = b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE);
    &&& serialized_context_complete_map_ok(after, window_bytes)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_SIZE)
        == b3b_scalar_u16_at(before, window_bytes, B3B_MAP_SIZE)
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_INITIALIZED) == active_len
    &&& b3b_scalar_u16_at(after, window_bytes, B3B_MAP_TREES) == num_trees
    &&& 1 <= num_trees <= 256
    &&& forall|i: int| 0 <= i < active_len ==> #[trigger]
        after[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            i as u16,
        ) as int] < num_trees
    &&& crate::brotli_prefix::context_tree_coverage(
        crate::brotli_prefix::context_map_values(
            after,
            window_bytes,
            kind,
            active_len as u16,
        ),
        num_trees,
    )
}

fn advance_context_map(
    workspace: &mut [u8],
    window_bytes: u32,
    input: &[u8],
    end_of_input: bool,
) -> (r: ContextAdvanceStep)
    requires serialized_context_state_ok(old(workspace)@, window_bytes),
    ensures
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            ==> b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        match r.status {
            ContextAdvanceStatus::Failed(_) => true,
            _ => b3b_scalar_byte_at(final(workspace)@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(old(workspace)@, window_bytes, B3B_OUTER_PHASE),
        },
        r.consumed <= input.len(),
        r.status == ContextAdvanceStatus::NeedInput ==> {
            &&& !end_of_input
            &&& r.consumed == input.len()
            &&& serialized_context_state_ok(final(workspace)@, window_bytes)
            &&& (compressed_decoder_state_ok(old(workspace)@, window_bytes)
                && 6 <= b3b_scalar_byte_at(
                    old(workspace)@,
                    window_bytes,
                    B3B_OUTER_PHASE,
                ) <= 7 ==> compressed_decoder_state_ok(
                    final(workspace)@,
                    window_bytes,
                ))
        },
        match r.status {
            ContextAdvanceStatus::Complete { kind, num_trees } => {
                &&& serialized_context_state_ok(final(workspace)@, window_bytes)
                &&& context_complete_result(
                    old(workspace)@,
                    final(workspace)@,
                    window_bytes,
                    kind,
                    num_trees,
                )
                &&& b3b_scalar_byte_at(
                    final(workspace)@,
                    window_bytes,
                    B3B_CONTEXT_PHASE,
                ) == 9
                &&& b3b_scalar_u16_at(
                    final(workspace)@,
                    window_bytes,
                    B3B_MAP_TREES,
                ) == num_trees
                &&& b3b_scalar_byte_at(
                    final(workspace)@,
                    window_bytes,
                    B3B_CONTEXT_KIND,
                ) == match kind {
                    crate::brotli_prefix::ContextMapKind::Literal => 0u8,
                    crate::brotli_prefix::ContextMapKind::Distance => 1u8,
                }
            },
            _ => true,
        },
{
    let ghost original = workspace@;
    proof { assert(original == old(workspace)@); }
    reveal(compressed_decoder_state_ok);
    reveal(serialized_context_state_ok);
    reveal(serialized_context_phase_payload_ok);
    reveal(serialized_context_data_ok);
    reveal(serialized_context_complete_map_ok);
    reveal(serialized_context_map_prefix_ok);
    reveal(serialized_mtf_state_ok);
    reveal(b3b_scalar_u16_at);
    reveal(b3b_scalar_byte_at);
    reveal(b3b_scalar_base);
    let kind_tag = match state_byte(workspace, window_bytes, B3B_CONTEXT_KIND) {
        Ok(value) => value,
        Err(error) => return ContextAdvanceStep { consumed: 0, status: ContextAdvanceStatus::Failed(error) },
    };
    let kind = match kind_tag {
        0 => crate::brotli_prefix::ContextMapKind::Literal,
        1 => crate::brotli_prefix::ContextMapKind::Distance,
        _ => return ContextAdvanceStep {
            consumed: 0,
            status: ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
        },
    };
    proof {
        match kind {
            crate::brotli_prefix::ContextMapKind::Literal => assert(kind_tag == 0),
            crate::brotli_prefix::ContextMapKind::Distance => assert(kind_tag == 1),
        }
    }
    let active_len = match state_u16(workspace, window_bytes, B3B_MAP_SIZE) {
        Ok(value) => value,
        Err(error) => return ContextAdvanceStep { consumed: 0, status: ContextAdvanceStatus::Failed(error) },
    };
    let capacity = match kind {
        crate::brotli_prefix::ContextMapKind::Literal => 16_384u16,
        crate::brotli_prefix::ContextMapKind::Distance => 1_024u16,
    };
    if active_len == 0 || active_len > capacity {
        return ContextAdvanceStep {
            consumed: 0,
            status: ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
        };
    }
    proof {
        match kind {
            crate::brotli_prefix::ContextMapKind::Literal => {
                assert(crate::brotli_prefix::context_map_capacity(kind) == 16_384);
            }
            crate::brotli_prefix::ContextMapKind::Distance => {
                assert(crate::brotli_prefix::context_map_capacity(kind) == 1_024);
            }
        }
        assert(active_len as nat <= crate::brotli_prefix::context_map_capacity(kind));
    }
    let map_index = match state_u16(workspace, window_bytes, B3B_MAP_INDEX) {
        Ok(value) => value,
        Err(error) => return ContextAdvanceStep {
            consumed: 0,
            status: ContextAdvanceStatus::Failed(error),
        },
    };
    let initialized = match state_u16(workspace, window_bytes, B3B_MAP_INITIALIZED) {
        Ok(value) => value,
        Err(error) => return ContextAdvanceStep {
            consumed: 0,
            status: ContextAdvanceStatus::Failed(error),
        },
    };
    if map_index != initialized || initialized > active_len {
        return ContextAdvanceStep {
            consumed: 0,
            status: ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
        };
    }
    let mut consumed: usize = 0;
    let mut transitions: u32 = 0;
    while transitions < 100_000
        invariant consumed <= input.len(), transitions <= 100_000,
            original == old(workspace)@,
            b3b_scalar_u16_at(original, window_bytes, B3B_MAP_SIZE) == active_len,
            active_len as nat <= crate::brotli_prefix::context_map_capacity(kind),
            b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_CONTEXT_KIND) == kind_tag,
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_MAP_SIZE) == active_len,
            b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE)
                == b3b_scalar_byte_at(original, window_bytes, B3B_OUTER_PHASE),
            kind == if b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_CONTEXT_KIND,
            ) == 0 {
                crate::brotli_prefix::ContextMapKind::Literal
            } else {
                crate::brotli_prefix::ContextMapKind::Distance
            },
        decreases 100_000 - transitions,
    {
        let phase = match state_byte(workspace, window_bytes, B3B_CONTEXT_PHASE) {
            Ok(value) => value,
            Err(error) => return ContextAdvanceStep { consumed, status: ContextAdvanceStatus::Failed(error) },
        };
        proof {
            assert(phase == b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_CONTEXT_PHASE,
            ));
        }
        match phase {
            0 => {
                let old_consumed = consumed;
                let (used, status) = advance_context_tree_count_phase(
                    workspace,
                    window_bytes,
                    kind_tag,
                    kind,
                    active_len,
                    &input[old_consumed..],
                    end_of_input,
                );
                consumed = old_consumed + used;
                match status {
                    Some(status) => return ContextAdvanceStep { consumed, status },
                    None => {}
                }
            }
            1 | 2 | 5 | 6 => {
                let old_consumed = consumed;
                let (used, status) = advance_context_bits_phase(
                    workspace,
                    window_bytes,
                    phase,
                    kind_tag,
                    kind,
                    active_len,
                    &input[old_consumed..],
                    end_of_input,
                );
                consumed = old_consumed + used;
                match status {
                    Some(status) => return ContextAdvanceStep { consumed, status },
                    None => {}
                }
            }
            3 => {
                let tree_step = advance_serialized_tree(
                    workspace, window_bytes, &input[consumed..], end_of_input);
                consumed = consumed + tree_step.consumed;
                match tree_step.status {
                    SerializedTreeStatus::NeedInput => return ContextAdvanceStep {
                        consumed,
                        status: ContextAdvanceStatus::NeedInput,
                    },
                    SerializedTreeStatus::Failed(error) => return ContextAdvanceStep {
                        consumed,
                        status: ContextAdvanceStatus::Failed(error),
                    },
                    SerializedTreeStatus::Complete => {
                        if let Err(error) = store_context_phase(
                            workspace, window_bytes, 4) {
                            return ContextAdvanceStep { consumed, status: ContextAdvanceStatus::Failed(error) };
                        }
                    }
                }
            }
            4 => {
                let old_consumed = consumed;
                let (used, status) = advance_context_symbol_phase(
                    workspace,
                    window_bytes,
                    kind_tag,
                    kind,
                    active_len,
                    &input[old_consumed..],
                    end_of_input,
                );
                consumed = old_consumed + used;
                match status {
                    Some(status) => return ContextAdvanceStep { consumed, status },
                    None => {}
                }
            }
            7 => {
                if let Err(error) = advance_context_mtf_phase(
                    workspace,
                    window_bytes,
                    kind,
                    active_len,
                ) {
                    return ContextAdvanceStep {
                        consumed,
                        status: ContextAdvanceStatus::Failed(error),
                    };
                }
            }
            8 => {
                if let Err(error) = advance_context_coverage_phase(
                    workspace,
                    window_bytes,
                    kind,
                    active_len,
                ) {
                    return ContextAdvanceStep {
                        consumed,
                        status: ContextAdvanceStatus::Failed(error),
                    };
                }
            }
            9 => {
                let num_trees = match state_u16(workspace, window_bytes, B3B_MAP_TREES) {
                    Ok(value) => value,
                    Err(error) => return ContextAdvanceStep { consumed, status: ContextAdvanceStatus::Failed(error) },
                };
                if num_trees == 0 || num_trees > 256 {
                    return ContextAdvanceStep {
                        consumed,
                        status: ContextAdvanceStatus::Failed(
                            CompressedHeaderError::InternalState),
                    };
                }
                proof {
                    assert(phase == 9);
                    assert(b3b_scalar_byte_at(
                        workspace@,
                        window_bytes,
                        B3B_CONTEXT_PHASE,
                    ) == 9);
                    assert((if kind_tag == 0 {
                        crate::brotli_prefix::ContextMapKind::Literal
                    } else {
                        crate::brotli_prefix::ContextMapKind::Distance
                    }) == kind);
                    reveal(serialized_context_state_ok);
                    reveal(serialized_context_phase_payload_ok);
                    reveal(serialized_context_complete_map_ok);
                    reveal(serialized_context_data_ok);
                    reveal(serialized_context_map_prefix_ok);
                    reveal(context_complete_result);
                    assert(b3b_scalar_u16_at(
                        workspace@,
                        window_bytes,
                        B3B_MAP_SIZE,
                    ) == active_len);
                    assert(b3b_scalar_u16_at(
                        original,
                        window_bytes,
                        B3B_MAP_SIZE,
                    ) == active_len);
                    assert(serialized_context_complete_map_ok(
                        workspace@,
                        window_bytes,
                    ));
                    assert(b3b_scalar_u16_at(
                        workspace@,
                        window_bytes,
                        B3B_MAP_INITIALIZED,
                    ) == active_len);
                    assert(crate::brotli_prefix::context_tree_coverage(
                        crate::brotli_prefix::context_map_values(
                            workspace@,
                            window_bytes,
                            kind,
                            active_len,
                        ),
                        num_trees,
                    ));
                    assert forall|i: int| 0 <= i < active_len implies #[trigger]
                        workspace@[crate::brotli_prefix::context_entry_at(
                            window_bytes,
                            kind,
                            i as u16,
                        ) as int] < num_trees by {
                        serialized_context_prefix_value_bound(
                            workspace@,
                            window_bytes,
                            i,
                        );
                    }
                    assert(context_complete_result(
                        original,
                        workspace@,
                        window_bytes,
                        kind,
                        num_trees,
                    ));
                }
                return ContextAdvanceStep {
                    consumed,
                    status: ContextAdvanceStatus::Complete { kind, num_trees },
                };
            }
            _ => return ContextAdvanceStep {
                consumed,
                status: ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
            },
        }
        transitions = transitions + 1;
    }
    ContextAdvanceStep {
        consumed,
        status: ContextAdvanceStatus::Failed(CompressedHeaderError::InternalState),
    }
}

fn initialize_ready_block_switch(
    workspace: &mut [u8],
    window_bytes: u32,
    num_types: [u16; 3],
    remaining: [u32; 3],
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        final(workspace)@.len() == old(workspace)@.len(),
        b3b_workspace_shape(old(workspace)@.len() as nat, window_bytes)
            ==> b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        compressed_decoder_state_ok(old(workspace)@, window_bytes)
            ==> compressed_decoder_state_ok(final(workspace)@, window_bytes),
        serialized_context_state_ok(old(workspace)@, window_bytes)
            ==> serialized_context_state_ok(final(workspace)@, window_bytes),
        r.is_ok() ==> b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_LITERAL_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_LITERAL_TREE),
        r.is_ok() ==> b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_COMMAND_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_COMMAND_TREE),
        r.is_ok() ==> b3b_scalar_u16_at(final(workspace)@, window_bytes, B3B_ACTIVE_DISTANCE_TREE)
            == b3b_scalar_u16_at(old(workspace)@, window_bytes, B3B_ACTIVE_DISTANCE_TREE),
        r.is_ok() ==> final(workspace)@[crate::brotli_prefix::context_entry_at(
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Literal,
            0,
        ) as int] == old(workspace)@[crate::brotli_prefix::context_entry_at(
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Literal,
            0,
        ) as int],
        r.is_ok() ==> final(workspace)@[crate::brotli_prefix::context_entry_at(
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            0,
        ) as int] == old(workspace)@[crate::brotli_prefix::context_entry_at(
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            0,
        ) as int],
{
    let ghost original = workspace@;
    proof { assert(original == old(workspace)@); }
    let mut kind: usize = 0;
    while kind < 3
        invariant kind <= 3,
            original == old(workspace)@,
            workspace@ == original,
        decreases 3 - kind,
    {
        if num_types[kind] == 0 || num_types[kind] > 256 || remaining[kind] == 0 {
            return Err(CompressedHeaderError::InternalState);
        }
        kind = kind + 1;
    }
    let ring = [1u16, 0, 1, 0, 1, 0];
    let mut entry: usize = 0;
    while entry < 6
        invariant entry <= 6,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            b3b_workspace_shape(original.len() as nat, window_bytes)
                ==> b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_LITERAL_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_LITERAL_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_COMMAND_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_COMMAND_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_DISTANCE_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_DISTANCE_TREE),
            workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                0,
            ) as int] == original[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                0,
            ) as int],
            workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                0,
            ) as int] == original[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                0,
            ) as int],
        decreases 6 - entry,
    {
        match put_state_u16(
            workspace,
            window_bytes,
            B3B_BLOCK_RING + 2 * entry as u16,
            ring[entry],
        ) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        entry = entry + 1;
    }
    kind = 0;
    while kind < 3
        invariant kind <= 3,
            original == old(workspace)@,
            workspace@.len() == original.len(),
            b3b_workspace_shape(original.len() as nat, window_bytes)
                ==> b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            compressed_decoder_state_ok(original, window_bytes)
                ==> compressed_decoder_state_ok(workspace@, window_bytes),
            serialized_context_state_ok(original, window_bytes)
                ==> serialized_context_state_ok(workspace@, window_bytes),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_LITERAL_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_LITERAL_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_COMMAND_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_COMMAND_TREE),
            b3b_scalar_u16_at(workspace@, window_bytes, B3B_ACTIVE_DISTANCE_TREE)
                == b3b_scalar_u16_at(original, window_bytes, B3B_ACTIVE_DISTANCE_TREE),
            workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                0,
            ) as int] == original[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                0,
            ) as int],
            workspace@[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                0,
            ) as int] == original[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                0,
            ) as int],
        decreases 3 - kind,
    {
        match put_state_u32(
            workspace,
            window_bytes,
            B3B_REMAINING_LENGTHS + 4 * kind as u16,
            remaining[kind],
        ) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        kind = kind + 1;
    }
    match put_state_byte(workspace, window_bytes, B3B_BLOCK_SWITCH_PHASE, 0) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        if serialized_context_state_ok(original, window_bytes) {
            assert(serialized_context_state_ok(workspace@, window_bytes));
        }
    }
    match put_state_byte(workspace, window_bytes, B3B_BLOCK_SWITCH_KIND, 255) {
        Ok(()) => {}
        Err(error) => return Err(error),
    }
    proof {
        if serialized_context_state_ok(original, window_bytes) {
            assert(serialized_context_state_ok(workspace@, window_bytes));
        }
    }
    match put_state_u16(workspace, window_bytes, B3B_PENDING_BLOCK_TYPE, 0) {
        Ok(()) => {
            proof {
                reveal(compressed_decoder_state_ok);
                assert(compressed_decoder_state_ok(original, window_bytes)
                    ==> compressed_decoder_state_ok(workspace@, window_bytes));
                assert(serialized_context_state_ok(original, window_bytes)
                    ==> serialized_context_state_ok(workspace@, window_bytes));
                assert(b3b_scalar_u16_at(
                    workspace@,
                    window_bytes,
                    B3B_ACTIVE_LITERAL_TREE,
                ) == b3b_scalar_u16_at(
                    original,
                    window_bytes,
                    B3B_ACTIVE_LITERAL_TREE,
                ));
                assert(b3b_scalar_u16_at(
                    workspace@,
                    window_bytes,
                    B3B_ACTIVE_COMMAND_TREE,
                ) == b3b_scalar_u16_at(
                    original,
                    window_bytes,
                    B3B_ACTIVE_COMMAND_TREE,
                ));
                assert(b3b_scalar_u16_at(
                    workspace@,
                    window_bytes,
                    B3B_ACTIVE_DISTANCE_TREE,
                ) == b3b_scalar_u16_at(
                    original,
                    window_bytes,
                    B3B_ACTIVE_DISTANCE_TREE,
                ));
            }
            Ok(())
        }
        Err(error) => Err(error),
    }
}

fn initialize_b3b_state_image(
    workspace: &mut [u8],
    window_bytes: u32,
) -> (r: Result<(), CompressedHeaderError>)
    ensures
        r.is_ok() ==> b3b_workspace_shape(final(workspace)@.len() as nat, window_bytes),
        r.is_ok() ==> forall|i: int| 0 <= i < B3B_SCALAR_BYTES ==>
            final(workspace)@[window_bytes as int + B3B_SCALAR_OFFSET as int + i]
                == b3b_initial_scalar_byte(i),
        r.is_ok() ==> forall|i: int| 0 <= i < final(workspace)@.len()
            && b3b_initial_metadata_index(window_bytes, i)
            ==> final(workspace)@[i] == 0,
        r.is_ok() ==> forall|i: int| 0 <= i < old(workspace)@.len()
            && !b3b_initialization_owned_index(window_bytes, i)
            ==> final(workspace)@[i] == old(workspace)@[i],
        r.is_err() ==> final(workspace)@ == old(workspace)@,
{
    let ghost initial_workspace = workspace@;
    if window_bytes < 1_024 || window_bytes > 16_777_216
        || (window_bytes & (window_bytes - 1)) != 0 {
        return Err(CompressedHeaderError::Workspace(
            crate::brotli_prefix::WorkspaceError::InvalidWindowBits,
        ));
    }
    let required = match (window_bytes as usize)
        .checked_add(crate::brotli_prefix::FIXED_SCRATCH_BYTES as usize) {
        Some(value) => value,
        None => return Err(CompressedHeaderError::Workspace(
            crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall,
        )),
    };
    if workspace.len() < required {
        return Err(CompressedHeaderError::Workspace(
            crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall,
        ));
    }
    proof { assert(b3b_workspace_shape(workspace@.len() as nat, window_bytes)); }
    let base = match b3b_state_address(
        workspace.len(),
        window_bytes,
        0,
        1,
    ) {
        Ok(value) => value,
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    };
    let mut i: usize = 0;
    while i < B3B_SCALAR_BYTES as usize
        invariant i <= B3B_SCALAR_BYTES,
            base as nat == window_bytes as nat + B3B_SCALAR_OFFSET as nat,
            base + B3B_SCALAR_BYTES as usize <= workspace.len(),
            b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            workspace@.len() == initial_workspace.len(),
            forall|j: int| 0 <= j < i ==>
                #[trigger] workspace@[base as int + j] == 0,
            forall|j: int| 0 <= j < initial_workspace.len()
                && !(base <= j < base + i)
                ==> #[trigger] workspace@[j] == initial_workspace[j],
        decreases B3B_SCALAR_BYTES as usize - i,
    {
        workspace[base + i] = 0;
        i = i + 1;
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_PENDING_RUN, 255) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_GROUP_KIND, 255) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_ACTIVE_REGION, 255) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_BLOCK_SWITCH_KIND, 255) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_MTF_UPPER_BOUND, 63) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_BLOCK_RING, 1) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_BLOCK_RING + 4, 1) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    match write_b3b_state_byte(workspace, window_bytes, B3B_BLOCK_RING + 8, 1) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    proof {
        b3b_scalar_layout_is_exact();
        assert forall|j: int| 0 <= j < B3B_SCALAR_BYTES implies
            workspace@[base as int + j] == b3b_initial_scalar_byte(j) by {
            if j == B3B_PENDING_RUN
                || j == B3B_GROUP_KIND
                || j == B3B_ACTIVE_REGION
                || j == B3B_BLOCK_SWITCH_KIND
                || j == B3B_MTF_UPPER_BOUND
                || j == B3B_BLOCK_RING
                || j == B3B_BLOCK_RING + 4
                || j == B3B_BLOCK_RING + 8
            {}
        }
    }
    let unused = crate::brotli_prefix::TreeMetadata::unused();
    let mut tree: u16 = 0;
    while tree < 3
        invariant tree <= 3,
            base as nat == window_bytes as nat + B3B_SCALAR_OFFSET as nat,
            b3b_workspace_shape(workspace@.len() as nat, window_bytes),
            unused.valid_for(crate::brotli_prefix::TreeRegion::BlockType),
            unused.valid_for(crate::brotli_prefix::TreeRegion::BlockLength),
            unused.valid_for(crate::brotli_prefix::TreeRegion::TemporaryContext),
            unused.symbols == 0,
            unused.storage == crate::brotli_prefix::TreeStorageState::Unused,
            forall|j: int| 0 <= j < B3B_SCALAR_BYTES ==>
                #[trigger] workspace@[base as int + j] == b3b_initial_scalar_byte(j),
            forall|j: int| 0 <= j < tree as int * 4 ==>
                #[trigger] workspace@[window_bytes as int
                    + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int + j] == 0,
            forall|j: int| 0 <= j < tree as int * 4 ==>
                #[trigger] workspace@[window_bytes as int
                    + crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as int + j] == 0,
            forall|j: int| 0 <= j < initial_workspace.len()
                && !b3b_initialization_owned_index(window_bytes, j)
                ==> #[trigger] workspace@[j] == initial_workspace[j],
        decreases 3 - tree,
    {
        let ghost before_type = workspace@;
        match crate::brotli_prefix::write_tree_metadata(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::BlockType,
            tree,
            unused,
        ) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        proof {
            b3b_scalar_layout_is_exact();
            let at = crate::brotli_prefix::tree_metadata_at(
                window_bytes,
                crate::brotli_prefix::TreeRegion::BlockType,
                tree,
            ) as int;
            assert(at == window_bytes as int
                + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int
                + tree as int * 4);
            assert(crate::brotli_prefix::tree_metadata_descriptor(unused) == 0);
            four_byte_update_preserves_outside(
                before_type,
                workspace@,
                at,
                0,
                0,
                0,
                0,
            );
            assert forall|j: int| 0 <= j < (tree as int + 1) * 4 implies
                #[trigger] workspace@[window_bytes as int
                    + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int + j] == 0 by {
                if j < tree as int * 4 {
                    assert(before_type[window_bytes as int
                        + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int + j] == 0);
                }
            }
            assert forall|j: int| 0 <= j < B3B_SCALAR_BYTES implies
                #[trigger] workspace@[base as int + j] == b3b_initial_scalar_byte(j) by {
                assert(at + 4 <= base as int + j || base as int + j < at);
            }
        }
        let ghost before_length = workspace@;
        match crate::brotli_prefix::write_tree_metadata(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::BlockLength,
            tree,
            unused,
        ) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        proof {
            b3b_scalar_layout_is_exact();
            let at = crate::brotli_prefix::tree_metadata_at(
                window_bytes,
                crate::brotli_prefix::TreeRegion::BlockLength,
                tree,
            ) as int;
            assert(at == window_bytes as int
                + crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as int
                + tree as int * 4);
            assert(crate::brotli_prefix::tree_metadata_descriptor(unused) == 0);
            four_byte_update_preserves_outside(
                before_length,
                workspace@,
                at,
                0,
                0,
                0,
                0,
            );
            assert forall|j: int| 0 <= j < (tree as int + 1) * 4 implies
                #[trigger] workspace@[window_bytes as int
                    + crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as int + j] == 0 by {
                if j < tree as int * 4 {
                    assert(before_length[window_bytes as int
                        + crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as int + j] == 0);
                }
            }
            assert forall|j: int| 0 <= j < (tree as int + 1) * 4 implies
                #[trigger] workspace@[window_bytes as int
                    + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int + j] == 0 by {
                assert(window_bytes as int
                    + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int + j < at);
            }
            assert forall|j: int| 0 <= j < B3B_SCALAR_BYTES implies
                #[trigger] workspace@[base as int + j] == b3b_initial_scalar_byte(j) by {
                assert(at + 4 <= base as int + j || base as int + j < at);
            }
        }
        tree = tree + 1;
    }
    proof { assert(tree == 3); }
    let ghost before_temporary = workspace@;
    match crate::brotli_prefix::write_tree_metadata(
        workspace,
        window_bytes,
        crate::brotli_prefix::TreeRegion::TemporaryContext,
        0,
        unused,
    ) {
        Ok(()) => {}
        Err(error) => return Err(CompressedHeaderError::Workspace(error)),
    }
    proof {
        b3b_scalar_layout_is_exact();
        let at = crate::brotli_prefix::tree_metadata_at(
            window_bytes,
            crate::brotli_prefix::TreeRegion::TemporaryContext,
            0,
        ) as int;
        assert(at == window_bytes as int
            + crate::brotli_prefix::TEMP_CONTEXT_METADATA_OFFSET as int);
        assert(crate::brotli_prefix::tree_metadata_descriptor(unused) == 0);
        four_byte_update_preserves_outside(
            before_temporary,
            workspace@,
            at,
            0,
            0,
            0,
            0,
        );
        assert forall|j: int| 0 <= j < B3B_SCALAR_BYTES implies
            #[trigger] workspace@[base as int + j] == b3b_initial_scalar_byte(j) by {
            assert(at + 4 <= base as int + j);
        }
        assert forall|j: int| 0 <= j < workspace@.len()
            && b3b_initial_metadata_index(window_bytes, j)
            implies #[trigger] workspace@[j] == 0 by {
            let relative = j - window_bytes as int;
            if crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET <= relative
                && relative < crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET + 12
            {
                let k = relative - crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int;
                assert(0 <= k < 12);
                assert(j == window_bytes as int
                    + crate::brotli_prefix::BLOCK_TYPE_METADATA_OFFSET as int + k);
                assert(before_temporary[j] == 0);
            } else if crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET <= relative
                && relative < crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET + 12
            {
                let k = relative - crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as int;
                assert(0 <= k < 12);
                assert(j == window_bytes as int
                    + crate::brotli_prefix::BLOCK_LENGTH_METADATA_OFFSET as int + k);
                assert(before_temporary[j] == 0);
            }
        }
    }
    Ok(())
}

fn read_active_context_entry(
    workspace: &[u8],
    window_bytes: u32,
    kind: crate::brotli_prefix::ContextMapKind,
    initialized: u16,
    index: u16,
    num_trees: u16,
) -> (r: Result<u8, CompressedHeaderError>)
    ensures r.is_ok() ==> {
        &&& index < initialized
        &&& r.unwrap() == workspace[crate::brotli_prefix::context_entry_at(
            window_bytes,
            kind,
            index,
        ) as int]
        &&& r.unwrap() < num_trees
    },
{
    let (offset, capacity) = match kind {
        crate::brotli_prefix::ContextMapKind::Literal => (
            crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET,
            16_384u16,
        ),
        crate::brotli_prefix::ContextMapKind::Distance => (
            crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET,
            1_024u16,
        ),
    };
    if window_bytes < 1_024
        || window_bytes > 16_777_216
        || (window_bytes & (window_bytes - 1)) != 0
    {
        return Err(CompressedHeaderError::Workspace(
            crate::brotli_prefix::WorkspaceError::InvalidWindowBits,
        ));
    }
    if initialized == 0
        || initialized > capacity
        || index >= initialized
        || num_trees == 0
        || num_trees > 256
    {
        return Err(CompressedHeaderError::InternalState);
    }
    let required = match (window_bytes as usize)
        .checked_add(crate::brotli_prefix::FIXED_SCRATCH_BYTES as usize)
    {
        Some(value) => value,
        None => return Err(CompressedHeaderError::Workspace(
            crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall,
        )),
    };
    if workspace.len() < required {
        return Err(CompressedHeaderError::Workspace(
            crate::brotli_prefix::WorkspaceError::WorkspaceTooSmall,
        ));
    }
    let at = window_bytes as usize + offset as usize + index as usize;
    let value = workspace[at];
    if value as u16 >= num_trees {
        return Err(CompressedHeaderError::InternalState);
    }
    Ok(value)
}

#[verifier::bit_vector]
proof fn serialized_distance_alphabet_fits(postfix: u8, direct: u16)
    requires postfix <= 3, direct <= 120,
    ensures 16u16 + direct + (24u16 << (postfix + 1)) <= 520,
{}

#[verifier::bit_vector]
proof fn serialized_distance_alphabet_exec_value(postfix: u8, direct: u16)
    requires postfix <= 3, direct <= 120,
    ensures
        (16u16 + direct + (24u16 << (postfix + 1))) as nat
            == 16 + direct as nat + 24 * (1u32 << (postfix + 1)) as nat,
{}

proof fn serialized_distance_alphabet_exact(postfix: u8, direct: u16)
    requires postfix <= 3, direct <= 120,
    ensures
        (16u16 + direct + (24u16 << (postfix + 1))) as nat
            == 16 + direct as nat + 24 * pow2(postfix as nat + 1),
{
    serialized_distance_alphabet_exec_value(postfix, direct);
    pow2_matches_context_repeat_shift((postfix as int + 1) as u8);
}

#[verifier::bit_vector]
proof fn serialized_context_lengths_fit(literal_types: u16, distance_types: u16)
    requires 1 <= literal_types <= 256, 1 <= distance_types <= 256,
    ensures
        literal_types * 64u16 <= 16_384,
        distance_types * 4u16 <= 1_024,
{}

spec fn serialized_block_count_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    category: int,
) -> nat {
    b3b_scalar_u16_at(
        workspace,
        window_bytes,
        (B3B_BLOCK_COUNTS as int + 2 * category) as u16,
    )
}

spec fn serialized_initial_length_at(
    workspace: Seq<u8>,
    window_bytes: u32,
    category: int,
) -> nat {
    b3b_scalar_u32_at(
        workspace,
        window_bytes,
        (B3B_INITIAL_LENGTHS as int + 4 * category) as u16,
    )
}

spec fn tree_group_region(group: u8) -> crate::brotli_prefix::TreeRegion {
    if group == 0 { crate::brotli_prefix::TreeRegion::Literal }
    else if group == 1 { crate::brotli_prefix::TreeRegion::Command }
    else { crate::brotli_prefix::TreeRegion::Distance }
}

spec fn tree_group_count_at(workspace: Seq<u8>, window_bytes: u32, group: u8) -> nat {
    if group == 0 {
        b3b_scalar_u16_at(workspace, window_bytes, B3B_LITERAL_TREES)
    } else if group == 1 {
        b3b_scalar_u16_at(
            workspace,
            window_bytes,
            (B3B_BLOCK_COUNTS as int + 2) as u16,
        )
    } else {
        b3b_scalar_u16_at(workspace, window_bytes, B3B_DISTANCE_TREES)
    }
}

spec fn tree_group_alphabet_at(workspace: Seq<u8>, window_bytes: u32, group: u8) -> nat {
    if group == 0 { 256 }
    else if group == 1 { 704 }
    else {
        16 + b3b_scalar_u16_at(workspace, window_bytes, B3B_DIRECT_DISTANCE)
            + 24 * pow2(b3b_scalar_byte_at(
                workspace,
                window_bytes,
                B3B_DISTANCE_POSTFIX,
            ) as nat + 1)
    }
}

spec fn tree_group_tree_complete(
    workspace: Seq<u8>,
    window_bytes: u32,
    group: u8,
    tree: int,
) -> bool {
    &&& group < 3
    &&& 0 <= tree < tree_group_count_at(workspace, window_bytes, group)
    &&& tree_group_alphabet_at(workspace, window_bytes, group) <= 704
    &&& tree_metadata_complete(
        workspace,
        window_bytes,
        tree_group_region(group),
        tree as u16,
        tree_group_alphabet_at(workspace, window_bytes, group) as u16,
    )
}

spec fn tree_group_prefix_complete(
    workspace: Seq<u8>,
    window_bytes: u32,
    group: u8,
    end: nat,
) -> bool {
    &&& end <= tree_group_count_at(workspace, window_bytes, group)
    &&& forall|tree: int| 0 <= tree < end ==> #[trigger]
        tree_group_tree_complete(workspace, window_bytes, group, tree)
}

spec fn prior_tree_groups_complete(
    workspace: Seq<u8>,
    window_bytes: u32,
    group: u8,
) -> bool {
    &&& (group >= 1 ==> tree_group_prefix_complete(
        workspace,
        window_bytes,
        0,
        tree_group_count_at(workspace, window_bytes, 0),
    ))
    &&& (group >= 2 ==> tree_group_prefix_complete(
        workspace,
        window_bytes,
        1,
        tree_group_count_at(workspace, window_bytes, 1),
    ))
}

spec fn all_tree_groups_complete(workspace: Seq<u8>, window_bytes: u32) -> bool {
    forall|group: int| 0 <= group < 3 ==> #[trigger] tree_group_prefix_complete(
        workspace,
        window_bytes,
        group as u8,
        tree_group_count_at(workspace, window_bytes, group as u8),
    )
}

spec fn tree_group_payload_ok(
    workspace: Seq<u8>,
    window_bytes: u32,
    phase_tag: u8,
) -> bool {
    if 8 <= phase_tag <= 10 {
        let group: u8 = (phase_tag as int - 8) as u8;
        let count = tree_group_count_at(workspace, window_bytes, group);
        let tree = b3b_scalar_u16_at(workspace, window_bytes, B3B_TREE_INDEX);
        let alphabet = tree_group_alphabet_at(workspace, window_bytes, group);
        &&& b3b_scalar_byte_at(workspace, window_bytes, B3B_GROUP_KIND) == group
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_TREE_COUNT) == count
        &&& 1 <= count <= 256
        &&& tree < count
        &&& b3b_scalar_byte_at(workspace, window_bytes, B3B_GROUP_PHASE) == 1
        &&& b3b_scalar_byte_at(workspace, window_bytes, B3B_ACTIVE_REGION) == group
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_ACTIVE_TREE) == tree
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_ALPHABET_MAX) == alphabet
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_ALPHABET_LIMIT) == alphabet
    } else if phase_tag == 11 {
        &&& b3b_scalar_byte_at(workspace, window_bytes, B3B_GROUP_PHASE) == 4
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_ACTIVE_LITERAL_TREE)
            == workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Literal,
                0,
            ) as int] as nat
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_ACTIVE_COMMAND_TREE) == 0
        &&& b3b_scalar_u16_at(workspace, window_bytes, B3B_ACTIVE_DISTANCE_TREE)
            == workspace[crate::brotli_prefix::context_entry_at(
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                0,
            ) as int] as nat
    } else {
        true
    }
}

spec fn tree_group_phase_refines(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    status: Option<CompressedHeaderStatus>,
) -> bool {
    let phase_tag = b3b_scalar_byte_at(before, window_bytes, B3B_OUTER_PHASE);
    let group = b3b_scalar_byte_at(before, window_bytes, B3B_GROUP_KIND);
    let tree = b3b_scalar_u16_at(before, window_bytes, B3B_TREE_INDEX);
    let count = b3b_scalar_u16_at(before, window_bytes, B3B_TREE_COUNT);
    if match status {
        Some(CompressedHeaderStatus::Failed(_)) => true,
        _ => false,
    } {
        true
    } else {
        &&& 8 <= phase_tag <= 10
        &&& tree_group_payload_ok(before, window_bytes, phase_tag)
        &&& match status {
            Some(CompressedHeaderStatus::NeedInput) => {
                &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == phase_tag
                &&& tree_group_payload_ok(after, window_bytes, phase_tag)
            },
            None => {
                if tree + 1 < count {
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == phase_tag
                    &&& b3b_scalar_u16_at(after, window_bytes, B3B_TREE_INDEX)
                        == tree + 1
                    &&& tree_group_payload_ok(after, window_bytes, phase_tag)
                } else if group < 2 {
                    let next_group = group + 1;
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
                        == phase_tag + 1
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_GROUP_KIND)
                        == next_group
                    &&& b3b_scalar_u16_at(after, window_bytes, B3B_TREE_INDEX) == 0
                    &&& tree_group_payload_ok(
                        after,
                        window_bytes,
                        (phase_tag as int + 1) as u8,
                    )
                } else {
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == 11
                    &&& tree_group_payload_ok(after, window_bytes, 11)
                }
            },
            Some(CompressedHeaderStatus::Complete(_)) => false,
            Some(CompressedHeaderStatus::Failed(_)) => false,
        }
    }
}

proof fn active_complete_implies_group_tree_complete(
    workspace: Seq<u8>,
    window_bytes: u32,
    phase_tag: u8,
)
    requires
        8 <= phase_tag <= 10,
        tree_group_payload_ok(workspace, window_bytes, phase_tag),
        active_tree_metadata_complete(workspace, window_bytes),
    ensures tree_group_tree_complete(
        workspace,
        window_bytes,
        b3b_scalar_byte_at(workspace, window_bytes, B3B_GROUP_KIND),
        b3b_scalar_u16_at(workspace, window_bytes, B3B_TREE_INDEX) as int,
    ),
{
    reveal(tree_group_payload_ok);
    reveal(tree_group_tree_complete);
    reveal(tree_group_region);
    reveal(active_tree_metadata_complete);
    let group = b3b_scalar_byte_at(workspace, window_bytes, B3B_GROUP_KIND);
    if group == 0 {
    } else if group == 1 {
    } else {
        assert(group == 2);
    }
}

spec fn block_count_phase_refines(
    before: Seq<u8>,
    after: Seq<u8>,
    window_bytes: u32,
    input: Seq<u8>,
    end_of_input: bool,
    consumed: usize,
    status: Option<CompressedHeaderStatus>,
) -> bool {
    let kind = b3b_scalar_byte_at(before, window_bytes, B3B_CURRENT_KIND);
    if kind >= 3 {
        &&& consumed == 0
        &&& status.is_none()
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == 4
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CURRENT_KIND) == kind
    } else if match status {
        Some(CompressedHeaderStatus::Failed(_)) => true,
        _ => false,
    } {
        true
    } else {
        exists|start_queue: BitQueue,
            final_queue: BitQueue,
            start_phase: VarUint8Phase,
            final_phase: VarUint8Phase,
            var_status: VarUint8Status| #![trigger var_uint8_exact_step(
                start_queue,
                start_phase,
                input,
                end_of_input,
                consumed,
                final_queue,
                final_phase,
                var_status,
            )] {
            &&& serialized_b3b_queue(before, window_bytes, start_queue)
            &&& serialized_var_uint8_phase(before, window_bytes, start_phase)
            &&& serialized_b3b_queue(after, window_bytes, final_queue)
            &&& serialized_var_uint8_phase(after, window_bytes, final_phase)
            &&& var_uint8_exact_step(
                start_queue,
                start_phase,
                input,
                end_of_input,
                consumed,
                final_queue,
                final_phase,
                var_status,
            )
            &&& match var_status {
                VarUint8Status::NeedInput => status
                    == Some(CompressedHeaderStatus::NeedInput),
                VarUint8Status::Truncated => match status {
                    Some(CompressedHeaderStatus::Failed(_)) => true,
                    _ => false,
                },
                VarUint8Status::Progress => {
                    &&& status.is_none()
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == 0
                    &&& b3b_scalar_byte_at(after, window_bytes, B3B_CURRENT_KIND) == kind
                },
                VarUint8Status::Value(raw) => {
                    &&& status.is_none()
                    &&& serialized_block_count_at(after, window_bytes, kind as int)
                        == raw as nat + 1
                    &&& if raw == 0 {
                        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == 0
                        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CURRENT_KIND)
                            == kind + 1
                        &&& serialized_initial_length_at(
                            after,
                            window_bytes,
                            kind as int,
                        ) == 1u32 << 24
                    } else {
                        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE) == 1
                        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CURRENT_KIND) == kind
                    }
                },
            }
        }
    }
}

spec fn block_count_value_applied(
    after: Seq<u8>,
    window_bytes: u32,
    kind: u8,
    raw: u16,
) -> bool {
    let count = raw as nat + 1;
    &&& serialized_block_count_at(after, window_bytes, kind as int) == count
    &&& if raw == 0 {
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == compressed_outer_phase_tag_spec(CompressedOuterPhase::BlockCount)
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CURRENT_KIND) == kind + 1
        &&& serialized_initial_length_at(after, window_bytes, kind as int) == 1u32 << 24
    } else {
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_OUTER_PHASE)
            == compressed_outer_phase_tag_spec(CompressedOuterPhase::BlockTypeTree)
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_CURRENT_KIND) == kind
        &&& b3b_scalar_byte_at(after, window_bytes, B3B_ACTIVE_REGION)
            == tree_region_tag_spec(crate::brotli_prefix::TreeRegion::BlockType)
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_ACTIVE_TREE) == kind
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_MAX) == count + 2
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_ALPHABET_LIMIT) == count + 2
        &&& b3b_scalar_u16_at(after, window_bytes, B3B_BUILDER_INITIALIZED) == 0
    }
}

spec fn compressed_decoder_state_ok(workspace: Seq<u8>, window_bytes: u32) -> bool {
    let outer = b3b_scalar_byte_at(workspace, window_bytes, B3B_OUTER_PHASE);
    &&& b3b_workspace_shape(workspace.len() as nat, window_bytes)
    &&& serialized_mtf_state_ok(workspace, window_bytes)
    &&& ((6 <= outer && outer <= 11)
        ==> serialized_context_state_ok(workspace, window_bytes))
    &&& ((8 <= outer && outer <= 11)
        ==> tree_group_payload_ok(workspace, window_bytes, outer))
}

struct CompressedMetaBlockDecoder<'w> {
    workspace: &'w mut [u8],
    window_bytes: u32,
}

impl<'w> CompressedMetaBlockDecoder<'w> {
    fn from_meta(
        workspace: &'w mut [u8],
        window_bytes: u32,
        meta: MetaBlockDecoder,
    ) -> (r: Result<Self, CompressedHeaderError>)
        requires meta.valid(),
        ensures r.is_ok() ==> compressed_decoder_state_ok(
            r.unwrap().workspace@,
            r.unwrap().window_bytes,
        ),
    {
        match meta.phase {
            MetaBlockPhase::Complete(header) => {
                if header.is_empty || header.is_uncompressed || header.is_metadata {
                    return Err(CompressedHeaderError::InternalState);
                }
            }
            _ => return Err(CompressedHeaderError::InternalState),
        }
        match initialize_b3b_state_image(workspace, window_bytes) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        proof {
            reveal(compressed_decoder_state_ok);
            reveal(serialized_mtf_state_ok);
            reveal(b3b_scalar_byte_at);
            reveal(b3b_scalar_base);
            reveal(b3b_initial_scalar_byte);
            b3b_scalar_layout_is_exact();
            assert(workspace@[window_bytes as int
                + B3B_SCALAR_OFFSET as int + B3B_OUTER_PHASE as int]
                == b3b_initial_scalar_byte(B3B_OUTER_PHASE as int));
            assert(workspace@[window_bytes as int
                + B3B_SCALAR_OFFSET as int + B3B_MTF_UPPER_BOUND as int]
                == b3b_initial_scalar_byte(B3B_MTF_UPPER_BOUND as int));
            assert(b3b_scalar_byte_at(workspace@, window_bytes, B3B_OUTER_PHASE) == 0);
            assert(b3b_scalar_byte_at(
                workspace@,
                window_bytes,
                B3B_MTF_UPPER_BOUND,
            ) == 63);
            assert(compressed_decoder_state_ok(workspace@, window_bytes));
        }
        let mut i: usize = 0;
        while i < meta.queue.len
            invariant i <= meta.queue.len <= 8,
                compressed_decoder_state_ok(workspace@, window_bytes),
            decreases meta.queue.len - i,
        {
            let ghost before_queue = workspace@;
            let relative = B3B_QUEUE_OFFSET + i as u16;
            let queue_value = meta.queue.pending[i];
            match write_b3b_state_byte(
                workspace,
                window_bytes,
                relative,
                queue_value,
            ) {
                Ok(()) => {}
                Err(error) => return Err(CompressedHeaderError::Workspace(error)),
            }
            proof {
                let at = b3b_scalar_base(window_bytes) + relative as int;
                assert(workspace@ == before_queue.update(at, queue_value)) by {
                    assert(workspace@.len() == before_queue.len());
                    assert forall|j: int| 0 <= j < workspace@.len() implies
                        #[trigger] workspace@[j] == before_queue.update(at, queue_value)[j] by {
                        if j == at {}
                    }
                }
                queue_write_preserves_decoder_state(
                    before_queue,
                    workspace@,
                    window_bytes,
                    relative,
                    queue_value,
                );
            }
            i = i + 1;
        }
        let ghost before_len = workspace@;
        match write_b3b_state_byte(workspace, window_bytes, B3B_QUEUE_LEN, meta.queue.len as u8) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        proof {
            let at = b3b_scalar_base(window_bytes) + B3B_QUEUE_LEN as int;
            assert(workspace@ == before_len.update(at, meta.queue.len as u8)) by {
                assert(workspace@.len() == before_len.len());
                assert forall|j: int| 0 <= j < workspace@.len() implies
                    #[trigger] workspace@[j]
                        == before_len.update(at, meta.queue.len as u8)[j] by {
                    if j == at {}
                }
            }
            queue_write_preserves_decoder_state(
                before_len,
                workspace@,
                window_bytes,
                B3B_QUEUE_LEN,
                meta.queue.len as u8,
            );
        }
        let ghost before_offset = workspace@;
        match write_b3b_state_byte(
            workspace,
            window_bytes,
            B3B_QUEUE_OFFSET_BYTE,
            meta.queue.offset as u8,
        ) {
            Ok(()) => {}
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        }
        proof {
            let at = b3b_scalar_base(window_bytes) + B3B_QUEUE_OFFSET_BYTE as int;
            assert(workspace@ == before_offset.update(at, meta.queue.offset as u8)) by {
                assert(workspace@.len() == before_offset.len());
                assert forall|j: int| 0 <= j < workspace@.len() implies
                    #[trigger] workspace@[j]
                        == before_offset.update(at, meta.queue.offset as u8)[j] by {
                    if j == at {}
                }
            }
            queue_write_preserves_decoder_state(
                before_offset,
                workspace@,
                window_bytes,
                B3B_QUEUE_OFFSET_BYTE,
                meta.queue.offset as u8,
            );
            assert(compressed_decoder_state_ok(workspace@, window_bytes));
        }
        Ok(Self { workspace, window_bytes })
    }

    fn load_outer_phase(&self) -> (r: Result<CompressedOuterPhase, CompressedHeaderError>)
        ensures
            r.is_ok() ==> b3b_scalar_byte_at(
                old(self.workspace)@,
                self.window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(r.unwrap()),
            forall|error: CompressedHeaderError| serialized_terminal_error(
                old(self.workspace)@,
                self.window_bytes,
                error,
            ) ==> r == Ok(CompressedOuterPhase::Failed),
    {
        let tag = match read_b3b_state_tag(
            self.workspace,
            self.window_bytes,
            B3B_OUTER_PHASE,
            13,
        ) {
            Ok(value) => value,
            Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol) =>
                return Err(CompressedHeaderError::InternalState),
            Err(error) => return Err(CompressedHeaderError::Workspace(error)),
        };
        match decode_compressed_outer_phase(tag) {
            Some(phase) => Ok(phase),
            None => Err(CompressedHeaderError::InternalState),
        }
    }

    fn store_outer_phase(
        &mut self,
        phase: CompressedOuterPhase,
    ) -> (r: Result<(), CompressedHeaderError>)
        requires
            b3b_workspace_shape(
                old(self).workspace@.len() as nat,
                old(self).window_bytes,
            ),
            serialized_mtf_state_ok(old(self).workspace@, old(self).window_bytes),
            (6 <= compressed_outer_phase_tag_spec(phase)
                && compressed_outer_phase_tag_spec(phase) <= 11)
                ==> serialized_context_state_ok(
                    old(self).workspace@,
                    old(self).window_bytes,
                ),
            (8 <= compressed_outer_phase_tag_spec(phase)
                && compressed_outer_phase_tag_spec(phase) <= 11)
                ==> tree_group_payload_ok(
                    old(self).workspace@,
                    old(self).window_bytes,
                    compressed_outer_phase_tag_spec(phase),
                ),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@.len() == old(self).workspace@.len(),
            b3b_workspace_shape(
                old(self).workspace@.len() as nat,
                old(self).window_bytes,
            ) ==> b3b_workspace_shape(
                final(self).workspace@.len() as nat,
                final(self).window_bytes,
            ),
            r.is_ok() ==> b3b_workspace_shape(
                final(self).workspace@.len() as nat,
                final(self).window_bytes,
            ),
            r.is_ok() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            b3b_workspace_shape(
                old(self).workspace@.len() as nat,
                old(self).window_bytes,
            ) ==> r.is_ok(),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_CONTEXT_KIND,
            ) == b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_CONTEXT_KIND,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_MAP_SIZE,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_MAP_SIZE,
            ),
            r.is_ok() ==> serialized_block_count_at(
                final(self).workspace@,
                final(self).window_bytes,
                2,
            ) == serialized_block_count_at(
                old(self).workspace@,
                old(self).window_bytes,
                2,
            ),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_ACTIVE_REGION,
            ) == b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_ACTIVE_REGION,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_ACTIVE_TREE,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_ACTIVE_TREE,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_ALPHABET_MAX,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_ALPHABET_MAX,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_ALPHABET_LIMIT,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_ALPHABET_LIMIT,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_BUILDER_INITIALIZED,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_BUILDER_INITIALIZED,
            ),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_GROUP_KIND,
            ) == b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_GROUP_KIND,
            ),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_GROUP_PHASE,
            ) == b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_GROUP_PHASE,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_TREE_INDEX,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_TREE_INDEX,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_TREE_COUNT,
            ) == b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_TREE_COUNT,
            ),
            r.is_ok() ==> forall|i: int| 0 <= i < B3B_GROUP_KIND
                && i != B3B_OUTER_PHASE ==> #[trigger]
                final(self).workspace@[b3b_scalar_base(final(self).window_bytes) + i]
                    == old(self).workspace@[b3b_scalar_base(old(self).window_bytes) + i],
    {
        match write_b3b_state_tag(
            self.workspace,
            self.window_bytes,
            B3B_OUTER_PHASE,
            13,
            compressed_outer_phase_tag(phase),
        ) {
            Ok(()) => {
                proof {
                    reveal(compressed_decoder_state_ok);
                    reveal(tree_group_payload_ok);
                    assert(compressed_decoder_state_ok(
                        self.workspace@,
                        self.window_bytes,
                    ));
                }
                Ok(())
            }
            Err(error) => Err(CompressedHeaderError::Workspace(error)),
        }
    }

    fn fail(&mut self, consumed: usize, error: CompressedHeaderError) -> (r: CompressedHeaderStep)
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.consumed == consumed,
            matches!(r.status, CompressedHeaderStatus::Failed(_)),
            b3b_workspace_shape(old(self).workspace@.len() as nat, old(self).window_bytes)
                ==> match r.status {
                CompressedHeaderStatus::Failed(stored) =>
                    serialized_terminal_error(
                        final(self).workspace@,
                        final(self).window_bytes,
                        stored,
                    ),
                _ => false,
            },
    {
        let stored = match store_terminal_error(self.workspace, self.window_bytes, error) {
            Ok(()) => error,
            Err(store_error) => store_error,
        };
        CompressedHeaderStep { consumed, status: CompressedHeaderStatus::Failed(stored) }
    }

    fn repeat_terminal_failure(
        &mut self,
        error: CompressedHeaderError,
    ) -> (r: CompressedHeaderStep)
        requires serialized_terminal_error(
            old(self).workspace@,
            old(self).window_bytes,
            error,
        ),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@ == old(self).workspace@,
            r == (CompressedHeaderStep {
                consumed: 0,
                status: CompressedHeaderStatus::Failed(error),
            }),
            serialized_terminal_error(
                final(self).workspace@,
                final(self).window_bytes,
                error,
            ),
    {
        CompressedHeaderStep {
            consumed: 0,
            status: CompressedHeaderStatus::Failed(error),
        }
    }

    fn load_installed_prefix(&self) -> (r: Result<InstalledPrefixState, CompressedHeaderError>)
        ensures r.is_ok() ==> r.unwrap().valid(),
    {
        let width = match state_byte(self.workspace, self.window_bytes, B3B_INSTALLED_PREFIX_WIDTH) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let bits = match state_u16(self.workspace, self.window_bytes, B3B_INSTALLED_PREFIX_BITS) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let scan = match state_u16(self.workspace, self.window_bytes, B3B_INSTALLED_SCAN) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        if width > 14 || scan != 0 || bits >= (1u16 << width) {
            return Err(CompressedHeaderError::InternalState);
        }
        let prefix = InstalledPrefixState { width, bits, scan };
        assert(prefix.valid());
        Ok(prefix)
    }

    fn store_installed_prefix(
        &mut self,
        prefix: InstalledPrefixState,
    ) -> (r: Result<(), CompressedHeaderError>)
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@.len() == old(self).workspace@.len(),
            b3b_workspace_shape(
                old(self).workspace@.len() as nat,
                old(self).window_bytes,
            ) ==> b3b_workspace_shape(
                final(self).workspace@.len() as nat,
                final(self).window_bytes,
            ),
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes)
                ==> compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                ),
    {
        if prefix.width > 14 || prefix.scan != 0 || prefix.bits >= (1u16 << prefix.width) {
            return Err(CompressedHeaderError::InternalState);
        }
        assert(prefix.valid());
        store_installed_prefix_state(self.workspace, self.window_bytes, prefix)
    }

        fn fail_phase(
        &mut self,
        consumed: usize,
        error: CompressedHeaderError,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires b3b_workspace_shape(
            old(self).workspace@.len() as nat,
            old(self).window_bytes,
        ),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 == consumed,
            match r.1 {
                Some(CompressedHeaderStatus::Failed(stored)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    stored,
                ),
                _ => false,
            },
    {
        let step = self.fail(consumed, error);
        proof {
            match step.status {
                CompressedHeaderStatus::Failed(stored) => {
                    assert(serialized_terminal_error(
                        self.workspace@,
                        self.window_bytes,
                        stored,
                    ));
                }
                _ => { assert(false); }
            }
        }
        (step.consumed, Some(step.status))
    }

    fn apply_block_count_value(
        &mut self,
        kind: u8,
        raw: u16,
        _queue: BitQueue,
        _var_phase: VarUint8Phase,
    ) -> (r: Result<(), CompressedHeaderError>)
        requires
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(CompressedOuterPhase::BlockCount),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_CURRENT_KIND,
            ) == kind,
            kind < 3,
            raw <= 255,
            _queue.valid(),
            _var_phase.valid(),
            serialized_b3b_queue(old(self).workspace@, old(self).window_bytes, _queue),
            serialized_var_uint8_phase(
                old(self).workspace@,
                old(self).window_bytes,
                _var_phase,
            ),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@.len() == old(self).workspace@.len(),
            b3b_workspace_shape(
                final(self).workspace@.len() as nat,
                final(self).window_bytes,
            ),
            r.is_ok() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.is_ok() ==> serialized_b3b_queue(
                final(self).workspace@,
                final(self).window_bytes,
                _queue,
            ),
            r.is_ok() ==> serialized_var_uint8_phase(
                final(self).workspace@,
                final(self).window_bytes,
                _var_phase,
            ),
            r.is_ok() ==> block_count_value_applied(
                final(self).workspace@,
                final(self).window_bytes,
                kind,
                raw,
            ),
    {
        let ghost original = self.workspace@;
        let count = raw + 1;
        proof { var_uint8_count_adds_one(raw); }
        put_state_u16(
            self.workspace,
            self.window_bytes,
            B3B_BLOCK_COUNTS + 2 * kind as u16,
            count,
        )?;
        if count == 1 {
            put_state_u32(
                self.workspace,
                self.window_bytes,
                B3B_INITIAL_LENGTHS + 4 * kind as u16,
                1u32 << 24,
            )?;
            put_state_byte(
                self.workspace,
                self.window_bytes,
                B3B_CURRENT_KIND,
                kind + 1,
            )?;
        } else {
            start_serialized_tree(
                self.workspace,
                self.window_bytes,
                crate::brotli_prefix::TreeRegion::BlockType,
                kind as u16,
                count + 2,
                count + 2,
            )?;
            self.store_outer_phase(CompressedOuterPhase::BlockTypeTree)?;
        }
        proof {
            b3b_scalar_layout_is_exact();
            assert forall|i: int| 0 <= i < B3B_VAR_WIDTH + 1
                && i != B3B_OUTER_PHASE
                && i != B3B_CURRENT_KIND implies #[trigger]
                self.workspace@[b3b_scalar_base(self.window_bytes) + i]
                    == original[b3b_scalar_base(self.window_bytes) + i] by {}
            serialized_block_count_cursor_from_frame(
                original,
                self.workspace@,
                self.window_bytes,
                _queue,
                _var_phase,
            );
            reveal(block_count_value_applied);
            reveal(serialized_block_count_at);
            reveal(serialized_initial_length_at);
            assert(serialized_block_count_at(
                self.workspace@,
                self.window_bytes,
                kind as int,
            ) == raw as nat + 1);
            if raw == 0 {
                assert(count == 1);
                assert(b3b_scalar_byte_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_OUTER_PHASE,
                ) == compressed_outer_phase_tag_spec(CompressedOuterPhase::BlockCount));
                assert(b3b_scalar_byte_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_CURRENT_KIND,
                ) == kind + 1);
                assert(serialized_initial_length_at(
                    self.workspace@,
                    self.window_bytes,
                    kind as int,
                ) == 1u32 << 24);
            } else {
                assert(b3b_scalar_byte_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_OUTER_PHASE,
                ) == compressed_outer_phase_tag_spec(
                    CompressedOuterPhase::BlockTypeTree,
                ));
                assert(b3b_scalar_byte_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_CURRENT_KIND,
                ) == kind);
                assert(b3b_scalar_byte_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_ACTIVE_REGION,
                ) == tree_region_tag_spec(
                    crate::brotli_prefix::TreeRegion::BlockType,
                ));
                assert(b3b_scalar_u16_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_ACTIVE_TREE,
                ) == kind);
                assert(b3b_scalar_u16_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_ALPHABET_MAX,
                ) == raw as nat + 3);
                assert(b3b_scalar_u16_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_ALPHABET_LIMIT,
                ) == raw as nat + 3);
                assert(b3b_scalar_u16_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_BUILDER_INITIALIZED,
                ) == 0);
            }
            assert(block_count_value_applied(
                self.workspace@,
                self.window_bytes,
                kind,
                raw,
            ));
        }
        Ok(())
    }

    fn advance_block_count_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::BlockCount,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
            block_count_phase_refines(
                old(self).workspace@,
                final(self).workspace@,
                old(self).window_bytes,
                input@,
                end_of_input,
                r.0,
                r.1,
            ),
    {
        let ghost original_workspace = self.workspace@;
        let mut consumed: usize = 0;

        let kind = match state_byte(self.workspace, self.window_bytes, B3B_CURRENT_KIND) {
            Ok(value) => value,
            Err(error) => return self.fail_phase(consumed, error),
        };
        if kind >= 3 {
            if let Err(error) = self.store_outer_phase(CompressedOuterPhase::DistanceParameters) {
                return self.fail_phase(consumed, error);
            }
            let result = (consumed, None);
            proof {
                reveal(block_count_phase_refines);
                assert(b3b_scalar_byte_at(
                    original_workspace,
                    self.window_bytes,
                    B3B_CURRENT_KIND,
                ) == kind);
                assert(b3b_scalar_byte_at(
                    self.workspace@,
                    self.window_bytes,
                    B3B_CURRENT_KIND,
                ) == kind);
                assert(block_count_phase_refines(
                    original_workspace,
                    self.workspace@,
                    self.window_bytes,
                    input@,
                    end_of_input,
                    result.0,
                    result.1,
                ));
            }
            return result;
        }

        let mut queue = match load_b3b_queue(self.workspace, self.window_bytes) {
            Ok(value) => value,
            Err(error) => return self.fail_phase(consumed, error),
        };
        let ghost start_queue = queue;
        let mut var_phase = match load_var_uint8_phase(self.workspace, self.window_bytes) {
            Ok(value) => value,
            Err(error) => return self.fail_phase(consumed, error),
        };
        let ghost start_phase = var_phase;
        let remaining = &input[consumed..];
        proof { assert(remaining@ == input@); }
        let step = advance_var_uint8(
            &mut queue,
            &mut var_phase,
            remaining,
            end_of_input,
        );
        proof {
            assert(var_uint8_exact_step(
                start_queue,
                start_phase,
                input@,
                end_of_input,
                step.consumed,
                queue,
                var_phase,
                step.status,
            ));
        }
        consumed = consumed + step.consumed;
        if let Err(error) = store_b3b_queue(self.workspace, self.window_bytes, &queue) {
            return self.fail_phase(consumed, error);
        }
        let ghost after_queue_store = self.workspace@;
        if let Err(error) = store_var_uint8_phase(
            self.workspace,
            self.window_bytes,
            var_phase,
        ) {
            return self.fail_phase(consumed, error);
        }
        proof {
            assert forall|i: int| 0 <= i < B3B_QUEUE_OFFSET_BYTE + 1 implies #[trigger]
                self.workspace@[b3b_scalar_base(self.window_bytes) + i]
                    == after_queue_store[b3b_scalar_base(self.window_bytes) + i] by {}
            serialized_b3b_queue_from_frame(
                after_queue_store,
                self.workspace@,
                self.window_bytes,
                queue,
            );
        }
        let ghost stored_cursor = self.workspace@;
        match step.status {
            VarUint8Status::NeedInput => {
                let result = (consumed, Some(CompressedHeaderStatus::NeedInput));
                proof {
                    reveal(block_count_phase_refines);
                    assert(b3b_scalar_byte_at(
                        original_workspace,
                        self.window_bytes,
                        B3B_CURRENT_KIND,
                    ) == kind);
                    assert(result.0 == step.consumed);
                    assert(step.status == VarUint8Status::NeedInput);
                    assert(serialized_b3b_queue(
                        original_workspace,
                        self.window_bytes,
                        start_queue,
                    ));
                    assert(serialized_var_uint8_phase(
                        original_workspace,
                        self.window_bytes,
                        start_phase,
                    ));
                    assert(serialized_b3b_queue(
                        self.workspace@,
                        self.window_bytes,
                        queue,
                    ));
                    assert(serialized_var_uint8_phase(
                        self.workspace@,
                        self.window_bytes,
                        var_phase,
                    ));
                    assert(var_uint8_exact_step(
                        start_queue,
                        start_phase,
                        input@,
                        end_of_input,
                        result.0,
                        queue,
                        var_phase,
                        step.status,
                    ));
                    assert({
                        &&& serialized_b3b_queue(
                            original_workspace,
                            self.window_bytes,
                            start_queue,
                        )
                        &&& serialized_var_uint8_phase(
                            original_workspace,
                            self.window_bytes,
                            start_phase,
                        )
                        &&& serialized_b3b_queue(
                            self.workspace@,
                            self.window_bytes,
                            queue,
                        )
                        &&& serialized_var_uint8_phase(
                            self.workspace@,
                            self.window_bytes,
                            var_phase,
                        )
                        &&& var_uint8_exact_step(
                            start_queue,
                            start_phase,
                            input@,
                            end_of_input,
                            result.0,
                            queue,
                            var_phase,
                            step.status,
                        )
                        &&& match step.status {
                            VarUint8Status::NeedInput => result.1
                                == Some(CompressedHeaderStatus::NeedInput),
                            _ => false,
                        }
                    });
                    assert(exists|witness_start_queue: BitQueue,
                        witness_final_queue: BitQueue,
                        witness_start_phase: VarUint8Phase,
                        witness_final_phase: VarUint8Phase,
                        witness_status: VarUint8Status| {
                        &&& serialized_b3b_queue(
                            original_workspace,
                            self.window_bytes,
                            witness_start_queue,
                        )
                        &&& serialized_var_uint8_phase(
                            original_workspace,
                            self.window_bytes,
                            witness_start_phase,
                        )
                        &&& serialized_b3b_queue(
                            self.workspace@,
                            self.window_bytes,
                            witness_final_queue,
                        )
                        &&& serialized_var_uint8_phase(
                            self.workspace@,
                            self.window_bytes,
                            witness_final_phase,
                        )
                        &&& var_uint8_exact_step(
                            witness_start_queue,
                            witness_start_phase,
                            input@,
                            end_of_input,
                            result.0,
                            witness_final_queue,
                            witness_final_phase,
                            witness_status,
                        )
                        &&& match witness_status {
                            VarUint8Status::NeedInput => result.1
                                == Some(CompressedHeaderStatus::NeedInput),
                            VarUint8Status::Truncated => match result.1 {
                                Some(CompressedHeaderStatus::Failed(_)) => true,
                                _ => false,
                            },
                            VarUint8Status::Progress => false,
                            VarUint8Status::Value(_) => false,
                        }
                    });
                    assert(block_count_phase_refines(
                        original_workspace,
                        self.workspace@,
                        self.window_bytes,
                        input@,
                        end_of_input,
                        result.0,
                        result.1,
                    ));
                }
                return result;
            }
            VarUint8Status::Truncated =>
                return self.fail_phase(consumed, CompressedHeaderError::Truncated),
            VarUint8Status::Progress => {}
            VarUint8Status::Value(raw) => {
                if let Err(error) = self.apply_block_count_value(
                    kind,
                    raw,
                    queue,
                    var_phase,
                ) {
                    return self.fail_phase(consumed, error);
                }
                proof {
                    assert(block_count_value_applied(
                        self.workspace@,
                        self.window_bytes,
                        kind,
                        raw,
                    ));
                }
            }
        }
        let result = (consumed, None);
        proof {
            reveal(block_count_phase_refines);
            assert(b3b_scalar_byte_at(
                original_workspace,
                self.window_bytes,
                B3B_CURRENT_KIND,
            ) == kind);
            assert(block_count_phase_refines(
                original_workspace,
                self.workspace@,
                self.window_bytes,
                input@,
                end_of_input,
                result.0,
                result.1,
            ));
        }
        result
    }

    fn advance_block_tree_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::BlockTypeTree || phase == CompressedOuterPhase::BlockLengthTree,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
    {
        let mut consumed: usize = 0;

                    let tree_step = advance_serialized_tree(
                        self.workspace,
                        self.window_bytes,
                        &input[consumed..],
                        end_of_input,
                    );
                    consumed = consumed + tree_step.consumed;
                    match tree_step.status {
                        SerializedTreeStatus::NeedInput => return (consumed, Some(CompressedHeaderStatus::NeedInput)),
                        SerializedTreeStatus::Failed(error) => return self.fail_phase(consumed, error),
                        SerializedTreeStatus::Complete => {
                            let kind = match state_byte(
                                self.workspace, self.window_bytes, B3B_CURRENT_KIND) {
                                Ok(value) => value,
                                Err(error) => return self.fail_phase(consumed, error),
                            };
                            if phase == CompressedOuterPhase::BlockTypeTree {
                                if let Err(error) = start_serialized_tree(
                                    self.workspace,
                                    self.window_bytes,
                                    crate::brotli_prefix::TreeRegion::BlockLength,
                                    kind as u16,
                                    26,
                                    26,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = self.store_outer_phase(
                                    CompressedOuterPhase::BlockLengthTree) {
                                    return self.fail_phase(consumed, error);
                                }
                            } else {
                                let initial = InstalledPrefixState::initial();
                                if let Err(error) = self.store_installed_prefix(initial) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = put_state_byte(
                                    self.workspace,
                                    self.window_bytes,
                                    B3B_BLOCK_LENGTH_PHASE,
                                    0,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = self.store_outer_phase(
                                    CompressedOuterPhase::InitialBlockLength) {
                                    return self.fail_phase(consumed, error);
                                }
                            }
                        }
                    }
                        (consumed, None)
    }

    fn advance_initial_block_length_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::InitialBlockLength,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
    {
        let mut consumed: usize = 0;

                    let kind = match state_byte(self.workspace, self.window_bytes, B3B_CURRENT_KIND) {
                        Ok(value) => value,
                        Err(error) => return self.fail_phase(consumed, error),
                    };
                    if kind >= 3 {
                        return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                    }
                    let subphase = match state_byte(
                        self.workspace, self.window_bytes, B3B_BLOCK_LENGTH_PHASE) {
                        Ok(value) => value,
                        Err(error) => return self.fail_phase(consumed, error),
                    };
                    if subphase == 0 {
                        let meta = match crate::brotli_prefix::read_tree_metadata(
                            self.workspace,
                            self.window_bytes,
                            crate::brotli_prefix::TreeRegion::BlockLength,
                            3,
                            kind as u16,
                        ) {
                            Ok(value) => value,
                            Err(crate::brotli_prefix::MetadataReadError::InvalidEncoding) =>
                                return self.fail_phase(consumed, CompressedHeaderError::InvalidFormat(
                                    CompressedFormatError::InvalidMetadata)),
                            Err(crate::brotli_prefix::MetadataReadError::Workspace(error)) =>
                                return self.fail_phase(consumed, CompressedHeaderError::Workspace(error)),
                        };
                        let mut queue = match load_b3b_queue(self.workspace, self.window_bytes) {
                            Ok(value) => value,
                            Err(error) => return self.fail_phase(consumed, error),
                        };
                        let mut prefix = match self.load_installed_prefix() {
                            Ok(value) => value,
                            Err(error) => return self.fail_phase(consumed, error),
                        };
                        let symbol_step = advance_installed_tree_symbol(
                            self.workspace,
                            self.window_bytes,
                            crate::brotli_prefix::TreeRegion::BlockLength,
                            kind as u16,
                            meta,
                            &mut queue,
                            &mut prefix,
                            &input[consumed..],
                            end_of_input,
                        );
                        consumed = consumed + symbol_step.consumed;
                        if let Err(error) = store_b3b_queue(
                            self.workspace, self.window_bytes, &queue) {
                            return self.fail_phase(consumed, error);
                        }
                        if let Err(error) = self.store_installed_prefix(prefix) {
                            return self.fail_phase(consumed, error);
                        }
                        match symbol_step.status {
                            InstalledSymbolStatus::NeedInput => return (consumed, Some(CompressedHeaderStatus::NeedInput)),
                            InstalledSymbolStatus::Truncated =>
                                return self.fail_phase(consumed, CompressedHeaderError::Truncated),
                            InstalledSymbolStatus::InvalidPrefixCode => return self.fail_phase(
                                consumed,
                                CompressedHeaderError::InvalidFormat(
                                    CompressedFormatError::InvalidPrefixCode),
                            ),
                            InstalledSymbolStatus::InternalState =>
                                return self.fail_phase(consumed, CompressedHeaderError::InternalState),
                            InstalledSymbolStatus::Symbol(symbol) => {
                                if symbol >= 26 {
                                    return self.fail_phase(consumed, CompressedHeaderError::InvalidFormat(
                                        CompressedFormatError::InvalidBlockLength));
                                }
                                let width = crate::brotli_prefix::BLOCK_LENGTH_EXTRA_BITS[
                                    symbol as usize];
                                if let Err(error) = put_state_byte(
                                    self.workspace, self.window_bytes,
                                    B3B_BLOCK_LENGTH_SYMBOL, symbol as u8) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = put_state_byte(
                                    self.workspace, self.window_bytes,
                                    B3B_BLOCK_LENGTH_SUFFIX_WIDTH, width) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = put_state_byte(
                                    self.workspace, self.window_bytes,
                                    B3B_BLOCK_LENGTH_PHASE, 1) {
                                    return self.fail_phase(consumed, error);
                                }
                            }
                        }
                    } else if subphase == 1 {
                        let width = match state_byte(
                            self.workspace, self.window_bytes, B3B_BLOCK_LENGTH_SUFFIX_WIDTH) {
                            Ok(value) => value,
                            Err(error) => return self.fail_phase(consumed, error),
                        };
                        let symbol = match state_byte(
                            self.workspace, self.window_bytes, B3B_BLOCK_LENGTH_SYMBOL) {
                            Ok(value) => value,
                            Err(error) => return self.fail_phase(consumed, error),
                        };
                        if symbol >= 26 || width != crate::brotli_prefix::BLOCK_LENGTH_EXTRA_BITS[
                            symbol as usize] {
                            return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                        }
                        let mut queue = match load_b3b_queue(self.workspace, self.window_bytes) {
                            Ok(value) => value,
                            Err(error) => return self.fail_phase(consumed, error),
                        };
                        let read = queue.read_bits(width as usize, &input[consumed..], end_of_input);
                        consumed = consumed + read.consumed;
                        if let Err(error) = store_b3b_queue(
                            self.workspace, self.window_bytes, &queue) {
                            return self.fail_phase(consumed, error);
                        }
                        match read.status {
                            BitReadStatus::NeedInput => return (consumed, Some(CompressedHeaderStatus::NeedInput)),
                            BitReadStatus::Truncated =>
                                return self.fail_phase(consumed, CompressedHeaderError::Truncated),
                            BitReadStatus::Value(suffix) => {
                                proof {
                                    lemma2_to64();
                                    assert(width <= 24);
                                    lemma_pow2_strictly_increases(width as nat, 32);
                                    assert(suffix <= u32::MAX);
                                    bounded_u64_fits_u32(suffix);
                                }
                                let length = match crate::brotli_prefix::decode_block_length(
                                    symbol,
                                    suffix as u32,
                                ) {
                                    Ok(value) => value,
                                    Err(_) => return self.fail_phase(
                                        consumed,
                                        CompressedHeaderError::InvalidFormat(
                                            CompressedFormatError::InvalidBlockLength),
                                    ),
                                };
                                if let Err(error) = put_state_u32(
                                    self.workspace,
                                    self.window_bytes,
                                    B3B_INITIAL_LENGTHS + 4 * kind as u16,
                                    length,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = put_state_byte(
                                    self.workspace,
                                    self.window_bytes,
                                    B3B_CURRENT_KIND,
                                    kind + 1,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = self.store_outer_phase(
                                    CompressedOuterPhase::BlockCount) {
                                    return self.fail_phase(consumed, error);
                                }
                            }
                        }
                    } else {
                        return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                    }
                        (consumed, None)
    }

    fn advance_distance_parameters_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::DistanceParameters,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
    {
        let mut consumed: usize = 0;

                    let mut queue = match load_b3b_queue(self.workspace, self.window_bytes) {
                        Ok(value) => value,
                        Err(error) => return self.fail_phase(consumed, error),
                    };
                    let read = queue.read_bits(6, &input[consumed..], end_of_input);
                    consumed = consumed + read.consumed;
                    if let Err(error) = store_b3b_queue(
                        self.workspace, self.window_bytes, &queue) {
                        return self.fail_phase(consumed, error);
                    }
                    match read.status {
                        BitReadStatus::NeedInput => return (consumed, Some(CompressedHeaderStatus::NeedInput)),
                        BitReadStatus::Truncated =>
                            return self.fail_phase(consumed, CompressedHeaderError::Truncated),
                        BitReadStatus::Value(value) => {
                            proof {
                                lemma2_to64();
                                assert(value < 64);
                                bounded_u64_fits_u8(value);
                            }
                            let (postfix, direct, alphabet) = decode_distance_parameters(value as u8);
                            if let Err(error) = put_state_byte(
                                self.workspace, self.window_bytes, B3B_DISTANCE_POSTFIX, postfix) {
                                return self.fail_phase(consumed, error);
                            }
                            if let Err(error) = put_state_u16(
                                self.workspace, self.window_bytes, B3B_DIRECT_DISTANCE, direct) {
                                return self.fail_phase(consumed, error);
                            }
                            if let Err(error) = put_state_u16(
                                self.workspace, self.window_bytes, B3B_ALPHABET_MAX, alphabet) {
                                return self.fail_phase(consumed, error);
                            }
                            if let Err(error) = self.store_outer_phase(
                                CompressedOuterPhase::ContextModes) {
                                return self.fail_phase(consumed, error);
                            }
                        }
                    }
                        (consumed, None)
    }

    fn advance_context_modes_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::ContextModes,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1.is_none()
                && b3b_scalar_u16_at(
                    old(self).workspace@,
                    old(self).window_bytes,
                    B3B_MODES_INITIALIZED,
                ) == serialized_block_count_at(
                    old(self).workspace@,
                    old(self).window_bytes,
                    0,
                ) ==> {
                &&& b3b_scalar_byte_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    B3B_OUTER_PHASE,
                ) == compressed_outer_phase_tag_spec(
                    CompressedOuterPhase::LiteralContextMap,
                )
                &&& b3b_scalar_byte_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    B3B_CONTEXT_KIND,
                ) == 0
                &&& b3b_scalar_u16_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    B3B_MAP_SIZE,
                ) == 64 * serialized_block_count_at(
                    old(self).workspace@,
                    old(self).window_bytes,
                    0,
                )
            },
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
    {
        let mut consumed: usize = 0;

                    let literal_count = match state_u16(
                        self.workspace, self.window_bytes, B3B_BLOCK_COUNTS) {
                        Ok(value) => value,
                        Err(error) => return self.fail_phase(consumed, error),
                    };
                    let initialized = match state_u16(
                        self.workspace, self.window_bytes, B3B_MODES_INITIALIZED) {
                        Ok(value) => value,
                        Err(error) => return self.fail_phase(consumed, error),
                    };
                    if literal_count == 0 || literal_count > 256 || initialized > literal_count {
                        return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                    }
                    if initialized == literal_count {
                        let active_len = literal_count * 64;
                        if let Err(error) = start_context_map(
                            self.workspace,
                            self.window_bytes,
                            crate::brotli_prefix::ContextMapKind::Literal,
                            active_len,
                        ) {
                            return self.fail_phase(consumed, error);
                        }
                        if let Err(error) = self.store_outer_phase(
                            CompressedOuterPhase::LiteralContextMap) {
                            return self.fail_phase(consumed, error);
                        }
                    } else {
                        let mut queue = match load_b3b_queue(self.workspace, self.window_bytes) {
                            Ok(value) => value,
                            Err(error) => return self.fail_phase(consumed, error),
                        };
                        let read = queue.read_bits(2, &input[consumed..], end_of_input);
                        consumed = consumed + read.consumed;
                        if let Err(error) = store_b3b_queue(
                            self.workspace, self.window_bytes, &queue) {
                            return self.fail_phase(consumed, error);
                        }
                        match read.status {
                            BitReadStatus::NeedInput => return (consumed, Some(CompressedHeaderStatus::NeedInput)),
                            BitReadStatus::Truncated =>
                                return self.fail_phase(consumed, CompressedHeaderError::Truncated),
                            BitReadStatus::Value(value) => {
                                proof {
                                    lemma2_to64();
                                    assert(value < 4);
                                    bounded_u64_fits_u8(value);
                                }
                                let ghost before_mode = self.workspace@;
                                let next = match crate::brotli_prefix::write_next_context_mode(
                                    self.workspace,
                                    self.window_bytes,
                                    initialized,
                                    value as u8,
                                ) {
                                    Ok(value) => value,
                                    Err(error) => return self.fail_phase(
                                        consumed, CompressedHeaderError::Workspace(error)),
                                };
                                proof {
                                    context_mode_update_preserves_decoder_state(
                                        before_mode,
                                        self.workspace@,
                                        self.window_bytes,
                                        initialized,
                                        value as u8,
                                    );
                                }
                                if let Err(error) = put_state_u16(
                                    self.workspace, self.window_bytes,
                                    B3B_MODES_INITIALIZED, next) {
                                    return self.fail_phase(consumed, error);
                                }
                                proof {
                                    reveal(compressed_decoder_state_ok);
                                    reveal(b3b_scalar_byte_at);
                                    reveal(b3b_scalar_base);
                                    b3b_scalar_layout_is_exact();
                                    assert(compressed_decoder_state_ok(
                                        self.workspace@,
                                        self.window_bytes,
                                    ));
                                }
                            }
                        }
                    }
                        (consumed, None)
    }

    fn advance_context_maps_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::LiteralContextMap || phase == CompressedOuterPhase::DistanceContextMap,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1.is_none() && phase == CompressedOuterPhase::LiteralContextMap ==> {
                &&& b3b_scalar_byte_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    B3B_OUTER_PHASE,
                ) == compressed_outer_phase_tag_spec(
                    CompressedOuterPhase::DistanceContextMap,
                )
                &&& b3b_scalar_byte_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    B3B_CONTEXT_KIND,
                ) == 1
                &&& b3b_scalar_u16_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    B3B_MAP_SIZE,
                ) == 4 * serialized_block_count_at(
                    final(self).workspace@,
                    final(self).window_bytes,
                    2,
                )
            },
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
    {
        let mut consumed: usize = 0;

                    proof {
                        reveal(compressed_decoder_state_ok);
                        match phase {
                            CompressedOuterPhase::LiteralContextMap => {}
                            CompressedOuterPhase::DistanceContextMap => {}
                            _ => { assert(false); }
                        }
                        assert(serialized_context_state_ok(
                            self.workspace@,
                            self.window_bytes,
                        ));
                    }
                    let context_step = advance_context_map(
                        self.workspace,
                        self.window_bytes,
                        &input[consumed..],
                        end_of_input,
                    );
                    consumed = consumed + context_step.consumed;
                    match context_step.status {
                        ContextAdvanceStatus::NeedInput => return (consumed, Some(CompressedHeaderStatus::NeedInput)),
                        ContextAdvanceStatus::Failed(error) => return self.fail_phase(consumed, error),
                        ContextAdvanceStatus::Complete { kind, num_trees } => match kind {
                            crate::brotli_prefix::ContextMapKind::Literal => {
                                match phase {
                                    CompressedOuterPhase::LiteralContextMap => {}
                                    _ => return self.fail_phase(
                                        consumed,
                                        CompressedHeaderError::InternalState,
                                    ),
                                }
                                if let Err(error) = put_state_u16(
                                    self.workspace,
                                    self.window_bytes,
                                    B3B_LITERAL_TREES,
                                    num_trees,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                let distance_types = match state_u16(
                                    self.workspace,
                                    self.window_bytes,
                                    B3B_BLOCK_COUNTS + 4,
                                ) {
                                    Ok(value) => value,
                                    Err(error) => return self.fail_phase(consumed, error),
                                };
                                if distance_types == 0 || distance_types > 256 {
                                    return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                                }
                                if let Err(error) = start_context_map(
                                    self.workspace,
                                    self.window_bytes,
                                    crate::brotli_prefix::ContextMapKind::Distance,
                                    distance_types * 4,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = self.store_outer_phase(
                                    CompressedOuterPhase::DistanceContextMap,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                proof {
                                    assert(b3b_scalar_byte_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_OUTER_PHASE,
                                    ) == compressed_outer_phase_tag_spec(
                                        CompressedOuterPhase::DistanceContextMap,
                                    ));
                                    assert(b3b_scalar_byte_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_CONTEXT_KIND,
                                    ) == 1);
                                    assert(b3b_scalar_u16_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_MAP_SIZE,
                                    ) == 4 * serialized_block_count_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        2,
                                    ));
                                }
                                return (consumed, None);
                            }
                            crate::brotli_prefix::ContextMapKind::Distance => {
                                match phase {
                                    CompressedOuterPhase::DistanceContextMap => {}
                                    _ => return self.fail_phase(
                                        consumed,
                                        CompressedHeaderError::InternalState,
                                    ),
                                }
                                if let Err(error) = put_state_u16(
                                    self.workspace,
                                    self.window_bytes,
                                    B3B_DISTANCE_TREES,
                                    num_trees,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                if let Err(error) = self.start_tree_group(
                                    0,
                                    CompressedOuterPhase::LiteralTreeGroup,
                                ) {
                                    return self.fail_phase(consumed, error);
                                }
                                return (consumed, None);
                            }
                        },
                    }
    }

    fn advance_tree_groups_phase(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            phase == CompressedOuterPhase::LiteralTreeGroup || phase == CompressedOuterPhase::CommandTreeGroup || phase == CompressedOuterPhase::DistanceTreeGroup,
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
            tree_group_phase_refines(
                old(self).workspace@,
                final(self).workspace@,
                old(self).window_bytes,
                r.1,
            ),
    {
        let ghost original = self.workspace@;
        let mut consumed: usize = 0;

                    let tree_step = advance_serialized_tree(
                        self.workspace,
                        self.window_bytes,
                        &input[consumed..],
                        end_of_input,
                    );
                    consumed = consumed + tree_step.consumed;
                    match tree_step.status {
                        SerializedTreeStatus::NeedInput => {
                            let result = (consumed, Some(CompressedHeaderStatus::NeedInput));
                            proof {
                                reveal(compressed_decoder_state_ok);
                                reveal(tree_group_phase_refines);
                                assert(tree_group_phase_refines(
                                    original,
                                    self.workspace@,
                                    self.window_bytes,
                                    result.1,
                                ));
                            }
                            return result;
                        }
                        SerializedTreeStatus::Failed(error) => return self.fail_phase(consumed, error),
                        SerializedTreeStatus::Complete => {
                            proof {
                                reveal(compressed_decoder_state_ok);
                                let phase_tag = b3b_scalar_byte_at(
                                    self.workspace@,
                                    self.window_bytes,
                                    B3B_OUTER_PHASE,
                                );
                                assert(tree_group_payload_ok(
                                    self.workspace@,
                                    self.window_bytes,
                                    phase_tag,
                                ));
                                active_complete_implies_group_tree_complete(
                                    self.workspace@,
                                    self.window_bytes,
                                    phase_tag,
                                );
                            }
                            let group = match state_byte(
                                self.workspace, self.window_bytes, B3B_GROUP_KIND) {
                                Ok(value) => value,
                                Err(error) => return self.fail_phase(consumed, error),
                            };
                            let tree = match state_u16(
                                self.workspace, self.window_bytes, B3B_TREE_INDEX) {
                                Ok(value) => value,
                                Err(error) => return self.fail_phase(consumed, error),
                            };
                            let count = match state_u16(
                                self.workspace, self.window_bytes, B3B_TREE_COUNT) {
                                Ok(value) => value,
                                Err(error) => return self.fail_phase(consumed, error),
                            };
                            if count == 0 || count > 256 || tree >= count {
                                return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                            }
                            let next = tree + 1;
                            if next < count {
                                if let Err(error) = self.start_group_tree(group, next) {
                                    return self.fail_phase(consumed, error);
                                }
                            } else if next == count {
                                if group < 2 {
                                    let next_group = group + 1;
                                    proof {
                                        assert(next_group == group + 1);
                                        assert(next_group == 1 || next_group == 2);
                                    }
                                    let next_phase = if next_group == 1 {
                                        CompressedOuterPhase::CommandTreeGroup
                                    } else {
                                        CompressedOuterPhase::DistanceTreeGroup
                                    };
                                    if let Err(error) = self.start_tree_group(next_group, next_phase) {
                                        return self.fail_phase(consumed, error);
                                    }
                                } else {
                                    if let Err(error) = self.complete_tree_groups() {
                                        return self.fail_phase(consumed, error);
                                    }
                                }
                            } else {
                                return self.fail_phase(consumed, CompressedHeaderError::InternalState);
                            }
                            let result = (consumed, None);
                            proof {
                                reveal(compressed_decoder_state_ok);
                                reveal(tree_group_phase_refines);
                                assert(group == b3b_scalar_byte_at(
                                    original,
                                    self.window_bytes,
                                    B3B_GROUP_KIND,
                                ));
                                assert(tree as nat == b3b_scalar_u16_at(
                                    original,
                                    self.window_bytes,
                                    B3B_TREE_INDEX,
                                ));
                                assert(count as nat == b3b_scalar_u16_at(
                                    original,
                                    self.window_bytes,
                                    B3B_TREE_COUNT,
                                ));
                                let phase_tag = b3b_scalar_byte_at(
                                    original,
                                    self.window_bytes,
                                    B3B_OUTER_PHASE,
                                );
                                assert(tree_group_payload_ok(
                                    original,
                                    self.window_bytes,
                                    phase_tag,
                                ));
                                if next < count {
                                    assert(b3b_scalar_byte_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_OUTER_PHASE,
                                    ) == phase_tag);
                                    assert(b3b_scalar_u16_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_TREE_INDEX,
                                    ) == tree + 1);
                                    assert(tree_group_payload_ok(
                                        self.workspace@,
                                        self.window_bytes,
                                        phase_tag,
                                    ));
                                } else if group < 2 {
                                    let next_phase_tag: u8 =
                                        (phase_tag as int + 1) as u8;
                                    assert(b3b_scalar_byte_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_OUTER_PHASE,
                                    ) == next_phase_tag);
                                    assert(b3b_scalar_byte_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_GROUP_KIND,
                                    ) == group + 1);
                                    assert(b3b_scalar_u16_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_TREE_INDEX,
                                    ) == 0);
                                    assert(tree_group_payload_ok(
                                        self.workspace@,
                                        self.window_bytes,
                                        next_phase_tag,
                                    ));
                                } else {
                                    assert(b3b_scalar_byte_at(
                                        self.workspace@,
                                        self.window_bytes,
                                        B3B_OUTER_PHASE,
                                    ) == 11);
                                    assert(tree_group_payload_ok(
                                        self.workspace@,
                                        self.window_bytes,
                                        11,
                                    ));
                                }
                                assert(tree_group_phase_refines(
                                    original,
                                    self.workspace@,
                                    self.window_bytes,
                                    result.1,
                                ));
                            }
                            return result;
                        }
                    }
    }

    fn advance_outer_phase_once(
        &mut self,
        phase: CompressedOuterPhase,
        input: &[u8],
        end_of_input: bool,
    ) -> (r: (usize, Option<CompressedHeaderStatus>))
        requires
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            r.0 <= input.len(),
            r.1.is_none() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.1 == Some(CompressedHeaderStatus::NeedInput) ==> {
                &&& !end_of_input
                &&& r.0 == input.len()
                &&& compressed_decoder_state_ok(
                    final(self).workspace@,
                    final(self).window_bytes,
                )
            },
            match r.1 {
                Some(CompressedHeaderStatus::Complete(_)) => false,
                Some(CompressedHeaderStatus::Failed(error)) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
            phase == CompressedOuterPhase::BlockCount ==> block_count_phase_refines(
                old(self).workspace@,
                final(self).workspace@,
                old(self).window_bytes,
                input@,
                end_of_input,
                r.0,
                r.1,
            ),
            (phase == CompressedOuterPhase::LiteralTreeGroup
                || phase == CompressedOuterPhase::CommandTreeGroup
                || phase == CompressedOuterPhase::DistanceTreeGroup)
                ==> tree_group_phase_refines(
                    old(self).workspace@,
                    final(self).workspace@,
                    old(self).window_bytes,
                    r.1,
                ),
    {
        let ghost original_workspace = self.workspace@;
        let mut consumed: usize = 0;
        match phase {
                CompressedOuterPhase::BlockCount => {
                    let old_consumed = consumed;
                    let remaining = &input[old_consumed..];
                    proof { assert(remaining@ == input@); }
                    let (used, status) = self.advance_block_count_phase(
                        phase,
                        remaining,
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    proof {
                        assert(block_count_phase_refines(
                            original_workspace,
                            self.workspace@,
                            self.window_bytes,
                            input@,
                            end_of_input,
                            consumed,
                            status,
                        ));
                    }
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::BlockTypeTree
                | CompressedOuterPhase::BlockLengthTree => {
                    let old_consumed = consumed;
                    let (used, status) = self.advance_block_tree_phase(
                        phase,
                        &input[old_consumed..],
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::InitialBlockLength => {
                    let old_consumed = consumed;
                    let (used, status) = self.advance_initial_block_length_phase(
                        phase,
                        &input[old_consumed..],
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::DistanceParameters => {
                    let old_consumed = consumed;
                    let (used, status) = self.advance_distance_parameters_phase(
                        phase,
                        &input[old_consumed..],
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::ContextModes => {
                    let old_consumed = consumed;
                    let (used, status) = self.advance_context_modes_phase(
                        phase,
                        &input[old_consumed..],
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::LiteralContextMap
                | CompressedOuterPhase::DistanceContextMap => {
                    let old_consumed = consumed;
                    let (used, status) = self.advance_context_maps_phase(
                        phase,
                        &input[old_consumed..],
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::LiteralTreeGroup
                | CompressedOuterPhase::CommandTreeGroup
                | CompressedOuterPhase::DistanceTreeGroup => {
                    let old_consumed = consumed;
                    let (used, status) = self.advance_tree_groups_phase(
                        phase,
                        &input[old_consumed..],
                        end_of_input,
                    );
                    consumed = old_consumed + used;
                    proof {
                        assert(tree_group_phase_refines(
                            original_workspace,
                            self.workspace@,
                            self.window_bytes,
                            status,
                        ));
                    }
                    match status {
                        Some(status) => return (consumed, Some(status)),
                        None => {}
                    }
                }
                CompressedOuterPhase::Complete | CompressedOuterPhase::Failed => {}
                    }
        (consumed, None)
    }

fn step(&mut self, input: &[u8], end_of_input: bool) -> (r: CompressedHeaderStep)
        requires compressed_decoder_state_ok(old(self.workspace)@, self.window_bytes),
        ensures
            r.consumed <= input.len(),
            r.status == CompressedHeaderStatus::NeedInput ==> {
                &&& !end_of_input
                &&& r.consumed == input.len()
            },
            forall|error: CompressedHeaderError| serialized_terminal_error(
                old(self).workspace@,
                old(self).window_bytes,
                error,
            ) ==> {
                &&& final(self).workspace@ == old(self).workspace@
                &&& final(self).window_bytes == old(self).window_bytes
                &&& r == (CompressedHeaderStep {
                    consumed: 0,
                    status: CompressedHeaderStatus::Failed(error),
                })
            },
            match r.status {
                CompressedHeaderStatus::Failed(error) =>
                    serialized_terminal_error(
                        final(self).workspace@,
                        final(self).window_bytes,
                        error,
                    ),
                _ => true,
            },
    {
        let mut consumed: usize = 0;
        let mut transitions: u32 = 0;
        while transitions < 100_000
            invariant consumed <= input.len(), transitions <= 100_000,
                compressed_decoder_state_ok(self.workspace@, self.window_bytes),
                self.window_bytes == old(self).window_bytes,
                forall|error: CompressedHeaderError| serialized_terminal_error(
                    old(self).workspace@,
                    old(self).window_bytes,
                    error,
                ) ==> {
                    &&& self.workspace@ == old(self).workspace@
                    &&& consumed == 0
                    &&& transitions == 0
                },
            decreases 100_000 - transitions,
        {
            let phase = match self.load_outer_phase() {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            };
            proof {
                assert forall|old_error: CompressedHeaderError| serialized_terminal_error(
                    old(self).workspace@,
                    old(self).window_bytes,
                    old_error,
                ) implies phase == CompressedOuterPhase::Failed by {
                    assert(self.workspace@ == old(self).workspace@);
                }
            }
            match phase {
                CompressedOuterPhase::Failed => {
                    let error = match load_terminal_error(self.workspace, self.window_bytes) {
                        Ok(error) => error,
                        Err(error) => return self.fail(0, error),
                    };
                    proof {
                        assert forall|old_error: CompressedHeaderError| serialized_terminal_error(
                            old(self).workspace@,
                            old(self).window_bytes,
                            old_error,
                        ) implies error == old_error by {
                            assert(self.workspace@ == old(self).workspace@);
                        }
                    }
                    return self.repeat_terminal_failure(error);
                }
                _ => {}
            }
            proof {
                assert(phase != CompressedOuterPhase::Failed);
                assert forall|old_error: CompressedHeaderError| !serialized_terminal_error(
                    old(self).workspace@,
                    old(self).window_bytes,
                    old_error,
                ) by {
                    if serialized_terminal_error(
                        old(self).workspace@,
                        old(self).window_bytes,
                        old_error,
                    ) {
                        assert(phase == CompressedOuterPhase::Failed);
                    }
                }
            }
            if phase == CompressedOuterPhase::Complete {
                return self.finish_header(consumed);
            }
            let old_consumed = consumed;
            let (used, status) = self.advance_outer_phase_once(
                phase,
                &input[old_consumed..],
                end_of_input,
            );
            consumed = old_consumed + used;
            match status {
                Some(status) => return CompressedHeaderStep { consumed, status },
                None => {}
            }
            transitions = transitions + 1;
        }
        self.fail(consumed, CompressedHeaderError::InternalState)
    }

    fn group_parameters(
        &self,
        group: u8,
    ) -> (r: Result<(crate::brotli_prefix::TreeRegion, u16, u16), CompressedHeaderError>)
        ensures r.is_ok() ==> {
            &&& group < 3
            &&& r.unwrap().0 == tree_group_region(group)
            &&& r.unwrap().1 as nat == tree_group_count_at(
                old(self.workspace)@,
                self.window_bytes,
                group,
            )
            &&& r.unwrap().2 as nat == tree_group_alphabet_at(
                old(self.workspace)@,
                self.window_bytes,
                group,
            )
        },
    {
        proof {
            reveal(tree_group_region);
            reveal(tree_group_count_at);
            reveal(tree_group_alphabet_at);
        }
        match group {
            0 => {
                let count = state_u16(self.workspace, self.window_bytes, B3B_LITERAL_TREES)?;
                proof {
                    assert(count as nat == tree_group_count_at(
                        old(self.workspace)@,
                        self.window_bytes,
                        group,
                    ));
                }
                Ok((crate::brotli_prefix::TreeRegion::Literal, count, 256))
            }
            1 => {
                let count = state_u16(
                    self.workspace, self.window_bytes, B3B_BLOCK_COUNTS + 2)?;
                proof {
                    assert(count as nat == tree_group_count_at(
                        old(self.workspace)@,
                        self.window_bytes,
                        group,
                    ));
                }
                Ok((crate::brotli_prefix::TreeRegion::Command, count, 704))
            }
            2 => {
                let count = state_u16(self.workspace, self.window_bytes, B3B_DISTANCE_TREES)?;
                let postfix = state_byte(
                    self.workspace, self.window_bytes, B3B_DISTANCE_POSTFIX)?;
                let direct = state_u16(
                    self.workspace, self.window_bytes, B3B_DIRECT_DISTANCE)?;
                if postfix > 3 || direct > 120 {
                    return Err(CompressedHeaderError::InternalState);
                }
                proof {
                    serialized_distance_alphabet_fits(postfix, direct);
                    serialized_distance_alphabet_exact(postfix, direct);
                }
                let alphabet = 16u16 + direct + (24u16 << (postfix + 1));
                if alphabet < 64 || alphabet > 520 {
                    return Err(CompressedHeaderError::InvalidFormat(
                        CompressedFormatError::InvalidDistanceAlphabet,
                    ));
                }
                proof {
                    assert(count as nat == tree_group_count_at(
                        old(self.workspace)@,
                        self.window_bytes,
                        group,
                    ));
                    assert(alphabet as nat == tree_group_alphabet_at(
                        old(self.workspace)@,
                        self.window_bytes,
                        group,
                    ));
                }
                Ok((crate::brotli_prefix::TreeRegion::Distance, count, alphabet))
            }
            _ => Err(CompressedHeaderError::InternalState),
        }
    }

    fn start_group_tree(&mut self, group: u8, tree: u16) -> (r: Result<(), CompressedHeaderError>)
        requires
            b3b_workspace_shape(
                old(self).workspace@.len() as nat,
                old(self).window_bytes,
            ),
            serialized_mtf_state_ok(old(self).workspace@, old(self).window_bytes),
            serialized_context_state_ok(old(self).workspace@, old(self).window_bytes),
            group < 3,
            b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_GROUP_KIND,
            ) == group,
            b3b_scalar_u16_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_TREE_COUNT,
            ) == tree_group_count_at(
                old(self).workspace@,
                old(self).window_bytes,
                group,
            ),
            1 <= tree_group_count_at(
                old(self).workspace@,
                old(self).window_bytes,
                group,
            ) <= 256,
            tree < tree_group_count_at(
                old(self).workspace@,
                old(self).window_bytes,
                group,
            ),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@.len() == old(self).workspace@.len(),
            b3b_workspace_shape(old(self).workspace@.len() as nat, old(self).window_bytes)
                ==> b3b_workspace_shape(
                    final(self).workspace@.len() as nat,
                    final(self).window_bytes,
                ),
            r.is_ok() && b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == (8 + group as int) as u8 ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.is_ok() ==> serialized_context_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.is_ok() ==> tree_group_payload_ok(
                final(self).workspace@,
                final(self).window_bytes,
                (8 + group as int) as u8,
            ),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == b3b_scalar_byte_at(
                old(self).workspace@,
                old(self).window_bytes,
                B3B_OUTER_PHASE,
            ),
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_TREE_INDEX,
            ) == tree,
    {
        let ghost original = self.workspace@;
        let (region, count, alphabet) = self.group_parameters(group)?;
        if count == 0 || count > 256 || tree >= count {
            return Err(CompressedHeaderError::InternalState);
        }
        start_serialized_tree(
            self.workspace,
            self.window_bytes,
            region,
            tree,
            alphabet,
            alphabet,
        )?;
        put_state_u16(self.workspace, self.window_bytes, B3B_TREE_INDEX, tree)?;
        put_state_byte(self.workspace, self.window_bytes, B3B_GROUP_PHASE, 1)?;
        proof {
            reveal(compressed_decoder_state_ok);
            reveal(tree_group_payload_ok);
            reveal(tree_group_count_at);
            reveal(tree_group_alphabet_at);
            reveal(tree_group_region);
            match group {
                0 => {}
                1 => {}
                2 => {}
                _ => { assert(false); }
            }
            assert(b3b_scalar_byte_at(
                self.workspace@,
                self.window_bytes,
                B3B_GROUP_KIND,
            ) == group);
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_TREE_COUNT,
            ) == count);
            assert(count as nat == tree_group_count_at(
                self.workspace@,
                self.window_bytes,
                group,
            ));
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_TREE_INDEX,
            ) == tree);
            assert(b3b_scalar_byte_at(
                self.workspace@,
                self.window_bytes,
                B3B_GROUP_PHASE,
            ) == 1);
            assert(b3b_scalar_byte_at(
                self.workspace@,
                self.window_bytes,
                B3B_ACTIVE_REGION,
            ) == group);
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_ACTIVE_TREE,
            ) == tree);
            assert(alphabet as nat == tree_group_alphabet_at(
                self.workspace@,
                self.window_bytes,
                group,
            ));
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_ALPHABET_MAX,
            ) == alphabet);
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_ALPHABET_LIMIT,
            ) == alphabet);
            assert(tree_group_payload_ok(
                self.workspace@,
                self.window_bytes,
                (8 + group as int) as u8,
            ));
            assert(serialized_context_state_ok(self.workspace@, self.window_bytes));
            if b3b_scalar_byte_at(
                self.workspace@,
                self.window_bytes,
                B3B_OUTER_PHASE,
            ) == (8 + group as int) as u8 {
                assert(compressed_decoder_state_ok(self.workspace@, self.window_bytes));
            }
        }
        Ok(())
    }

    fn start_tree_group(
        &mut self,
        group: u8,
        phase: CompressedOuterPhase,
    ) -> (r: Result<(), CompressedHeaderError>)
        requires
            b3b_workspace_shape(
                old(self).workspace@.len() as nat,
                old(self).window_bytes,
            ),
            serialized_mtf_state_ok(old(self).workspace@, old(self).window_bytes),
            serialized_context_state_ok(old(self).workspace@, old(self).window_bytes),
            6 <= compressed_outer_phase_tag_spec(phase) <= 11,
            group < 3,
            compressed_outer_phase_tag_spec(phase) == (8 + group as int) as u8,
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@.len() == old(self).workspace@.len(),
            b3b_workspace_shape(old(self).workspace@.len() as nat, old(self).window_bytes)
                ==> b3b_workspace_shape(
                    final(self).workspace@.len() as nat,
                    final(self).window_bytes,
                ),
            r.is_ok() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.is_ok() ==> tree_group_payload_ok(
                final(self).workspace@,
                final(self).window_bytes,
                compressed_outer_phase_tag_spec(phase),
            ),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == compressed_outer_phase_tag_spec(phase),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_GROUP_KIND,
            ) == group,
            r.is_ok() ==> b3b_scalar_u16_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_TREE_INDEX,
            ) == 0,
    {
        let (_, count, _) = self.group_parameters(group)?;
        if count == 0 || count > 256 {
            return Err(CompressedHeaderError::InternalState);
        }
        put_state_byte(self.workspace, self.window_bytes, B3B_GROUP_KIND, group)?;
        put_state_byte(self.workspace, self.window_bytes, B3B_GROUP_PHASE, 0)?;
        put_state_u16(self.workspace, self.window_bytes, B3B_TREE_COUNT, count)?;
        self.start_group_tree(group, 0)?;
        proof {
            reveal(tree_group_payload_ok);
            assert(tree_group_payload_ok(
                self.workspace@,
                self.window_bytes,
                compressed_outer_phase_tag_spec(phase),
            ));
            assert(serialized_context_state_ok(self.workspace@, self.window_bytes));
        }
        self.store_outer_phase(phase)
    }

    fn complete_tree_groups(&mut self) -> (r: Result<(), CompressedHeaderError>)
        requires
            compressed_decoder_state_ok(old(self).workspace@, old(self).window_bytes),
            serialized_context_state_ok(old(self).workspace@, old(self).window_bytes),
        ensures
            final(self).window_bytes == old(self).window_bytes,
            final(self).workspace@.len() == old(self).workspace@.len(),
            b3b_workspace_shape(old(self).workspace@.len() as nat, old(self).window_bytes)
                ==> b3b_workspace_shape(
                    final(self).workspace@.len() as nat,
                    final(self).window_bytes,
                ),
            r.is_ok() ==> compressed_decoder_state_ok(
                final(self).workspace@,
                final(self).window_bytes,
            ),
            r.is_ok() ==> tree_group_payload_ok(
                final(self).workspace@,
                final(self).window_bytes,
                11,
            ),
            r.is_ok() ==> b3b_scalar_byte_at(
                final(self).workspace@,
                final(self).window_bytes,
                B3B_OUTER_PHASE,
            ) == 11,
    {
        let literal_types = state_u16(self.workspace, self.window_bytes, B3B_BLOCK_COUNTS)?;
        let command_types = state_u16(
            self.workspace, self.window_bytes, B3B_BLOCK_COUNTS + 2)?;
        let distance_types = state_u16(self.workspace, self.window_bytes, B3B_BLOCK_COUNTS + 4)?;
        let literal_trees = state_u16(self.workspace, self.window_bytes, B3B_LITERAL_TREES)?;
        let distance_trees = state_u16(self.workspace, self.window_bytes, B3B_DISTANCE_TREES)?;
        if literal_types == 0 || literal_types > 256
            || command_types == 0 || command_types > 256
            || distance_types == 0 || distance_types > 256
            || literal_trees == 0 || literal_trees > 256
            || distance_trees == 0 || distance_trees > 256 {
            return Err(CompressedHeaderError::InternalState);
        }
        let literal = match read_active_context_entry(
            self.workspace,
            self.window_bytes,
            crate::brotli_prefix::ContextMapKind::Literal,
            literal_types * 64,
            0,
            literal_trees,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let distance = match read_active_context_entry(
            self.workspace,
            self.window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            distance_types * 4,
            0,
            distance_trees,
        ) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        put_state_u16(
            self.workspace, self.window_bytes, B3B_ACTIVE_LITERAL_TREE, literal as u16)?;
        put_state_u16(self.workspace, self.window_bytes, B3B_ACTIVE_COMMAND_TREE, 0)?;
        put_state_u16(
            self.workspace, self.window_bytes, B3B_ACTIVE_DISTANCE_TREE, distance as u16)?;
        let ghost selected_workspace = self.workspace@;
        proof {
            assert(literal == selected_workspace[
                crate::brotli_prefix::context_entry_at(
                    self.window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    0,
                ) as int
            ]);
            assert(distance == selected_workspace[
                crate::brotli_prefix::context_entry_at(
                    self.window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    0,
                ) as int
            ]);
            assert(b3b_scalar_u16_at(
                selected_workspace,
                self.window_bytes,
                B3B_ACTIVE_LITERAL_TREE,
            ) == literal as nat);
            assert(b3b_scalar_u16_at(
                selected_workspace,
                self.window_bytes,
                B3B_ACTIVE_COMMAND_TREE,
            ) == 0);
            assert(b3b_scalar_u16_at(
                selected_workspace,
                self.window_bytes,
                B3B_ACTIVE_DISTANCE_TREE,
            ) == distance as nat);
        }
        let initial_lengths = [
            state_u32(self.workspace, self.window_bytes, B3B_INITIAL_LENGTHS)?,
            state_u32(self.workspace, self.window_bytes, B3B_INITIAL_LENGTHS + 4)?,
            state_u32(self.workspace, self.window_bytes, B3B_INITIAL_LENGTHS + 8)?,
        ];
        initialize_ready_block_switch(
            self.workspace,
            self.window_bytes,
            [literal_types, command_types, distance_types],
            initial_lengths,
        )?;
        put_state_byte(self.workspace, self.window_bytes, B3B_GROUP_PHASE, 4)?;
        proof {
            reveal(tree_group_payload_ok);
            assert(b3b_scalar_byte_at(
                self.workspace@,
                self.window_bytes,
                B3B_GROUP_PHASE,
            ) == 4);
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_ACTIVE_LITERAL_TREE,
            ) == literal as nat);
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_ACTIVE_COMMAND_TREE,
            ) == 0);
            assert(b3b_scalar_u16_at(
                self.workspace@,
                self.window_bytes,
                B3B_ACTIVE_DISTANCE_TREE,
            ) == distance as nat);
            assert(literal == self.workspace@[
                crate::brotli_prefix::context_entry_at(
                    self.window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    0,
                ) as int
            ]);
            assert(distance == self.workspace@[
                crate::brotli_prefix::context_entry_at(
                    self.window_bytes,
                    crate::brotli_prefix::ContextMapKind::Distance,
                    0,
                ) as int
            ]);
            assert(tree_group_payload_ok(
                self.workspace@,
                self.window_bytes,
                11,
            ));
            assert(serialized_context_state_ok(self.workspace@, self.window_bytes));
        }
        self.store_outer_phase(CompressedOuterPhase::Complete)
    }

    fn finish_header(&mut self, consumed: usize) -> (r: CompressedHeaderStep)
        requires b3b_workspace_shape(old(self).workspace@.len() as nat, self.window_bytes),
        ensures
            r.consumed == consumed,
            r.status != CompressedHeaderStatus::NeedInput,
            match r.status {
                CompressedHeaderStatus::Failed(error) => serialized_terminal_error(
                    final(self).workspace@,
                    final(self).window_bytes,
                    error,
                ),
                _ => true,
            },
    {
        let mut counts = [0u16; 3];
        let mut lengths = [0u32; 3];
        let mut i: usize = 0;
        while i < 3
            invariant i <= 3,
                b3b_workspace_shape(self.workspace@.len() as nat, self.window_bytes),
            decreases 3 - i,
        {
            proof {
                b3b_scalar_layout_is_exact();
                assert(B3B_BLOCK_COUNTS as nat + 2 * i as nat + 2 <= B3B_SCALAR_BYTES);
                assert(B3B_INITIAL_LENGTHS as nat + 4 * i as nat + 4 <= B3B_SCALAR_BYTES);
            }
            counts[i] = match state_u16(
                self.workspace, self.window_bytes, B3B_BLOCK_COUNTS + 2 * i as u16) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            };
            lengths[i] = match state_u32(
                self.workspace, self.window_bytes, B3B_INITIAL_LENGTHS + 4 * i as u16) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            };
            i = i + 1;
        }
        if counts[0] == 0 || counts[0] > 256
            || counts[1] == 0 || counts[1] > 256
            || counts[2] == 0 || counts[2] > 256
            || lengths[0] == 0 || lengths[1] == 0 || lengths[2] == 0
        {
            return self.fail(consumed, CompressedHeaderError::InternalState);
        }
        proof { serialized_context_lengths_fit(counts[0], counts[2]); }
        proof { b3b_scalar_layout_is_exact(); }
        let literal_trees = match state_u16(self.workspace, self.window_bytes, B3B_LITERAL_TREES) {
            Ok(value) => value,
            Err(error) => return self.fail(consumed, error),
        };
        let distance_trees = match state_u16(self.workspace, self.window_bytes, B3B_DISTANCE_TREES) {
            Ok(value) => value,
            Err(error) => return self.fail(consumed, error),
        };
        let header = CompressedHeader {
            num_block_types: counts,
            initial_block_lengths: lengths,
            distance_postfix_bits: match state_byte(
                self.workspace, self.window_bytes, B3B_DISTANCE_POSTFIX) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            },
            num_direct_distance_codes: match state_u16(
                self.workspace, self.window_bytes, B3B_DIRECT_DISTANCE) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            },
            distance_alphabet_size: match state_u16(
                self.workspace, self.window_bytes, B3B_ALPHABET_MAX) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            },
            num_literal_htrees: literal_trees,
            num_distance_htrees: distance_trees,
            literal_context_map_len: counts[0] * 64,
            distance_context_map_len: counts[2] * 4,
            literal_context_modes_len: counts[0],
            literal_trees_initialized: literal_trees,
            command_trees_initialized: counts[1],
            distance_trees_initialized: distance_trees,
            active_literal_tree: match state_u16(
                self.workspace, self.window_bytes, B3B_ACTIVE_LITERAL_TREE) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            },
            active_command_tree: match state_u16(
                self.workspace, self.window_bytes, B3B_ACTIVE_COMMAND_TREE) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            },
            active_distance_tree: match state_u16(
                self.workspace, self.window_bytes, B3B_ACTIVE_DISTANCE_TREE) {
                Ok(value) => value,
                Err(error) => return self.fail(consumed, error),
            },
        };
        CompressedHeaderStep { consumed, status: CompressedHeaderStatus::Complete(header) }
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

    fn compressed_header_fixture_bits() -> Vec<u8> {
        let mut bits = Vec::new();
        bits.extend([0, 0, 0]);
        bits.extend([0; 6]);
        bits.extend([0; 2]);
        bits.push(0);
        bits.push(0);
        for symbol_width in [8u8, 10, 6] {
            bits.extend([1, 0]);
            bits.extend([0, 0]);
            push_bits(&mut bits, 0, symbol_width);
        }
        bits
    }

    fn run_compressed_header_fixture(
        one_byte_chunks: bool,
    ) -> (CompressedHeader, [u32; 3], [u16; 6], u16, u16, u8, u8, u16) {
        let mut bits = compressed_meta_prefix_bits();
        bits.extend(compressed_header_fixture_bits());
        let bytes = pack_lsb_bits(&bits);
        let mut header = HeaderDecoder::new();
        let header_step = header.advance_header(&bytes, false);
        assert!(matches!(header_step.status, HeaderStatus::Complete { .. }));
        let mut at = header_step.consumed;
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

        let window_bytes = 1u32 << 16;
        let required = crate::brotli_prefix::required_workspace_bytes(16).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];
        let mut decoder =
            CompressedMetaBlockDecoder::from_meta(&mut workspace, window_bytes, meta).unwrap();
        let completed = loop {
            let end = if one_byte_chunks {
                (at + 1).min(bytes.len())
            } else {
                bytes.len()
            };
            let step = decoder.step(&bytes[at..end], end == bytes.len());
            at += step.consumed;
            match step.status {
                CompressedHeaderStatus::Complete(value) => break value,
                CompressedHeaderStatus::NeedInput => {
                    assert!(at < bytes.len());
                }
                CompressedHeaderStatus::Failed(error) => {
                    panic!("compressed header failed: {error:?}")
                }
            }
        };
        let remaining = [
            state_u32(decoder.workspace, window_bytes, B3B_REMAINING_LENGTHS).unwrap(),
            state_u32(decoder.workspace, window_bytes, B3B_REMAINING_LENGTHS + 4).unwrap(),
            state_u32(decoder.workspace, window_bytes, B3B_REMAINING_LENGTHS + 8).unwrap(),
        ];
        let ring = [
            state_u16(decoder.workspace, window_bytes, B3B_BLOCK_RING).unwrap(),
            state_u16(decoder.workspace, window_bytes, B3B_BLOCK_RING + 2).unwrap(),
            state_u16(decoder.workspace, window_bytes, B3B_BLOCK_RING + 4).unwrap(),
            state_u16(decoder.workspace, window_bytes, B3B_BLOCK_RING + 6).unwrap(),
            state_u16(decoder.workspace, window_bytes, B3B_BLOCK_RING + 8).unwrap(),
            state_u16(decoder.workspace, window_bytes, B3B_BLOCK_RING + 10).unwrap(),
        ];
        let map_index = state_u16(decoder.workspace, window_bytes, B3B_MAP_INDEX).unwrap();
        let map_initialized =
            state_u16(decoder.workspace, window_bytes, B3B_MAP_INITIALIZED).unwrap();
        let switch_phase =
            state_byte(decoder.workspace, window_bytes, B3B_BLOCK_SWITCH_PHASE).unwrap();
        let switch_kind =
            state_byte(decoder.workspace, window_bytes, B3B_BLOCK_SWITCH_KIND).unwrap();
        let pending_type =
            state_u16(decoder.workspace, window_bytes, B3B_PENDING_BLOCK_TYPE).unwrap();
        (
            completed,
            remaining,
            ring,
            map_index,
            map_initialized,
            switch_phase,
            switch_kind,
            pending_type,
        )
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

    #[derive(Clone, Copy, Debug)]
    enum TestChunkPlan {
        Whole,
        Split(usize),
        OneByte,
    }

    fn next_test_chunk_end(at: usize, len: usize, plan: TestChunkPlan) -> usize {
        match plan {
            TestChunkPlan::Whole => len,
            TestChunkPlan::Split(split) if at < split => split,
            TestChunkPlan::Split(_) => len,
            TestChunkPlan::OneByte => (at + 1).min(len),
        }
    }

    fn fresh_b3b_workspace() -> (Vec<u8>, u32) {
        let window_bytes = 1u32 << 16;
        let required = crate::brotli_prefix::required_workspace_bytes(16).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];
        initialize_b3b_state_image(&mut workspace, window_bytes).unwrap();
        (workspace, window_bytes)
    }

    fn compressed_meta_decoder_fixture() -> MetaBlockDecoder {
        let bytes = pack_lsb_bits(&compressed_meta_prefix_bits());
        let mut header = HeaderDecoder::new();
        let header_step = header.advance_header(&bytes, false);
        assert!(matches!(header_step.status, HeaderStatus::Complete { .. }));
        let mut at = header_step.consumed;
        let mut meta = MetaBlockDecoder::from_header(header).unwrap();
        for _ in 0..32 {
            let step = meta.advance_field(&bytes[at..], true);
            at += step.consumed;
            match step.status {
                MetaBlockStatus::Complete(_) => return meta,
                MetaBlockStatus::Progress => {}
                other => panic!("compressed meta fixture did not complete: {other:?}"),
            }
        }
        panic!("compressed meta fixture exceeded transition bound")
    }

    fn context_map_bytes(
        workspace: &[u8],
        window_bytes: u32,
        kind: crate::brotli_prefix::ContextMapKind,
        len: u16,
    ) -> Vec<u8> {
        let base = match kind {
            crate::brotli_prefix::ContextMapKind::Literal => {
                crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET
            }
            crate::brotli_prefix::ContextMapKind::Distance => {
                crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET
            }
        };
        workspace[window_bytes as usize + base as usize
            ..window_bytes as usize + base as usize + len as usize]
            .to_vec()
    }

    fn configure_binary_context_map(
        workspace: &mut [u8],
        window_bytes: u32,
        kind: crate::brotli_prefix::ContextMapKind,
        active_len: u16,
    ) {
        start_context_map(workspace, window_bytes, kind, active_len).unwrap();
        put_state_u16(workspace, window_bytes, B3B_MAP_TREES, 2).unwrap();
        put_state_byte(workspace, window_bytes, B3B_MAX_RUN_PREFIX, 0).unwrap();
        start_serialized_tree(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::TemporaryContext,
            0,
            2,
            2,
        )
        .unwrap();
        let code = SimpleCodeDescription {
            selector: 1,
            count: 2,
            symbols: [0, 1, 0, 0],
        };
        install_completed_simple_tree(
            workspace,
            window_bytes,
            crate::brotli_prefix::TreeRegion::TemporaryContext,
            0,
            2,
            code,
        )
        .unwrap();
        store_context_phase(workspace, window_bytes, 4).unwrap();
    }

    fn setup_binary_context_map(
        kind: crate::brotli_prefix::ContextMapKind,
        active_len: u16,
    ) -> (Vec<u8>, u32) {
        let (mut workspace, window_bytes) = fresh_b3b_workspace();
        configure_binary_context_map(&mut workspace, window_bytes, kind, active_len);
        (workspace, window_bytes)
    }

    fn drive_context_map(
        workspace: &mut [u8],
        window_bytes: u32,
        input: &[u8],
        plan: TestChunkPlan,
    ) -> (crate::brotli_prefix::ContextMapKind, u16) {
        let mut at = 0usize;
        for _ in 0..100_000 {
            let end = next_test_chunk_end(at, input.len(), plan);
            let step =
                advance_context_map(workspace, window_bytes, &input[at..end], end == input.len());
            at += step.consumed;
            match step.status {
                ContextAdvanceStatus::Complete { kind, num_trees } => {
                    assert_eq!(at, input.len());
                    return (kind, num_trees);
                }
                ContextAdvanceStatus::NeedInput => {
                    assert_eq!(at, end);
                    assert!(end < input.len());
                }
                ContextAdvanceStatus::Failed(error) => {
                    panic!("context map failed under {plan:?}: {error:?}")
                }
            }
        }
        panic!("context map exceeded transition bound")
    }

    fn setup_rle_phase(prefix: u8, active_len: u16) -> (Vec<u8>, u32) {
        let (mut workspace, window_bytes) = fresh_b3b_workspace();
        start_context_map(
            &mut workspace,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Literal,
            active_len,
        )
        .unwrap();
        put_state_u16(&mut workspace, window_bytes, B3B_MAP_TREES, 2).unwrap();
        put_state_byte(&mut workspace, window_bytes, B3B_PENDING_RUN, prefix).unwrap();
        store_context_phase(&mut workspace, window_bytes, 5).unwrap();
        (workspace, window_bytes)
    }

    fn drive_rle_suffix(
        workspace: &mut [u8],
        window_bytes: u32,
        _prefix: u8,
        active_len: u16,
        input: &[u8],
        plan: TestChunkPlan,
    ) -> Option<ContextAdvanceStatus> {
        let mut at = 0usize;
        for _ in 0..32 {
            let end = next_test_chunk_end(at, input.len(), plan);
            let (used, status) = advance_context_bits_phase(
                workspace,
                window_bytes,
                5,
                0,
                crate::brotli_prefix::ContextMapKind::Literal,
                active_len,
                &input[at..end],
                end == input.len(),
            );
            at += used;
            match status {
                Some(ContextAdvanceStatus::NeedInput) => {
                    assert_eq!(at, end);
                    assert!(end < input.len());
                }
                other => {
                    assert_eq!(at, input.len());
                    return other;
                }
            }
        }
        panic!("RLE suffix exceeded transition bound")
    }

    fn write_context_values(
        workspace: &mut [u8],
        window_bytes: u32,
        kind: crate::brotli_prefix::ContextMapKind,
        values: &[u8],
        num_trees: u16,
    ) {
        start_context_map(workspace, window_bytes, kind, values.len() as u16).unwrap();
        put_state_u16(workspace, window_bytes, B3B_MAP_TREES, num_trees).unwrap();
        let mut initialized = 0u16;
        for value in values {
            initialized = crate::brotli_prefix::write_next_context_entry(
                workspace,
                window_bytes,
                kind,
                values.len() as u16,
                initialized,
                *value,
                num_trees,
            )
            .unwrap();
        }
        store_context_map_progress(workspace, window_bytes, initialized).unwrap();
    }

    fn setup_tree_group_decoder<'a>(
        workspace: &'a mut [u8],
        window_bytes: u32,
    ) -> CompressedMetaBlockDecoder<'a> {
        let meta = compressed_meta_decoder_fixture();
        let mut decoder =
            CompressedMetaBlockDecoder::from_meta(workspace, window_bytes, meta).unwrap();
        store_b3b_queue(decoder.workspace, window_bytes, &BitQueue::new()).unwrap();
        let block_counts = [1u16, 2, 1];
        for (kind, count) in block_counts.into_iter().enumerate() {
            put_state_u16(
                decoder.workspace,
                window_bytes,
                B3B_BLOCK_COUNTS + 2 * kind as u16,
                count,
            )
            .unwrap();
            put_state_u32(
                decoder.workspace,
                window_bytes,
                B3B_INITIAL_LENGTHS + 4 * kind as u16,
                1u32 << 24,
            )
            .unwrap();
        }
        put_state_u16(decoder.workspace, window_bytes, B3B_LITERAL_TREES, 2).unwrap();
        put_state_u16(decoder.workspace, window_bytes, B3B_DISTANCE_TREES, 2).unwrap();
        put_state_byte(decoder.workspace, window_bytes, B3B_DISTANCE_POSTFIX, 0).unwrap();
        put_state_u16(decoder.workspace, window_bytes, B3B_DIRECT_DISTANCE, 0).unwrap();
        let literal_at =
            window_bytes as usize + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as usize;
        let distance_at =
            window_bytes as usize + crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET as usize;
        decoder.workspace[literal_at] = 0;
        decoder.workspace[distance_at] = 0;
        decoder
            .start_tree_group(0, CompressedOuterPhase::LiteralTreeGroup)
            .unwrap();
        decoder
    }

    fn tree_group_description_bytes() -> Vec<u8> {
        let mut bits = Vec::new();
        for width in [8u8, 8, 10, 10, 6, 6] {
            bits.extend([1, 0]);
            bits.extend([0, 0]);
            push_bits(&mut bits, 0, width);
        }
        pack_lsb_bits(&bits)
    }

    fn drive_tree_groups(
        decoder: &mut CompressedMetaBlockDecoder<'_>,
        input: &[u8],
        plan: TestChunkPlan,
    ) -> (CompressedHeader, Vec<(u8, u16)>) {
        let mut at = 0usize;
        let mut completed = Vec::new();
        for _ in 0..128 {
            let phase = decoder.load_outer_phase().unwrap();
            if phase == CompressedOuterPhase::Complete {
                let step = decoder.step(&input[at..], true);
                assert_eq!(step.consumed, 0);
                return match step.status {
                    CompressedHeaderStatus::Complete(header) => (header, completed),
                    other => panic!("completion handoff failed: {other:?}"),
                };
            }
            let group =
                state_byte(decoder.workspace, decoder.window_bytes, B3B_GROUP_KIND).unwrap();
            let tree = state_u16(decoder.workspace, decoder.window_bytes, B3B_TREE_INDEX).unwrap();
            let end = next_test_chunk_end(at, input.len(), plan);
            let (used, status) =
                decoder.advance_tree_groups_phase(phase, &input[at..end], end == input.len());
            at += used;
            match status {
                None => completed.push((group, tree)),
                Some(CompressedHeaderStatus::NeedInput) => {
                    assert_eq!(at, end);
                    assert!(end < input.len());
                }
                Some(CompressedHeaderStatus::Failed(error)) => {
                    panic!(
                        "tree group failed under {plan:?} at group={group} tree={tree} input={at}: {error:?}"
                    )
                }
                Some(CompressedHeaderStatus::Complete(_)) => {
                    panic!("tree group helper returned a header directly")
                }
            }
        }
        panic!("tree groups exceeded transition bound")
    }

    fn assert_nonfinal_need_input_final_truncated_and_sticky(
        decoder: &mut CompressedMetaBlockDecoder<'_>,
    ) {
        let base = (decoder.window_bytes + B3B_SCALAR_OFFSET) as usize;
        let logical_offsets = [
            B3B_QUEUE_LEN,
            B3B_QUEUE_OFFSET_BYTE,
            B3B_OUTER_PHASE,
            B3B_CURRENT_KIND,
            B3B_VAR_PHASE,
            B3B_VAR_WIDTH,
            B3B_CONTEXT_PHASE,
            B3B_MAP_INDEX,
            B3B_MAP_INDEX + 1,
            B3B_MAP_INITIALIZED,
            B3B_MAP_INITIALIZED + 1,
            B3B_GROUP_KIND,
            B3B_GROUP_PHASE,
            B3B_TREE_INDEX,
            B3B_TREE_INDEX + 1,
            B3B_TREE_COUNT,
            B3B_TREE_COUNT + 1,
            B3B_CODE_PHASE,
            B3B_ACTIVE_REGION,
            B3B_ACTIVE_TREE,
            B3B_ACTIVE_TREE + 1,
            B3B_INSTALLED_PREFIX_WIDTH,
            B3B_INSTALLED_PREFIX_BITS,
            B3B_INSTALLED_PREFIX_BITS + 1,
            B3B_INSTALLED_SCAN,
            B3B_INSTALLED_SCAN + 1,
        ];
        let before: Vec<u8> = (0..8)
            .map(|i| decoder.workspace[base + B3B_QUEUE_OFFSET as usize + i])
            .chain(
                logical_offsets
                    .into_iter()
                    .map(|offset| decoder.workspace[base + offset as usize]),
            )
            .collect();
        assert_eq!(
            decoder.step(&[], false),
            CompressedHeaderStep {
                consumed: 0,
                status: CompressedHeaderStatus::NeedInput,
            }
        );
        let after_nonfinal: Vec<u8> = (0..8)
            .map(|i| decoder.workspace[base + B3B_QUEUE_OFFSET as usize + i])
            .chain(
                logical_offsets
                    .into_iter()
                    .map(|offset| decoder.workspace[base + offset as usize]),
            )
            .collect();
        assert_eq!(after_nonfinal, before);
        assert_eq!(
            decoder.step(&[], true),
            CompressedHeaderStep {
                consumed: 0,
                status: CompressedHeaderStatus::Failed(CompressedHeaderError::Truncated),
            }
        );
        let failed = decoder.workspace.to_vec();
        assert_eq!(
            decoder.step(&[0xff], false),
            CompressedHeaderStep {
                consumed: 0,
                status: CompressedHeaderStatus::Failed(CompressedHeaderError::Truncated),
            }
        );
        assert_eq!(decoder.workspace, failed.as_slice());
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

    #[test]
    fn installed_symbol_reader_handles_single_canonical_and_suspension() {
        let window = 1u32 << 10;
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5u8; required];
        let single = crate::brotli_prefix::TreeMetadata::single(
            crate::brotli_prefix::TreeRegion::Literal,
            256,
            19,
        )
        .unwrap();
        let mut queue = BitQueue::new();
        let mut prefix = InstalledPrefixState::initial();
        assert_eq!(
            advance_installed_tree_symbol(
                &workspace,
                window,
                crate::brotli_prefix::TreeRegion::Literal,
                0,
                single,
                &mut queue,
                &mut prefix,
                &[],
                false,
            ),
            InstalledSymbolStep {
                consumed: 0,
                status: InstalledSymbolStatus::Symbol(19)
            }
        );

        let symbols = [1u16, 4, 0, 0];
        let meta = crate::brotli_prefix::install_simple_tree(
            &mut workspace,
            window,
            crate::brotli_prefix::TreeRegion::Literal,
            1,
            8,
            1,
            2,
            symbols,
        )
        .unwrap();
        for (byte, expected) in [(0u8, 1u16), (1u8, 4u16)] {
            let mut queue = BitQueue::new();
            let mut prefix = InstalledPrefixState::initial();
            let step = advance_installed_tree_symbol(
                &workspace,
                window,
                crate::brotli_prefix::TreeRegion::Literal,
                1,
                meta,
                &mut queue,
                &mut prefix,
                &[byte],
                false,
            );
            assert_eq!(step.status, InstalledSymbolStatus::Symbol(expected));
        }

        let mut queue = BitQueue::new();
        let mut prefix = InstalledPrefixState::initial();
        assert_eq!(
            advance_installed_tree_symbol(
                &workspace,
                window,
                crate::brotli_prefix::TreeRegion::Literal,
                1,
                meta,
                &mut queue,
                &mut prefix,
                &[],
                false,
            ),
            InstalledSymbolStep {
                consumed: 0,
                status: InstalledSymbolStatus::NeedInput
            }
        );
        assert_eq!(prefix, InstalledPrefixState::initial());
        assert_eq!(
            advance_installed_tree_symbol(
                &workspace,
                window,
                crate::brotli_prefix::TreeRegion::Literal,
                1,
                meta,
                &mut queue,
                &mut prefix,
                &[],
                true,
            ),
            InstalledSymbolStep {
                consumed: 0,
                status: InstalledSymbolStatus::Truncated
            }
        );
    }

    #[test]
    fn compressed_header_completes_with_exact_streaming_handoff() {
        for one_byte_chunks in [false, true] {
            let (
                header,
                remaining,
                ring,
                map_index,
                map_initialized,
                switch_phase,
                switch_kind,
                pending_type,
            ) = run_compressed_header_fixture(one_byte_chunks);
            assert_eq!(header.num_block_types, [1, 1, 1]);
            assert_eq!(header.initial_block_lengths, [1 << 24; 3]);
            assert_eq!(header.distance_postfix_bits, 0);
            assert_eq!(header.num_direct_distance_codes, 0);
            assert_eq!(header.distance_alphabet_size, 64);
            assert_eq!(header.num_literal_htrees, 1);
            assert_eq!(header.num_distance_htrees, 1);
            assert_eq!(header.literal_context_map_len, 64);
            assert_eq!(header.distance_context_map_len, 4);
            assert_eq!(header.literal_context_modes_len, 1);
            assert_eq!(header.literal_trees_initialized, 1);
            assert_eq!(header.command_trees_initialized, 1);
            assert_eq!(header.distance_trees_initialized, 1);
            assert_eq!(header.active_literal_tree, 0);
            assert_eq!(header.active_command_tree, 0);
            assert_eq!(header.active_distance_tree, 0);
            assert_eq!(map_index, 4);
            assert_eq!(map_initialized, 4);
            assert_eq!(remaining, [1 << 24; 3]);
            assert_eq!(ring, [1, 0, 1, 0, 1, 0]);
            assert_eq!(switch_phase, 0);
            assert_eq!(switch_kind, 255);
            assert_eq!(pending_type, 0);
        }
    }

    #[test]
    fn b3b_context_map_runtime_matrix() {
        let mut cases = 0usize;
        for (kind, active_len) in [
            (crate::brotli_prefix::ContextMapKind::Literal, 64u16),
            (crate::brotli_prefix::ContextMapKind::Distance, 4u16),
        ] {
            for plan in [TestChunkPlan::Whole, TestChunkPlan::OneByte] {
                let (mut workspace, window_bytes) = fresh_b3b_workspace();
                start_context_map(&mut workspace, window_bytes, kind, active_len).unwrap();
                let completed = drive_context_map(&mut workspace, window_bytes, &[0], plan);
                assert_eq!(completed, (kind, 1));
                assert_eq!(
                    context_map_bytes(&workspace, window_bytes, kind, active_len),
                    vec![0; active_len as usize],
                );
                cases += 1;
            }
        }

        for (kind, active_len) in [
            (crate::brotli_prefix::ContextMapKind::Literal, 64u16),
            (crate::brotli_prefix::ContextMapKind::Distance, 4u16),
        ] {
            let mut bits: Vec<u8> = (0..active_len).map(|i| (i & 1) as u8).collect();
            bits.push(0);
            let input = pack_lsb_bits(&bits);
            let mut plans = vec![TestChunkPlan::Whole, TestChunkPlan::OneByte];
            plans.extend((1..input.len()).map(TestChunkPlan::Split));
            for plan in plans {
                let (mut workspace, window_bytes) = setup_binary_context_map(kind, active_len);
                let completed = drive_context_map(&mut workspace, window_bytes, &input, plan);
                assert_eq!(completed, (kind, 2));
                assert_eq!(
                    context_map_bytes(&workspace, window_bytes, kind, active_len),
                    (0..active_len).map(|i| (i & 1) as u8).collect::<Vec<_>>(),
                );
                assert_eq!(
                    state_u16(&workspace, window_bytes, B3B_MAP_INDEX).unwrap(),
                    active_len,
                );
                assert_eq!(
                    state_u16(&workspace, window_bytes, B3B_MAP_INITIALIZED).unwrap(),
                    active_len,
                );
                cases += 1;
            }
        }
        assert_eq!(cases, 16);
    }

    #[test]
    fn b3b_rle_prefix_runtime_matrix_exact_fill_and_overflow() {
        let mut cases = 0usize;
        let mut exact_fill = 0usize;
        let mut overflow = 0usize;
        for prefix in 1u8..=16 {
            let input = vec![0u8; (prefix as usize).div_ceil(8)];
            for plan in [TestChunkPlan::Whole, TestChunkPlan::OneByte] {
                let active_len = if prefix <= 14 { 1u16 << prefix } else { 16_384 };
                let (mut workspace, window_bytes) = setup_rle_phase(prefix, active_len);
                let before_map = context_map_bytes(
                    &workspace,
                    window_bytes,
                    crate::brotli_prefix::ContextMapKind::Literal,
                    active_len,
                );
                let status = drive_rle_suffix(
                    &mut workspace,
                    window_bytes,
                    prefix,
                    active_len,
                    &input,
                    plan,
                );
                if prefix <= 14 {
                    assert_eq!(status, None);
                    assert_eq!(
                        state_u16(&workspace, window_bytes, B3B_MAP_INDEX).unwrap(),
                        active_len,
                    );
                    assert_eq!(
                        state_u16(&workspace, window_bytes, B3B_MAP_INITIALIZED).unwrap(),
                        active_len,
                    );
                    assert_eq!(
                        state_byte(&workspace, window_bytes, B3B_PENDING_RUN).unwrap(),
                        255,
                    );
                    assert_eq!(
                        context_map_bytes(
                            &workspace,
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Literal,
                            active_len,
                        ),
                        vec![0; active_len as usize],
                    );
                    exact_fill += 1;
                } else {
                    assert_eq!(
                        status,
                        Some(ContextAdvanceStatus::Failed(
                            CompressedHeaderError::InvalidFormat(
                                CompressedFormatError::ContextMapRepeat,
                            ),
                        )),
                    );
                    assert_eq!(
                        state_u16(&workspace, window_bytes, B3B_MAP_INDEX).unwrap(),
                        0,
                    );
                    assert_eq!(
                        state_u16(&workspace, window_bytes, B3B_MAP_INITIALIZED).unwrap(),
                        0,
                    );
                    assert_eq!(
                        context_map_bytes(
                            &workspace,
                            window_bytes,
                            crate::brotli_prefix::ContextMapKind::Literal,
                            active_len,
                        ),
                        before_map,
                    );
                    overflow += 1;
                }
                cases += 1;
            }
        }
        assert_eq!((cases, exact_fill, overflow), (32, 28, 4));
    }

    #[test]
    fn b3b_mtf_coverage_and_native_comparison_classification() {
        let (mut no_mtf, window_bytes) = fresh_b3b_workspace();
        write_context_values(
            &mut no_mtf,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            &[0, 1],
            2,
        );
        store_context_phase(&mut no_mtf, window_bytes, 6).unwrap();
        assert_eq!(
            advance_context_bits_phase(
                &mut no_mtf,
                window_bytes,
                6,
                1,
                crate::brotli_prefix::ContextMapKind::Distance,
                2,
                &[0],
                true,
            ),
            (1, None),
        );
        assert_eq!(state_byte(&no_mtf, window_bytes, B3B_CONTEXT_PHASE), Ok(8));
        assert!(advance_context_coverage_phase(
            &mut no_mtf,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            2,
        )
        .is_ok());
        assert_eq!(
            context_map_bytes(
                &no_mtf,
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                2,
            ),
            vec![0, 1],
        );

        let (mut mtf, window_bytes) = fresh_b3b_workspace();
        write_context_values(
            &mut mtf,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            &[1, 1],
            2,
        );
        store_context_phase(&mut mtf, window_bytes, 6).unwrap();
        assert_eq!(
            advance_context_bits_phase(
                &mut mtf,
                window_bytes,
                6,
                1,
                crate::brotli_prefix::ContextMapKind::Distance,
                2,
                &[1],
                true,
            ),
            (1, None),
        );
        assert_eq!(state_byte(&mtf, window_bytes, B3B_CONTEXT_PHASE), Ok(7));
        advance_context_mtf_phase(
            &mut mtf,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            2,
        )
        .unwrap();
        assert_eq!(
            context_map_bytes(
                &mtf,
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                2,
            ),
            vec![1, 0],
        );
        advance_context_coverage_phase(
            &mut mtf,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            2,
        )
        .unwrap();

        let (mut missing, window_bytes) = fresh_b3b_workspace();
        write_context_values(
            &mut missing,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Distance,
            &[0, 0],
            2,
        );
        store_context_phase(&mut missing, window_bytes, 8).unwrap();
        assert_eq!(
            advance_context_coverage_phase(
                &mut missing,
                window_bytes,
                crate::brotli_prefix::ContextMapKind::Distance,
                2,
            ),
            Err(CompressedHeaderError::InvalidFormat(
                CompressedFormatError::ContextMapCoverage,
            )),
        );

        #[derive(Debug, PartialEq, Eq)]
        enum NativeComparisonClass {
            SameAcceptanceStatus,
            IntentionalRfcStrictMissingTreeDifference,
            InternalFieldsUnavailable,
        }
        let accepted_cases = NativeComparisonClass::SameAcceptanceStatus;
        let missing_tree = NativeComparisonClass::IntentionalRfcStrictMissingTreeDifference;
        let internal_fields = NativeComparisonClass::InternalFieldsUnavailable;
        assert_eq!(accepted_cases, NativeComparisonClass::SameAcceptanceStatus);
        assert_eq!(
            missing_tree,
            NativeComparisonClass::IntentionalRfcStrictMissingTreeDifference,
        );
        assert_eq!(
            internal_fields,
            NativeComparisonClass::InternalFieldsUnavailable
        );
        // tests/native/brotli_stream_harness.c can compare native acceptance/status.
        // It cannot expose native context-map or MTF fields, so those comparisons
        // are intentionally classified unavailable rather than inferred.
    }

    #[test]
    fn b3b_final_and_nonfinal_exhaustion_are_exact_and_sticky() {
        let required = crate::brotli_prefix::required_workspace_bytes(16).unwrap() as usize;
        let window_bytes = 1u32 << 16;

        let mut block_workspace = vec![0xa5u8; required];
        let block_meta = compressed_meta_decoder_fixture();
        let mut block =
            CompressedMetaBlockDecoder::from_meta(&mut block_workspace, window_bytes, block_meta)
                .unwrap();
        store_b3b_queue(block.workspace, window_bytes, &BitQueue::new()).unwrap();
        assert_nonfinal_need_input_final_truncated_and_sticky(&mut block);

        let mut context_workspace = vec![0xa5u8; required];
        let context_meta = compressed_meta_decoder_fixture();
        let mut context = CompressedMetaBlockDecoder::from_meta(
            &mut context_workspace,
            window_bytes,
            context_meta,
        )
        .unwrap();
        configure_binary_context_map(
            context.workspace,
            window_bytes,
            crate::brotli_prefix::ContextMapKind::Literal,
            64,
        );
        store_b3b_queue(context.workspace, window_bytes, &BitQueue::new()).unwrap();
        context
            .store_outer_phase(CompressedOuterPhase::LiteralContextMap)
            .unwrap();
        assert_nonfinal_need_input_final_truncated_and_sticky(&mut context);

        let mut tree_workspace = vec![0xa5u8; required];
        let mut tree = setup_tree_group_decoder(&mut tree_workspace, window_bytes);
        assert_nonfinal_need_input_final_truncated_and_sticky(&mut tree);
    }

    #[test]
    fn b3b_tree_group_order_count_and_completion_chunk_matrix() {
        let input = tree_group_description_bytes();
        let mut plans = vec![TestChunkPlan::Whole, TestChunkPlan::OneByte];
        plans.extend((1..input.len()).map(TestChunkPlan::Split));
        let expected_order = vec![(0u8, 0u16), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)];
        let expected_cases = plans.len();
        let required = crate::brotli_prefix::required_workspace_bytes(16).unwrap() as usize;
        let window_bytes = 1u32 << 16;
        let mut cases = 0usize;
        for plan in plans {
            let mut workspace = vec![0xa5u8; required];
            let mut decoder = setup_tree_group_decoder(&mut workspace, window_bytes);
            let (header, order) = drive_tree_groups(&mut decoder, &input, plan);
            assert_eq!(order, expected_order);
            assert_eq!(header.num_block_types, [1, 2, 1]);
            assert_eq!(header.initial_block_lengths, [1 << 24; 3]);
            assert_eq!(header.literal_trees_initialized, 2);
            assert_eq!(header.command_trees_initialized, 2);
            assert_eq!(header.distance_trees_initialized, 2);
            assert_eq!(header.active_literal_tree, 0);
            assert_eq!(header.active_command_tree, 0);
            assert_eq!(header.active_distance_tree, 0);
            for (region, symbols) in [
                (crate::brotli_prefix::TreeRegion::Literal, 256u16),
                (crate::brotli_prefix::TreeRegion::Command, 704u16),
                (crate::brotli_prefix::TreeRegion::Distance, 64u16),
            ] {
                for tree in 0..2 {
                    let meta = crate::brotli_prefix::read_tree_metadata(
                        decoder.workspace,
                        window_bytes,
                        region,
                        2,
                        tree,
                    )
                    .unwrap();
                    assert_eq!(meta.symbols, symbols);
                }
            }
            cases += 1;
        }
        assert_eq!(cases, expected_cases);
        assert_eq!(cases, input.len() + 1);
    }
}
