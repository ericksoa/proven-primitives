//! Brotli B3c implementation candidate under the approved normal-window profile.
//!
//! M1 compressed-header metering is checked; broader B3c refinement and release
//! obligations remain open.
//! This module is not a supported or completely verified Brotli decoder.

use vstd::prelude::*;

verus! {

pub const B3C_INITIALIZATION_WORK: u64 = 425;
const B3C_EMISSION_WRITE_WORK: u64 = 24;

#[verifier::bit_vector]
proof fn approved_window_bytes(bits: u8)
    requires 10 <= bits <= 24,
    ensures
        1_024 <= (1u32 << bits) <= 16_777_216,
        ((1u32 << bits) & (((1u32 << bits) - 1) as u32)) == 0,
{}

#[verifier::bit_vector]
proof fn dictionary_mask_shift_is_nonzero(bits: u8)
    requires 1 <= bits < 32,
    ensures (1u32 << bits) >= 2,
{}

fn selected_literal_context(
    mode: u8,
    previous: u8,
    second_previous: u8,
) -> (r: u8)
    requires mode < 4,
    ensures r == (
        crate::brotli_data::LITERAL_CONTEXT_TABLE@[(mode as int) * 512 + previous as int]
        | crate::brotli_data::LITERAL_CONTEXT_TABLE@[
            (mode as int) * 512 + 256 + second_previous as int
        ]
    ),
{
    crate::brotli_data::literal_context(mode, previous, second_previous)
}

fn command_copy_length_context(copy_offset: u16) -> (r: u8)
    ensures r == if copy_offset < 2 {
        0u8
    } else if copy_offset <= 4 {
        (copy_offset - 2) as u8
    } else {
        3u8
    },
{
    if copy_offset < 2 {
        0
    } else if copy_offset <= 4 {
        (copy_offset - 2) as u8
    } else {
        3
    }
}

fn phase_after_completed_insert(meta_remaining: u32) -> (r: u8)
    ensures r == if meta_remaining == 0 { 15u8 } else { 8u8 },
{
    if meta_remaining == 0 { 15 } else { 8 }
}

fn next_recent_cursor(cursor: u8) -> (r: u8)
    requires cursor < 4,
    ensures r == if cursor == 3 { 0u8 } else { (cursor + 1) as u8 },
{
    if cursor == 3 { 0 } else { cursor + 1 }
}

fn copy_setup_phase(distance: u32, history: u32) -> (r: u8)
    requires distance > 0,
    ensures
        distance <= history ==> r == 12,
        distance > history ==> r == 13,
{
    if distance <= history { 12 } else { 13 }
}

fn overlap_source_position(
    position: u32,
    distance: u32,
    window_bytes: u32,
) -> (r: u32)
    requires position < window_bytes, 0 < distance <= window_bytes,
    ensures
        r < window_bytes,
        position >= distance ==> r == position - distance,
        position < distance ==> r == window_bytes - (distance - position),
{
    if position >= distance {
        position - distance
    } else {
        window_bytes - (distance - position)
    }
}

fn output_block_reason(
    output_remaining: u64,
    work_remaining: u64,
    has_output_slot: bool,
) -> (r: u8)
    ensures
        output_remaining == 0 || work_remaining < B3C_EMISSION_WRITE_WORK ==> r == 1,
        output_remaining > 0 && work_remaining >= B3C_EMISSION_WRITE_WORK && !has_output_slot ==> r == 2,
        output_remaining > 0 && work_remaining >= B3C_EMISSION_WRITE_WORK && has_output_slot ==> r == 0,
{
    if output_remaining == 0 || work_remaining < B3C_EMISSION_WRITE_WORK {
        1
    } else if !has_output_slot {
        2
    } else {
        0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequestLimits {
    pub max_input: u64,
    pub max_output: u64,
    pub max_work: u64,
    pub max_calls: u64,
    pub max_initializations: u32,
    pub max_window_bits: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequestBudget {
    pub(crate) limits: RequestLimits,
    pub(crate) input_remaining: u64,
    pub(crate) output_remaining: u64,
    pub(crate) work_remaining: u64,
    pub(crate) calls_remaining: u64,
    pub(crate) initializations_remaining: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Step {
    pub consumed: usize,
    pub produced: usize,
    pub status: Status,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    NeedInput,
    NeedOutput,
    Finished,
    Failed(StreamError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamError {
    InvalidFormat,
    Truncated,
    UnsupportedMode,
    ResourceLimit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InitError {
    InvalidLimits,
    WorkspaceTooSmall,
    ResourceLimit,
}

impl RequestBudget {
    pub closed spec fn limits_view(&self) -> RequestLimits {
        self.limits
    }

    pub closed spec fn remaining_work(&self) -> u64 {
        self.work_remaining
    }

    pub closed spec fn remaining_initializations(&self) -> u32 {
        self.initializations_remaining
    }

    pub closed spec fn valid(&self) -> bool {
        &&& 10 <= self.limits.max_window_bits <= 24
        &&& self.input_remaining <= self.limits.max_input
        &&& self.output_remaining <= self.limits.max_output
        &&& self.work_remaining <= self.limits.max_work
        &&& self.calls_remaining <= self.limits.max_calls
        &&& self.initializations_remaining <= self.limits.max_initializations
    }

    pub closed spec fn matches_limits(&self, limits: RequestLimits) -> bool {
        &&& self.limits == limits
        &&& self.input_remaining == limits.max_input
        &&& self.output_remaining == limits.max_output
        &&& self.work_remaining == limits.max_work
        &&& self.calls_remaining == limits.max_calls
        &&& self.initializations_remaining == limits.max_initializations
    }

    pub closed spec fn reset_effect(
        &self,
        before: RequestBudget,
        result: Result<(), InitError>,
    ) -> bool {
        &&& self.limits == before.limits
        &&& self.input_remaining == before.input_remaining
        &&& self.output_remaining == before.output_remaining
        &&& self.calls_remaining == before.calls_remaining
        &&& if before.initializations_remaining == 0 {
            &&& result == Err(InitError::ResourceLimit)
            &&& *self == before
        } else if before.work_remaining < B3C_INITIALIZATION_WORK {
            &&& result == Err(InitError::ResourceLimit)
            &&& self.initializations_remaining == before.initializations_remaining - 1
            &&& self.work_remaining == before.work_remaining
        } else {
            &&& result.is_ok()
            &&& self.initializations_remaining == before.initializations_remaining - 1
            &&& self.work_remaining == before.work_remaining - B3C_INITIALIZATION_WORK
        }
    }

    pub fn new(limits: RequestLimits) -> (r: Result<Self, InitError>)
        ensures
            r.is_ok() == (10 <= limits.max_window_bits <= 24),
            r.is_ok() ==> {
                let budget = r.unwrap();
                &&& budget.valid()
                &&& budget.matches_limits(limits)
                &&& budget.limits_view() == limits
                &&& budget.remaining_work() == limits.max_work
                &&& budget.remaining_initializations() == limits.max_initializations
            },
            r.is_err() ==> r == Err(InitError::InvalidLimits),
    {
        if limits.max_window_bits < 10 || limits.max_window_bits > 24 {
            return Err(InitError::InvalidLimits);
        }
        Ok(Self {
            limits,
            input_remaining: limits.max_input,
            output_remaining: limits.max_output,
            work_remaining: limits.max_work,
            calls_remaining: limits.max_calls,
            initializations_remaining: limits.max_initializations,
        })
    }

    pub(crate) fn reserve_initialization(&mut self) -> (r: bool)
        requires old(self).valid(),
        ensures
            r == (old(self).initializations_remaining > 0
                && old(self).work_remaining >= B3C_INITIALIZATION_WORK),
            final(self).valid(),
            final(self).limits == old(self).limits,
            old(self).initializations_remaining == 0 ==> {
                &&& !r
                &&& *final(self) == *old(self)
            },
            old(self).initializations_remaining > 0
                && old(self).work_remaining < B3C_INITIALIZATION_WORK ==> {
                &&& !r
                &&& final(self).initializations_remaining
                    == old(self).initializations_remaining - 1
                &&& final(self).work_remaining == old(self).work_remaining
                &&& final(self).input_remaining == old(self).input_remaining
                &&& final(self).output_remaining == old(self).output_remaining
                &&& final(self).calls_remaining == old(self).calls_remaining
            },
            r ==> {
                &&& old(self).initializations_remaining > 0
                &&& old(self).work_remaining >= B3C_INITIALIZATION_WORK
                &&& final(self).initializations_remaining
                    == old(self).initializations_remaining - 1
                &&& final(self).work_remaining
                    == old(self).work_remaining - B3C_INITIALIZATION_WORK
                &&& final(self).input_remaining == old(self).input_remaining
                &&& final(self).output_remaining == old(self).output_remaining
                &&& final(self).calls_remaining == old(self).calls_remaining
            },
    {
        if self.initializations_remaining == 0 {
            return false;
        }
        self.initializations_remaining = self.initializations_remaining - 1;
        if self.work_remaining < B3C_INITIALIZATION_WORK {
            return false;
        }
        self.work_remaining = self.work_remaining - B3C_INITIALIZATION_WORK;
        true
    }

    pub(crate) fn charge_call(&mut self) -> (r: bool)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).limits == old(self).limits,
            old(self).calls_remaining == 0 ==> {
                &&& !r
                &&& *final(self) == *old(self)
            },
            old(self).calls_remaining > 0 ==> {
                &&& r
                &&& final(self).calls_remaining == old(self).calls_remaining - 1
                &&& final(self).input_remaining == old(self).input_remaining
                &&& final(self).output_remaining == old(self).output_remaining
                &&& final(self).work_remaining == old(self).work_remaining
                &&& final(self).initializations_remaining
                    == old(self).initializations_remaining
            },
    {
        if self.calls_remaining == 0 {
            false
        } else {
            self.calls_remaining = self.calls_remaining - 1;
            true
        }
    }

    pub(crate) fn charge_work(&mut self, amount: u64) -> (r: bool)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).limits == old(self).limits,
            old(self).work_remaining < amount ==> {
                &&& !r
                &&& *final(self) == *old(self)
            },
            old(self).work_remaining >= amount ==> {
                &&& r
                &&& final(self).work_remaining == old(self).work_remaining - amount
                &&& final(self).input_remaining == old(self).input_remaining
                &&& final(self).output_remaining == old(self).output_remaining
                &&& final(self).calls_remaining == old(self).calls_remaining
                &&& final(self).initializations_remaining
                    == old(self).initializations_remaining
            },
    {
        if self.work_remaining < amount {
            false
        } else {
            self.work_remaining = self.work_remaining - amount;
            true
        }
    }

    pub(crate) fn charge_input(&mut self, amount: u64) -> (r: bool)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).limits == old(self).limits,
            old(self).input_remaining < amount ==> {
                &&& !r
                &&& *final(self) == *old(self)
            },
            old(self).input_remaining >= amount ==> {
                &&& r
                &&& final(self).input_remaining == old(self).input_remaining - amount
                &&& final(self).output_remaining == old(self).output_remaining
                &&& final(self).work_remaining == old(self).work_remaining
                &&& final(self).calls_remaining == old(self).calls_remaining
                &&& final(self).initializations_remaining
                    == old(self).initializations_remaining
            },
    {
        if self.input_remaining < amount {
            false
        } else {
            self.input_remaining = self.input_remaining - amount;
            true
        }
    }

    pub(crate) fn charge_output(&mut self, amount: u64) -> (r: bool)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).limits == old(self).limits,
            old(self).output_remaining < amount ==> {
                &&& !r
                &&& *final(self) == *old(self)
            },
            old(self).output_remaining >= amount ==> {
                &&& r
                &&& final(self).output_remaining == old(self).output_remaining - amount
                &&& final(self).input_remaining == old(self).input_remaining
                &&& final(self).work_remaining == old(self).work_remaining
                &&& final(self).calls_remaining == old(self).calls_remaining
                &&& final(self).initializations_remaining
                    == old(self).initializations_remaining
            },
    {
        if self.output_remaining < amount {
            false
        } else {
            self.output_remaining = self.output_remaining - amount;
            true
        }
    }
}

pub struct BrotliDecoder<'w, 'b> {
    pub(crate) workspace: &'w mut [u8],
    pub(crate) budget: &'b mut RequestBudget,
}

impl<'w, 'b> BrotliDecoder<'w, 'b> {
    spec fn invariant(&self) -> bool {
        let window_bytes = (1u32 << self.budget.limits.max_window_bits) as u32;
        &&& self.budget.valid()
        &&& crate::brotli_input::b3c_workspace_shape(
            self.workspace@.len() as nat,
            window_bytes,
        )
        &&& (crate::brotli_input::b3c_scalar_byte_at(
            self.workspace@,
            window_bytes,
            crate::brotli_input::B3C_STREAM_PHASE as int,
        ) == 5 ==> crate::brotli_input::compressed_decoder_state_ok(
            self.workspace@,
            window_bytes,
        ))
    }

    pub closed spec fn valid(&self) -> bool {
        self.invariant()
    }

    pub closed spec fn workspace_view(&self) -> Seq<u8> {
        self.workspace@
    }

    pub closed spec fn budget_view(&self) -> RequestBudget {
        *self.budget
    }

    pub closed spec fn stored_terminal_result(&self) -> Option<Step> {
        let window_bytes = (1u32 << self.budget.limits.max_window_bits) as u32;
        let phase = crate::brotli_input::b3c_scalar_byte_at(
            self.workspace@,
            window_bytes,
            crate::brotli_input::B3C_STREAM_PHASE as int,
        );
        if phase == 8 {
            Some(Step { consumed: 0, produced: 0, status: Status::Finished })
        } else if phase == 9 {
            let family = crate::brotli_input::b3c_scalar_byte_at(
                self.workspace@,
                window_bytes,
                crate::brotli_input::B3C_TERMINAL_FAMILY as int,
            );
            Some(Step {
                consumed: 0,
                produced: 0,
                status: Status::Failed(match family {
                    2 => StreamError::Truncated,
                    3 => StreamError::UnsupportedMode,
                    4 => StreamError::ResourceLimit,
                    _ => StreamError::InvalidFormat,
                }),
            })
        } else {
            None
        }
    }

    pub fn new(
        workspace: &'w mut [u8],
        budget: &'b mut RequestBudget,
    ) -> (r: Result<Self, InitError>)
        requires old(budget).valid(),
        ensures
            r.is_err() ==> final(workspace)@ == old(workspace)@,
            match r {
                Ok(decoder) => {
                    &&& decoder.valid()
                    &&& old(workspace)@.len()
                        >= (1u32 << old(budget).limits_view().max_window_bits) as nat + 1_176_560
                    &&& old(budget).remaining_initializations() > 0
                    &&& old(budget).remaining_work() >= 425
                    &&& decoder.budget_view().limits_view() == old(budget).limits_view()
                    &&& decoder.budget_view().remaining_work() as nat + 425
                        == old(budget).remaining_work() as nat
                    &&& decoder.budget_view().remaining_initializations() as nat + 1
                        == old(budget).remaining_initializations() as nat
                    &&& decoder.budget_view().reset_effect(*old(budget), Ok(()))
                    &&& decoder.workspace_view().len() == old(workspace)@.len()
                    &&& decoder.stored_terminal_result().is_none()
                },
                Err(InitError::WorkspaceTooSmall) => {
                    &&& old(workspace)@.len()
                        < (1u32 << old(budget).limits_view().max_window_bits) as nat + 1_176_560
                    &&& *final(budget) == *old(budget)
                },
                Err(InitError::ResourceLimit) => {
                    &&& old(workspace)@.len()
                        >= (1u32 << old(budget).limits_view().max_window_bits) as nat + 1_176_560
                    &&& (old(budget).remaining_initializations() == 0
                        || old(budget).remaining_work() < 425)
                    &&& final(budget).reset_effect(*old(budget), Err(InitError::ResourceLimit))
                },
                Err(InitError::InvalidLimits) => false,
            },
    {
        proof {
            reveal(BrotliDecoder::valid);
            reveal(BrotliDecoder::budget_view);
            reveal(BrotliDecoder::workspace_view);
            reveal(BrotliDecoder::stored_terminal_result);
            reveal(RequestBudget::reset_effect);
            reveal(RequestBudget::limits_view);
            reveal(RequestBudget::remaining_work);
            reveal(RequestBudget::remaining_initializations);
            assert(crate::brotli_prefix::FIXED_SCRATCH_BYTES == 1_176_560) by (compute_only);
            assert(B3C_INITIALIZATION_WORK == 425) by (compute_only);
            approved_window_bytes(budget.limits.max_window_bits);
        }
        let window_bytes = 1u32 << budget.limits.max_window_bits;
        let required = match (window_bytes as usize).checked_add(
            crate::brotli_prefix::FIXED_SCRATCH_BYTES as usize,
        ) {
            Some(value) => value,
            None => return Err(InitError::WorkspaceTooSmall),
        };
        if workspace.len() < required {
            return Err(InitError::WorkspaceTooSmall);
        }
        if !budget.reserve_initialization() {
            return Err(InitError::ResourceLimit);
        }
        proof {
            reveal(RequestBudget::valid);
            approved_window_bytes(budget.limits.max_window_bits);
            assert(crate::brotli_input::b3c_workspace_shape(
                workspace@.len() as nat,
                window_bytes,
            ));
        }
        match crate::brotli_input::initialize_serialized_b3c(
            workspace,
            window_bytes,
        ) {
            Ok(()) => Ok(Self { workspace, budget }),
            Err(_) => {
                proof { assert(false); }
                Err(InitError::WorkspaceTooSmall)
            }
        }
    }

    pub fn reset(&mut self) -> (r: Result<(), InitError>)
        requires old(self).valid(),
        ensures
            final(self).valid(),
            final(self).budget_view().reset_effect(old(self).budget_view(), r),
            r.is_err() ==> final(self).workspace_view() == old(self).workspace_view(),
    {
        proof {
            reveal(RequestBudget::reset_effect);
            reveal(BrotliDecoder::budget_view);
        }
        let ghost before_budget = *self.budget;
        let reserved = self.budget.reserve_initialization();
        if !reserved {
            proof {
                if before_budget.initializations_remaining == 0 {
                    assert(*self.budget == before_budget);
                } else {
                    assert(before_budget.work_remaining >= B3C_INITIALIZATION_WORK
                        ==> reserved);
                    assert(before_budget.work_remaining < B3C_INITIALIZATION_WORK);
                }
                assert(self.budget.reset_effect(
                    before_budget,
                    Err(InitError::ResourceLimit),
                ));
            }
            return Err(InitError::ResourceLimit);
        }
        let window_bytes = 1u32 << self.budget.limits.max_window_bits;
        proof {
            reveal(BrotliDecoder::valid);
            assert(crate::brotli_input::b3c_workspace_shape(
                self.workspace@.len() as nat,
                window_bytes,
            ));
        }
        match crate::brotli_input::initialize_serialized_b3c(
            self.workspace,
            window_bytes,
        ) {
            Ok(()) => {
                proof {
                    assert(self.budget.reset_effect(before_budget, Ok(())));
                }
                Ok(())
            },
            Err(_) => {
                proof { assert(false); }
                Err(InitError::WorkspaceTooSmall)
            }
        }
    }

    fn window_bytes(&self) -> (r: u32)
        ensures old(self.budget).valid() ==>
            r == (1u32 << old(self.budget).limits.max_window_bits) as u32,
    {
        if self.budget.limits.max_window_bits < 32 {
            1u32 << self.budget.limits.max_window_bits
        } else {
            0
        }
    }

    fn read_phase(&self) -> (r: Result<u8, StreamError>)
        requires self.valid(),
        ensures ({
            let window_bytes = (1u32 << old(self.budget).limits.max_window_bits) as u32;
            let phase = crate::brotli_input::b3c_scalar_byte_at(
                old(self.workspace)@,
                window_bytes,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            );
            if phase <= 9 {
                r == Ok(phase)
            } else {
                r == Err(StreamError::InvalidFormat)
            }
        }),
    {
        proof { reveal(BrotliDecoder::valid); }
        match crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            self.window_bytes(),
            crate::brotli_input::B3C_STREAM_PHASE,
        ) {
            Ok(value) if value <= 9 => Ok(value),
            _ => Err(StreamError::InvalidFormat),
        }
    }

    fn write_phase(&mut self, phase: u8) -> (r: Result<(), StreamError>)
        requires
            old(self).budget.valid(),
            crate::brotli_input::b3c_workspace_shape(
                old(self).workspace@.len() as nat,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
            ),
            phase == 5 ==> crate::brotli_input::compressed_decoder_state_ok(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
            ),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
    {
        proof { reveal(BrotliDecoder::valid); }
        let window_bytes = self.window_bytes();
        let ghost before_workspace = self.workspace@;
        proof {
            if phase == 5 {
                assert(crate::brotli_input::compressed_decoder_state_ok(
                    before_workspace,
                    window_bytes,
                ));
            }
        }
        let result = crate::brotli_input::write_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_STREAM_PHASE,
            phase,
        ).0;
        match result {
            Ok(()) => {
                proof {
                    reveal(BrotliDecoder::valid);
                    assert(crate::brotli_input::b3c_scalar_byte_at(
                        self.workspace@,
                        window_bytes,
                        crate::brotli_input::B3C_STREAM_PHASE as int,
                    ) == phase);
                    assert(self.budget.valid());
                    assert(window_bytes
                        == (1u32 << self.budget.limits.max_window_bits) as u32);
                    assert(crate::brotli_input::b3c_workspace_shape(
                        self.workspace@.len() as nat,
                        window_bytes,
                    ));
                    if phase == 5 {
                        assert(crate::brotli_input::compressed_decoder_state_ok(
                            before_workspace,
                            window_bytes,
                        ));
                        assert(crate::brotli_input::compressed_decoder_state_ok(
                            self.workspace@,
                            window_bytes,
                        ));
                    }
                    assert(self.invariant());
                }
                Ok(())
            }
            Err(_) => {
                proof {
                    reveal(BrotliDecoder::valid);
                    assert(self.invariant());
                }
                Err(StreamError::InvalidFormat)
            }
        }
    }

    fn failure_encoding(error: StreamError) -> (u8, u8) {
        match error {
            StreamError::InvalidFormat => (1, 0),
            StreamError::Truncated => (2, 0),
            StreamError::UnsupportedMode => (3, 0),
            StreamError::ResourceLimit => (4, 0),
        }
    }

    fn fail(
        &mut self,
        error: StreamError,
        consumed: usize,
        produced: usize,
    ) -> (r: Step)
        requires
            old(self).budget.valid(),
            crate::brotli_input::b3c_workspace_shape(
                old(self).workspace@.len() as nat,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
            ),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.consumed == consumed,
            r.produced == produced,
            r.status == Status::Failed(error),
            crate::brotli_input::b3c_scalar_byte_at(
                final(self).workspace@,
                (1u32 << final(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 9,
    {
        let (family, detail) = Self::failure_encoding(error);
        let window_bytes = self.window_bytes();
        let family_result = crate::brotli_input::write_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_TERMINAL_FAMILY,
            family,
        ).0;
        let detail_result = crate::brotli_input::write_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_TERMINAL_DETAIL,
            detail,
        ).0;
        let phase_result = crate::brotli_input::write_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_STREAM_PHASE,
            9,
        ).0;
        let stored = family_result.is_ok() && detail_result.is_ok() && phase_result.is_ok();
        proof {
            reveal(BrotliDecoder::invariant);
            assert(stored);
            assert(crate::brotli_input::b3c_scalar_byte_at(
                self.workspace@,
                window_bytes,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 9);
            assert(self.invariant());
        }
        let final_error = if stored { error } else { StreamError::InvalidFormat };
        Step { consumed, produced, status: Status::Failed(final_error) }
    }

    fn terminal_step(&self, phase: u8) -> (r: Option<Step>)
        requires self.valid(),
        ensures
            phase == 8 ==> r == Some(Step {
                consumed: 0,
                produced: 0,
                status: Status::Finished,
            }),
            phase == 9 ==> {
                let family = crate::brotli_input::b3c_scalar_byte_at(
                    old(self.workspace)@,
                    (1u32 << old(self.budget).limits.max_window_bits) as u32,
                    crate::brotli_input::B3C_TERMINAL_FAMILY as int,
                );
                r == Some(Step {
                    consumed: 0,
                    produced: 0,
                    status: Status::Failed(match family {
                        2 => StreamError::Truncated,
                        3 => StreamError::UnsupportedMode,
                        4 => StreamError::ResourceLimit,
                        _ => StreamError::InvalidFormat,
                    }),
                })
            },
            phase != 8 && phase != 9 ==> r.is_none(),
    {
        if phase == 8 {
            return Some(Step { consumed: 0, produced: 0, status: Status::Finished });
        }
        if phase != 9 {
            return None;
        }
        let family = match crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            self.window_bytes(),
            crate::brotli_input::B3C_TERMINAL_FAMILY,
        ) {
            Ok(value) => value,
            Err(_) => 1,
        };
        let error = match family {
            2 => StreamError::Truncated,
            3 => StreamError::UnsupportedMode,
            4 => StreamError::ResourceLimit,
            _ => StreamError::InvalidFormat,
        };
        Some(Step { consumed: 0, produced: 0, status: Status::Failed(error) })
    }

    fn map_core_failure(error: crate::brotli_input::CoreFailure) -> StreamError {
        match error {
            crate::brotli_input::CoreFailure::InvalidFormat(_) => StreamError::InvalidFormat,
            crate::brotli_input::CoreFailure::Truncated => StreamError::Truncated,
            crate::brotli_input::CoreFailure::UnsupportedMode => StreamError::UnsupportedMode,
            crate::brotli_input::CoreFailure::ResourceLimit => StreamError::ResourceLimit,
        }
    }

    fn committed_eof(&self) -> bool {
        match crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            self.window_bytes(),
            crate::brotli_input::B3C_EOF_COMMITTED,
        ) {
            Ok(value) => value != 0,
            Err(_) => true,
        }
    }

    fn state_byte(&self, relative: u16) -> (r: Result<u8, StreamError>)
        requires self.valid(), relative < crate::brotli_input::B3C_SCALAR_BYTES,
        ensures r.is_ok() ==> r.unwrap() == crate::brotli_input::b3c_scalar_byte_at(
            old(self.workspace)@,
            (1u32 << old(self.budget).limits.max_window_bits) as u32,
            relative as int,
        ),
    {
        proof { reveal(BrotliDecoder::valid); }
        crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            self.window_bytes(),
            relative,
        )
        .map_err(|_| StreamError::InvalidFormat)
    }

    fn state_u32(&self, relative: u16) -> Result<u32, StreamError> {
        crate::brotli_input::read_b3c_state_u32(
            self.workspace,
            self.window_bytes(),
            relative,
        )
        .map_err(|_| StreamError::InvalidFormat)
    }

    fn set_state_byte(&mut self, relative: u16, value: u8) -> (r: Result<(), StreamError>)
        requires old(self).invariant(), relative != crate::brotli_input::B3C_STREAM_PHASE,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.is_ok() ==> crate::brotli_input::b3c_scalar_byte_at(
                final(self).workspace@,
                (1u32 << final(self).budget.limits.max_window_bits) as u32,
                relative as int,
            ) == value,
            r.is_ok() ==> final(self).workspace@
                == old(self).workspace@.update(
                    crate::brotli_input::b3c_scalar_base(
                        (1u32 << old(self).budget.limits.max_window_bits) as u32,
                    ) + relative as int,
                    value,
                ),
    {
        proof { reveal(BrotliDecoder::valid); }
        let window_bytes = self.window_bytes();
        let result = crate::brotli_input::write_b3c_state_byte(
            self.workspace,
            window_bytes,
            relative,
            value,
        ).0;
        match result {
            Ok(()) => {
                proof {
                    reveal(BrotliDecoder::valid);
                    assert(crate::brotli_input::b3c_scalar_byte_at(
                        self.workspace@,
                        window_bytes,
                        crate::brotli_input::B3C_STREAM_PHASE as int,
                    ) == crate::brotli_input::b3c_scalar_byte_at(
                        old(self).workspace@,
                        window_bytes,
                        crate::brotli_input::B3C_STREAM_PHASE as int,
                    ));
                    assert(self.invariant());
                }
                Ok(())
            }
            Err(_) => {
                proof {
                    reveal(BrotliDecoder::valid);
                    assert(self.invariant());
                }
                Err(StreamError::InvalidFormat)
            }
        }
    }

    fn set_state_u16(&mut self, relative: u16, value: u16) -> (r: Result<(), StreamError>)
        requires old(self).invariant(), relative > crate::brotli_input::B3C_STREAM_PHASE,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
    {
        crate::brotli_input::write_b3c_state_u16(
            self.workspace,
            self.window_bytes(),
            relative,
            value,
        )
        .map_err(|_| StreamError::InvalidFormat)
    }

    fn set_state_u32(&mut self, relative: u16, value: u32) -> (r: Result<(), StreamError>)
        requires old(self).invariant(), relative > crate::brotli_input::B3C_STREAM_PHASE,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.is_ok() ==> crate::brotli_input::b3c_scalar_u32_at(
                final(self).workspace@,
                (1u32 << final(self).budget.limits.max_window_bits) as u32,
                relative as int,
            ) == value,
            r.is_ok() ==> {
                let at = crate::brotli_input::b3c_scalar_base(
                    (1u32 << old(self).budget.limits.max_window_bits) as u32,
                ) + relative as int;
                final(self).workspace@ == old(self).workspace@
                    .update(at, (value % 256) as u8)
                    .update(at + 1, ((value / 256) % 256) as u8)
                    .update(at + 2, ((value / 65_536) % 256) as u8)
                    .update(at + 3, (value / 16_777_216) as u8)
            },
    {
        crate::brotli_input::write_b3c_state_u32(
            self.workspace,
            self.window_bytes(),
            relative,
            value,
        ).0
        .map_err(|_| StreamError::InvalidFormat)
    }

    fn push_recent_distance(&mut self, distance: u32) -> (r: Result<(), StreamError>)
        requires
            old(self).valid(),
            distance > 0,
        ensures
            final(self).valid(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.is_ok() ==> {
                let window_bytes =
                    (1u32 << final(self).budget.limits.max_window_bits) as u32;
                let old_cursor = crate::brotli_input::b3c_scalar_byte_at(
                    old(self).workspace@,
                    window_bytes,
                    crate::brotli_input::B3C_RECENT_CURSOR as int,
                );
                &&& old_cursor < 4
                &&& crate::brotli_input::b3c_scalar_u32_at(
                    final(self).workspace@,
                    window_bytes,
                    (crate::brotli_input::B3C_RECENT_DISTANCES
                        + 4 * old_cursor as u16) as int,
                ) == distance
                &&& crate::brotli_input::b3c_scalar_byte_at(
                    final(self).workspace@,
                    window_bytes,
                    crate::brotli_input::B3C_RECENT_CURSOR as int,
                ) == if old_cursor == 3 { 0u8 } else { (old_cursor + 1) as u8 }
                &&& crate::brotli_input::b3c_scalar_byte_at(
                    final(self).workspace@,
                    window_bytes,
                    crate::brotli_input::B3C_COMMAND_DISTANCE_MODE as int,
                ) == 1
            },
    {
        let ghost initial_workspace = self.workspace@;
        let window_bytes = self.window_bytes();
        let cursor = match self.state_byte(crate::brotli_input::B3C_RECENT_CURSOR) {
            Ok(value) if value < 4 => value,
            _ => return Err(StreamError::InvalidFormat),
        };
        match self.set_state_u32(
            crate::brotli_input::B3C_RECENT_DISTANCES + 4 * cursor as u16,
            distance,
        ) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        let ghost after_distance = self.workspace@;
        proof {
            let ring_at = crate::brotli_input::b3c_scalar_base(window_bytes)
                + crate::brotli_input::B3C_RECENT_DISTANCES as int
                + 4 * cursor as int;
            assert(after_distance == initial_workspace
                .update(ring_at, (distance % 256) as u8)
                .update(ring_at + 1, ((distance / 256) % 256) as u8)
                .update(ring_at + 2, ((distance / 65_536) % 256) as u8)
                .update(ring_at + 3, (distance / 16_777_216) as u8));
        }
        let next_cursor = next_recent_cursor(cursor);
        match self.set_state_byte(
            crate::brotli_input::B3C_RECENT_CURSOR,
            next_cursor,
        ) {
            Ok(()) => {}
            Err(error) => return Err(error),
        }
        let ghost after_cursor = self.workspace@;
        proof {
            let cursor_at = crate::brotli_input::b3c_scalar_base(window_bytes)
                + crate::brotli_input::B3C_RECENT_CURSOR as int;
            assert(after_cursor == after_distance.update(cursor_at, next_cursor));
        }
        let result = self.set_state_byte(
            crate::brotli_input::B3C_COMMAND_DISTANCE_MODE,
            1,
        );
        proof {
            if result.is_ok() {
                reveal(crate::brotli_input::b3c_scalar_byte_at);
                reveal(crate::brotli_input::b3c_scalar_u32_at);
                reveal(crate::brotli_input::b3c_scalar_base);
                assert(crate::brotli_input::B3C_COMMAND_DISTANCE_MODE
                    < crate::brotli_input::B3C_RECENT_DISTANCES);
                assert(crate::brotli_input::B3C_RECENT_DISTANCES
                    + 4 * cursor as u16 + 4
                    <= crate::brotli_input::B3C_RECENT_CURSOR);
                assert(after_cursor == self.workspace@.update(
                    crate::brotli_input::b3c_scalar_base(window_bytes)
                        + crate::brotli_input::B3C_COMMAND_DISTANCE_MODE as int,
                    after_cursor[
                        crate::brotli_input::b3c_scalar_base(window_bytes)
                            + crate::brotli_input::B3C_COMMAND_DISTANCE_MODE as int
                    ],
                ));
                assert(after_distance.len() == self.workspace@.len());
                let mode_at = crate::brotli_input::b3c_scalar_base(window_bytes)
                    + crate::brotli_input::B3C_COMMAND_DISTANCE_MODE as int;
                assert(self.workspace@ == after_cursor.update(mode_at, 1));
                let ring_relative = crate::brotli_input::B3C_RECENT_DISTANCES
                    + 4 * cursor as u16;
                assert(crate::brotli_input::b3c_scalar_u32_at(
                    self.workspace@,
                    window_bytes,
                    ring_relative as int,
                ) == distance);
                assert(crate::brotli_input::b3c_scalar_byte_at(
                    self.workspace@,
                    window_bytes,
                    crate::brotli_input::B3C_RECENT_CURSOR as int,
                ) == if cursor == 3 { 0u8 } else { (cursor + 1) as u8 });
                assert(crate::brotli_input::b3c_scalar_byte_at(
                    self.workspace@,
                    window_bytes,
                    crate::brotli_input::B3C_COMMAND_DISTANCE_MODE as int,
                ) == 1);
            }
        }
        result
    }

    fn consume_metadata_byte(&mut self, remaining: u32) -> (r: Result<(), StreamError>)
        requires
            old(self).valid(),
            remaining > 0,
            old(self).budget.input_remaining > 0,
            old(self).budget.work_remaining >= 2,
            crate::brotli_input::b3c_scalar_u32_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_META_REMAINING as int,
            ) == remaining,
        ensures
            final(self).valid(),
            final(self).budget.limits == old(self).budget.limits,
            r.is_ok(),
            final(self).budget.input_remaining == old(self).budget.input_remaining - 1,
            final(self).budget.work_remaining == old(self).budget.work_remaining - 2,
            final(self).budget.output_remaining == old(self).budget.output_remaining,
            final(self).budget.calls_remaining == old(self).budget.calls_remaining,
            final(self).budget.initializations_remaining
                == old(self).budget.initializations_remaining,
            r.is_ok() ==> {
                let window_bytes =
                    (1u32 << old(self).budget.limits.max_window_bits) as u32;
                let at = crate::brotli_input::b3c_scalar_base(window_bytes)
                    + crate::brotli_input::B3C_META_REMAINING as int;
                let value = remaining - 1;
                final(self).workspace@ == old(self).workspace@
                    .update(at, (value % 256) as u8)
                    .update(at + 1, ((value / 256) % 256) as u8)
                    .update(at + 2, ((value / 65_536) % 256) as u8)
                    .update(at + 3, (value / 16_777_216) as u8)
            },
    {
        assert!(self.budget.charge_input(1));
        assert!(self.budget.charge_work(2));
        let result = crate::brotli_input::write_b3c_state_u32(
            self.workspace,
            self.window_bytes(),
            crate::brotli_input::B3C_META_REMAINING,
            remaining - 1,
        ).0.map_err(|_| StreamError::InvalidFormat);
        result
    }

    fn commit_eof_if_complete(
        &mut self,
        consumed: usize,
        input_len: usize,
        end: bool,
    )
        requires old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            if end && consumed == input_len {
                crate::brotli_input::b3c_scalar_byte_at(
                    final(self).workspace@,
                    (1u32 << final(self).budget.limits.max_window_bits) as u32,
                    crate::brotli_input::B3C_EOF_COMMITTED as int,
                ) == 1
            } else {
                crate::brotli_input::b3c_scalar_byte_at(
                    final(self).workspace@,
                    (1u32 << final(self).budget.limits.max_window_bits) as u32,
                    crate::brotli_input::B3C_EOF_COMMITTED as int,
                ) == crate::brotli_input::b3c_scalar_byte_at(
                    old(self).workspace@,
                    (1u32 << old(self).budget.limits.max_window_bits) as u32,
                    crate::brotli_input::B3C_EOF_COMMITTED as int,
                )
            },
    {
        if end && consumed == input_len {
            let window_bytes = self.window_bytes();
            let _ = crate::brotli_input::write_b3c_state_byte(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_EOF_COMMITTED,
                1,
            ).0;
        }
    }

    fn return_step(
        &mut self,
        input_len: usize,
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        status: Status,
    ) -> (r: Step)
        requires old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.consumed == consumed,
            r.produced == produced,
            r.status == status,
    {
        self.commit_eof_if_complete(consumed, input_len, end_of_input);
        Step { consumed, produced, status }
    }

    fn finish_meta_block(&mut self) -> (r: Result<(), StreamError>)
        requires old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
    {
        let window_bytes = self.window_bytes();
        let flags = crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_META_FLAGS,
        )
        .map_err(|_| StreamError::InvalidFormat)?;
        if flags & 1 != 0 {
            self.write_phase(7)
        } else {
            match crate::brotli_input::reset_serialized_meta_header(
                self.workspace,
                window_bytes,
            ) {
                Ok(()) => {}
                Err(error) => return Err(Self::map_core_failure(error)),
            }
            self.write_phase(1)
        }
    }

    #[verifier::spinoff_prover]
    fn emit_byte(
        &mut self,
        byte: u8,
        output: &mut [u8],
        produced: usize,
        consumes_input: bool,
    ) -> (r: (Result<(), StreamError>, Ghost<nat>))
        requires
            old(self).invariant(),
            produced < old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) != 5,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.0.is_ok() ==> {
                &&& final(self).budget.work_remaining
                    == old(self).budget.work_remaining - B3C_EMISSION_WRITE_WORK
                &&& final(self).budget.output_remaining
                    == old(self).budget.output_remaining - 1
                &&& final(self).budget.input_remaining
                    == old(self).budget.input_remaining
                        - if consumes_input { 1u64 } else { 0u64 }
            },
            final(self).budget.calls_remaining == old(self).budget.calls_remaining,
            final(self).budget.initializations_remaining
                == old(self).budget.initializations_remaining,
            r.0.is_err() ==> {
                &&& *final(self).budget == *old(self).budget
                &&& final(self).workspace@ == old(self).workspace@
            },
            r.0.is_ok() ==> {
                let w = (1u32 << old(self).budget.limits.max_window_bits) as u32;
                let base = crate::brotli_input::b3c_scalar_base(w);
                let before = old(self).workspace@;
                let position = crate::brotli_input::b3c_scalar_u32_at(
                    before, w, crate::brotli_input::B3C_WINDOW_POSITION as int,
                );
                let history = crate::brotli_input::b3c_scalar_u32_at(
                    before, w, crate::brotli_input::B3C_HISTORY_LENGTH as int,
                );
                let remaining = crate::brotli_input::b3c_scalar_u32_at(
                    before, w, crate::brotli_input::B3C_META_REMAINING as int,
                );
                let bits = crate::brotli_input::b3c_scalar_byte_at(
                    before, w, crate::brotli_input::B3C_STREAM_WINDOW_BITS as int,
                );
                let limit = (1u32 << bits) as nat - 16;
                let p = (if position + 1 == w { 0nat } else { position + 1 }) as u32;
                let h = (if history < limit { history + 1 } else { history }) as u32;
                let m = (remaining - 1) as u32;
                let total = before[base + 24] as nat
                    + 256 * before[base + 25] as nat
                    + 65_536 * before[base + 26] as nat
                    + 16_777_216 * before[base + 27] as nat
                    + 4_294_967_296 * before[base + 28] as nat
                    + 1_099_511_627_776 * before[base + 29] as nat
                    + 281_474_976_710_656 * before[base + 30] as nat
                    + 72_057_594_037_927_936 * before[base + 31] as nat;
                let t = (total + 1) as u64;
                &&& position < w
                &&& remaining > 0
                &&& 10 <= bits <= 24
                &&& total < 18_446_744_073_709_551_615nat
                &&& (history <= limit ==> h as nat <= limit)
                &&& final(self).workspace@ == before
                    .update(position as int, byte)
                    .update(base + 33, before[base + 32])
                    .update(base + 32, byte)
                    .update(base + 16, (p % 256) as u8)
                    .update(base + 17, ((p / 256) % 256) as u8)
                    .update(base + 18, ((p / 65_536) % 256) as u8)
                    .update(base + 19, (p / 16_777_216) as u8)
                    .update(base + 20, (h % 256) as u8)
                    .update(base + 21, ((h / 256) % 256) as u8)
                    .update(base + 22, ((h / 65_536) % 256) as u8)
                    .update(base + 23, (h / 16_777_216) as u8)
                    .update(base + 24, t as u8)
                    .update(base + 25, (t >> 8) as u8)
                    .update(base + 26, (t >> 16) as u8)
                    .update(base + 27, (t >> 24) as u8)
                    .update(base + 28, (t >> 32) as u8)
                    .update(base + 29, (t >> 40) as u8)
                    .update(base + 30, (t >> 48) as u8)
                    .update(base + 31, (t >> 56) as u8)
                    .update(base + 12, (m % 256) as u8)
                    .update(base + 13, ((m / 256) % 256) as u8)
                    .update(base + 14, ((m / 65_536) % 256) as u8)
                    .update(base + 15, (m / 16_777_216) as u8)
            },
            final(output)@.len() == old(output)@.len(),
            r.0.is_ok() ==> final(output)@[produced as int] == byte,
            r.0.is_err() ==> final(output)@ == old(output)@,
            forall|i: int| 0 <= i < old(output)@.len() && i != produced ==>
                final(output)@[i] == old(output)@[i],
            r.1@ == if r.0.is_ok() { 24nat } else { 0nat },
            r.0.is_ok() ==> final(self).budget.work_remaining as nat + r.1@
                == old(self).budget.work_remaining as nat,
    {
        let ghost mut e3_source_writes: nat = 0;
        let ghost initial_workspace = self.workspace@;
        if produced >= output.len() {
            return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes));
        }
        if (consumes_input && self.budget.input_remaining == 0)
            || self.budget.output_remaining == 0
            || self.budget.work_remaining < B3C_EMISSION_WRITE_WORK
        {
            return (Err(StreamError::ResourceLimit), Ghost(e3_source_writes));
        }
        let window_bytes = self.window_bytes();
        let position = match crate::brotli_input::read_b3c_state_u32(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_WINDOW_POSITION,
        )
        .map_err(|_| StreamError::InvalidFormat) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };
        let history = match crate::brotli_input::read_b3c_state_u32(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_HISTORY_LENGTH,
        )
        .map_err(|_| StreamError::InvalidFormat) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };
        let total = match crate::brotli_input::read_b3c_state_u64(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_TOTAL_PRODUCED,
        )
        .map_err(|_| StreamError::InvalidFormat) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };
        let remaining = match crate::brotli_input::read_b3c_state_u32(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_META_REMAINING,
        )
        .map_err(|_| StreamError::InvalidFormat) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };
        let stream_bits = match crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_STREAM_WINDOW_BITS,
        )
        .map_err(|_| StreamError::InvalidFormat) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };
        if position >= window_bytes || remaining == 0 || !(10..=24).contains(&stream_bits) {
            return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes));
        }
        proof { approved_window_bytes(stream_bits); }
        let history_limit = (1u32 << stream_bits) - 16;
        let next_position = if position + 1 == window_bytes { 0 } else { position + 1 };
        let next_history = if history < history_limit { history + 1 } else { history };
        proof {
            assert(next_history as nat == if history < history_limit {
                history as nat + 1
            } else { history as nat });
        }
        let next_total = match total.checked_add(1).ok_or(StreamError::ResourceLimit) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };

        proof { assert(next_total as nat == total as nat + 1); }
        if consumes_input {
            assert!(self.budget.charge_input(1));
        }
        assert!(self.budget.charge_output(1));
        assert!(self.budget.charge_work(B3C_EMISSION_WRITE_WORK));
        proof {
            assert(e3_source_writes == 0);
            assert(self.budget.work_remaining as nat + B3C_EMISSION_WRITE_WORK as nat
                == old(self).budget.work_remaining as nat);
        }
        output[produced] = byte;
        proof { e3_source_writes = e3_source_writes + 1; }
        proof { assert(e3_source_writes == 1); assert(output@[produced as int] == byte); }
        self.workspace[position as usize] = byte;
        proof { e3_source_writes = e3_source_writes + 1; }
        proof { assert(e3_source_writes == 2); assert(self.workspace@[position as int] == byte); }
        proof {
            reveal(BrotliDecoder::invariant);
            assert((position as int) < (window_bytes as int));
            assert((window_bytes as int)
                < crate::brotli_input::b3c_scalar_base(window_bytes));
            assert(crate::brotli_input::b3c_scalar_byte_at(
                self.workspace@,
                window_bytes,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == crate::brotli_input::b3c_scalar_byte_at(
                initial_workspace,
                window_bytes,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ));
            assert(self.invariant());
        }
        let previous = match crate::brotli_input::read_b3c_state_byte(
            self.workspace,
            window_bytes,
            crate::brotli_input::B3C_PREVIOUS_BYTE,
        )
        .map_err(|_| StreamError::InvalidFormat) {
            Ok(value) => value,
            Err(error) => return (Err(error), Ghost(e3_source_writes)),
        };
        {
            let (e3_result, Ghost(e3_child_writes)) = crate::brotli_input::write_b3c_state_byte(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE,
                previous,
            );
            proof { e3_source_writes = e3_source_writes + e3_child_writes; }
            match e3_result {
                Ok(()) => (),
                Err(_) => return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes)),
            }
        }
        proof { assert(e3_source_writes == 3); assert(crate::brotli_input::b3c_scalar_byte_at(self.workspace@, window_bytes, crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE as int) == previous); }
        {
            let (e3_result, Ghost(e3_child_writes)) = crate::brotli_input::write_b3c_state_byte(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_PREVIOUS_BYTE,
                byte,
            );
            proof { e3_source_writes = e3_source_writes + e3_child_writes; }
            match e3_result {
                Ok(()) => (),
                Err(_) => return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes)),
            }
        }
        proof { assert(e3_source_writes == 4); assert(crate::brotli_input::b3c_scalar_byte_at(self.workspace@, window_bytes, crate::brotli_input::B3C_PREVIOUS_BYTE as int) == byte); }
        {
            let (e3_result, Ghost(e3_child_writes)) = crate::brotli_input::write_b3c_state_u32(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_WINDOW_POSITION,
                next_position,
            );
            proof { e3_source_writes = e3_source_writes + e3_child_writes; }
            match e3_result {
                Ok(()) => (),
                Err(_) => return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes)),
            }
        }
        proof { assert(e3_source_writes == 8); assert(crate::brotli_input::b3c_scalar_byte_at(self.workspace@, window_bytes, crate::brotli_input::B3C_WINDOW_POSITION as int) == (next_position % 256) as u8); }
        {
            let (e3_result, Ghost(e3_child_writes)) = crate::brotli_input::write_b3c_state_u32(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_HISTORY_LENGTH,
                next_history,
            );
            proof { e3_source_writes = e3_source_writes + e3_child_writes; }
            match e3_result {
                Ok(()) => (),
                Err(_) => return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes)),
            }
        }
        proof { assert(e3_source_writes == 12);  }
        {
            let (e3_result, Ghost(e3_child_writes)) = crate::brotli_input::write_b3c_state_u64(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_TOTAL_PRODUCED,
                next_total,
            );
            proof { e3_source_writes = e3_source_writes + e3_child_writes; }
            match e3_result {
                Ok(()) => (),
                Err(_) => return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes)),
            }
        }
        proof { assert(e3_source_writes == 20);  }
        {
            let (e3_result, Ghost(e3_child_writes)) = crate::brotli_input::write_b3c_state_u32(
                self.workspace,
                window_bytes,
                crate::brotli_input::B3C_META_REMAINING,
                remaining - 1,
            );
            proof { e3_source_writes = e3_source_writes + e3_child_writes; }
            match e3_result {
                Ok(()) => (),
                Err(_) => return (Err(StreamError::InvalidFormat), Ghost(e3_source_writes)),
            }
        }
        proof { assert(e3_source_writes == 24); assert(crate::brotli_input::b3c_scalar_byte_at(self.workspace@, window_bytes, crate::brotli_input::B3C_META_REMAINING as int) == ((remaining - 1) % 256) as u8); }
        (Ok(()), Ghost(e3_source_writes))
    }

    fn emit_uncompressed_byte(
        &mut self,
        byte: u8,
        output: &mut [u8],
        produced: usize,
    ) -> (r: (Result<(), StreamError>, Ghost<nat>))
        requires
            old(self).invariant(),
            produced < old(output)@.len(),
            old(self).budget.input_remaining > 0,
            old(self).budget.output_remaining > 0,
            old(self).budget.work_remaining >= 8,
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 4,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            r.0.is_ok() ==> {
                &&& final(self).budget.input_remaining
                    == old(self).budget.input_remaining - 1
                &&& final(self).budget.output_remaining
                    == old(self).budget.output_remaining - 1
                &&& final(self).budget.work_remaining
                    == old(self).budget.work_remaining - B3C_EMISSION_WRITE_WORK
            },
            final(self).budget.calls_remaining == old(self).budget.calls_remaining,
            final(self).budget.initializations_remaining
                == old(self).budget.initializations_remaining,
            r.0.is_err() ==> {
                &&& *final(self).budget == *old(self).budget
                &&& final(self).workspace@ == old(self).workspace@
            },
            r.0.is_ok() ==> {
                let w = (1u32 << old(self).budget.limits.max_window_bits) as u32;
                let base = crate::brotli_input::b3c_scalar_base(w);
                let before = old(self).workspace@;
                let position = crate::brotli_input::b3c_scalar_u32_at(
                    before, w, crate::brotli_input::B3C_WINDOW_POSITION as int,
                );
                let history = crate::brotli_input::b3c_scalar_u32_at(
                    before, w, crate::brotli_input::B3C_HISTORY_LENGTH as int,
                );
                let remaining = crate::brotli_input::b3c_scalar_u32_at(
                    before, w, crate::brotli_input::B3C_META_REMAINING as int,
                );
                let bits = crate::brotli_input::b3c_scalar_byte_at(
                    before, w, crate::brotli_input::B3C_STREAM_WINDOW_BITS as int,
                );
                let limit = (1u32 << bits) as nat - 16;
                let p = (if position + 1 == w { 0nat } else { position + 1 }) as u32;
                let h = (if history < limit { history + 1 } else { history }) as u32;
                let m = (remaining - 1) as u32;
                let total = before[base + 24] as nat
                    + 256 * before[base + 25] as nat
                    + 65_536 * before[base + 26] as nat
                    + 16_777_216 * before[base + 27] as nat
                    + 4_294_967_296 * before[base + 28] as nat
                    + 1_099_511_627_776 * before[base + 29] as nat
                    + 281_474_976_710_656 * before[base + 30] as nat
                    + 72_057_594_037_927_936 * before[base + 31] as nat;
                let t = (total + 1) as u64;
                &&& position < w
                &&& remaining > 0
                &&& 10 <= bits <= 24
                &&& total < 18_446_744_073_709_551_615nat
                &&& (history <= limit ==> h as nat <= limit)
                &&& final(self).workspace@ == before
                    .update(position as int, byte)
                    .update(base + 33, before[base + 32])
                    .update(base + 32, byte)
                    .update(base + 16, (p % 256) as u8)
                    .update(base + 17, ((p / 256) % 256) as u8)
                    .update(base + 18, ((p / 65_536) % 256) as u8)
                    .update(base + 19, (p / 16_777_216) as u8)
                    .update(base + 20, (h % 256) as u8)
                    .update(base + 21, ((h / 256) % 256) as u8)
                    .update(base + 22, ((h / 65_536) % 256) as u8)
                    .update(base + 23, (h / 16_777_216) as u8)
                    .update(base + 24, t as u8)
                    .update(base + 25, (t >> 8) as u8)
                    .update(base + 26, (t >> 16) as u8)
                    .update(base + 27, (t >> 24) as u8)
                    .update(base + 28, (t >> 32) as u8)
                    .update(base + 29, (t >> 40) as u8)
                    .update(base + 30, (t >> 48) as u8)
                    .update(base + 31, (t >> 56) as u8)
                    .update(base + 12, (m % 256) as u8)
                    .update(base + 13, ((m / 256) % 256) as u8)
                    .update(base + 14, ((m / 65_536) % 256) as u8)
                    .update(base + 15, (m / 16_777_216) as u8)
            },
            final(output)@.len() == old(output)@.len(),
            r.0.is_ok() ==> final(output)@[produced as int] == byte,
            r.0.is_err() ==> final(output)@ == old(output)@,
            forall|i: int| 0 <= i < old(output)@.len() && i != produced ==>
                final(output)@[i] == old(output)@[i],
            r.1@ == if r.0.is_ok() { 24nat } else { 0nat },
            r.0.is_ok() ==> final(self).budget.work_remaining as nat + r.1@
                == old(self).budget.work_remaining as nat,
    {
        let ghost mut e3_source_writes: nat = 0;
        let (result, Ghost(e3_child_writes)) = self.emit_byte(byte, output, produced, true);
        proof { e3_source_writes = e3_source_writes + e3_child_writes; }
        (result, Ghost(e3_source_writes))
    }


    fn fail_transition(
        &mut self,
        error: StreamError,
        consumed: usize,
        produced: usize,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).budget.valid(),
            crate::brotli_input::b3c_workspace_shape(
                old(self).workspace@.len() as nat,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
            ),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            match r {
                Ok(_) => false,
                Err(step) => {
                    &&& step.consumed == consumed
                    &&& step.produced == produced
                    &&& matches!(step.status, Status::Failed(_))
                },
            },
    {
        Err(self.fail(error, consumed, produced))
    }

    fn return_transition(
        &mut self,
        input_len: usize,
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        status: Status,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            match r {
                Ok(_) => false,
                Err(step) => {
                    &&& step.consumed == consumed
                    &&& step.produced == produced
                    &&& step.status == status
                },
            },
    {
        Err(self.return_step(
            input_len,
            end_of_input,
            consumed,
            produced,
            status,
        ))
    }

    #[verifier::rlimit(90)]
    fn step_body_phase_zero(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase == 0,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            0 => {
                let meta_remaining = match self.state_u32(
                    crate::brotli_input::B3C_META_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                if meta_remaining == 0 {
                    if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        15,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else {
                    let command_remaining = match
                        crate::brotli_input::body_block_remaining(
                            self.workspace,
                            self.window_bytes(),
                            1,
                        )
                    {
                        Ok(value) => value,
                        Err(error) => {
                            return self.fail_transition(
                                Self::map_core_failure(error),
                                consumed,
                                produced,
                            );
                        }
                    };
                    if command_remaining == 0 {
                        let switch =
                            crate::brotli_input::advance_serialized_body_block_switch(
                                self.workspace,
                                self.window_bytes(),
                                self.budget,
                                1,
                                &input[consumed..],
                                self.committed_eof() || end_of_input,
                            );
                        consumed += switch.consumed;
                        match switch.status {
                            crate::brotli_input::BodySwitchStatus::NeedInput => {
                                return self.return_transition(
                                    input.len(),
                                    end_of_input,
                                    consumed,
                                    produced,
                                    Status::NeedInput,
                                );
                            }
                            crate::brotli_input::BodySwitchStatus::Complete { .. } => {
                                return Ok((consumed, produced));
                            }
                            crate::brotli_input::BodySwitchStatus::Failed(error) => {
                                return self.fail_transition(
                                    Self::map_core_failure(error),
                                    consumed,
                                    produced,
                                );
                            }
                        }
                    }
                    let tree = match crate::brotli_input::body_active_block_type(
                        self.workspace,
                        self.window_bytes(),
                        1,
                    ) {
                        Ok(value) => value,
                        Err(error) => {
                            return self.fail_transition(
                                Self::map_core_failure(error),
                                consumed,
                                produced,
                            );
                        }
                    };
                    let final_input = self.committed_eof() || end_of_input;
                    let symbol_step =
                        crate::brotli_input::advance_serialized_body_symbol(
                            self.workspace,
                            self.window_bytes(),
                            self.budget,
                            crate::brotli_prefix::TreeRegion::Command,
                            tree,
                            704,
                            &input[consumed..],
                            final_input,
                        );
                    consumed += symbol_step.consumed;
                    let symbol = match symbol_step.status {
                        crate::brotli_input::BodySymbolStatus::NeedInput => {
                            return self.return_transition(
                                input.len(),
                                end_of_input,
                                consumed,
                                produced,
                                Status::NeedInput,
                            );
                        }
                        crate::brotli_input::BodySymbolStatus::Failed(error) => {
                            return self.fail_transition(
                                Self::map_core_failure(error),
                                consumed,
                                produced,
                            );
                        }
                        crate::brotli_input::BodySymbolStatus::Symbol(value) => value,
                    };
                    if let Err(error) =
                        crate::brotli_input::body_decrement_block_remaining(
                            self.workspace,
                            self.window_bytes(),
                            1,
                        )
                    {
                        return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        );
                    }
                    let table_entry = crate::brotli_data::command_entry(symbol);
                    let entry = crate::brotli_data::command_entry_formula(symbol);
                    if entry != table_entry {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    let distance_mode = if entry.distance_mode == 0 { 0 } else { 1 };
                    if self.set_state_u16(
                        crate::brotli_input::B3C_COMMAND_SYMBOL,
                        symbol,
                    ).is_err()
                        || self.set_state_byte(
                            crate::brotli_input::B3C_INSERT_EXTRA_WIDTH,
                            entry.insert_extra_bits,
                        ).is_err()
                        || self.set_state_byte(
                            crate::brotli_input::B3C_COPY_EXTRA_WIDTH,
                            entry.copy_extra_bits,
                        ).is_err()
                        || self.set_state_u32(
                            crate::brotli_input::B3C_INSERT_LENGTH,
                            entry.insert_offset as u32,
                        ).is_err()
                        || self.set_state_u32(
                            crate::brotli_input::B3C_COPY_LENGTH,
                            entry.copy_offset as u32,
                        ).is_err()
                        || self.set_state_byte(
                            crate::brotli_input::B3C_COMMAND_DISTANCE_MODE,
                            distance_mode,
                        ).is_err()
                        || self.set_state_byte(
                            crate::brotli_input::B3C_DISTANCE_CONTEXT,
                            command_copy_length_context(entry.copy_offset),
                        ).is_err()
                        || self.set_state_byte(
                            crate::brotli_input::B3C_BODY_PHASE,
                            4,
                        ).is_err()
                    {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                }
            }
            _ => {
                return self.fail_transition(
                    StreamError::InvalidFormat,
                    consumed,
                    produced,
                );
            }
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(60)]
    fn step_body_phase_lengths(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase == 4 || body_phase == 5,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            4 | 5 => {
                let (width_field, length_field, next_phase) = if body_phase == 4 {
                    (
                        crate::brotli_input::B3C_INSERT_EXTRA_WIDTH,
                        crate::brotli_input::B3C_INSERT_LENGTH,
                        5u8,
                    )
                } else {
                    (
                        crate::brotli_input::B3C_COPY_EXTRA_WIDTH,
                        crate::brotli_input::B3C_COPY_LENGTH,
                        6u8,
                    )
                };
                let width = match self.state_byte(width_field) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                let final_input = self.committed_eof() || end_of_input;
                let bits_step = crate::brotli_input::advance_serialized_body_bits(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                    width,
                    &input[consumed..],
                    final_input,
                );
                consumed += bits_step.consumed;
                let suffix = match bits_step.status {
                    crate::brotli_input::BodyBitsStatus::NeedInput => {
                        return self.return_transition(
                            input.len(),
                            end_of_input,
                            consumed,
                            produced,
                            Status::NeedInput,
                        );
                    }
                    crate::brotli_input::BodyBitsStatus::Failed(error) => {
                        return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        );
                    }
                    crate::brotli_input::BodyBitsStatus::Value(value) => value,
                };
                let base = match self.state_u32(length_field) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                let length = match base.checked_add(suffix) {
                    Some(value) => value,
                    None => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                if self.set_state_u32(length_field, length).is_err()
                    || (body_phase == 4
                        && self.set_state_u32(
                            crate::brotli_input::B3C_INSERT_REMAINING,
                            length,
                        ).is_err())
                    || (body_phase == 5
                        && self.set_state_u32(
                            crate::brotli_input::B3C_COPY_REMAINING,
                            length,
                        ).is_err())
                    || self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        next_phase,
                    ).is_err()
                {
                    return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    );
                }
                if body_phase == 4 {
                    let meta_remaining = match self.state_u32(
                        crate::brotli_input::B3C_META_REMAINING,
                    ) {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    };
                    if length > meta_remaining {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                }
            }
            _ => {
                return self.fail_transition(
                    StreamError::InvalidFormat,
                    consumed,
                    produced,
                );
            }
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(90)]
    fn step_body_emit_literal(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        insert_remaining: u32,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            insert_remaining > 0,
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        let literal_remaining = match
            crate::brotli_input::body_block_remaining(
                self.workspace,
                self.window_bytes(),
                0,
            )
        {
            Ok(value) => value,
            Err(error) => {
                return self.fail_transition(
                    Self::map_core_failure(error),
                    consumed,
                    produced,
                );
            }
        };
        if literal_remaining == 0 {
            let switch =
                crate::brotli_input::advance_serialized_body_block_switch(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                    0,
                    &input[consumed..],
                    self.committed_eof() || end_of_input,
                );
            consumed += switch.consumed;
            match switch.status {
                crate::brotli_input::BodySwitchStatus::NeedInput => {
                    return self.return_transition(
                        input.len(),
                        end_of_input,
                        consumed,
                        produced,
                        Status::NeedInput,
                    );
                }
                crate::brotli_input::BodySwitchStatus::Complete { .. } => {
                    return Ok((consumed, produced));
                }
                crate::brotli_input::BodySwitchStatus::Failed(error) => {
                    return self.fail_transition(
                        Self::map_core_failure(error),
                        consumed,
                        produced,
                    );
                }
            }
        }
        let block_type = match
            crate::brotli_input::body_active_block_type(
                self.workspace,
                self.window_bytes(),
                0,
            )
        {
            Ok(value) => value,
            Err(error) => {
                return self.fail_transition(
                    Self::map_core_failure(error),
                    consumed,
                    produced,
                );
            }
        };
        let block_count = match crate::brotli_input::body_block_count(
            self.workspace,
            self.window_bytes(),
            0,
        ) {
            Ok(value) => value,
            Err(error) => {
                return self.fail_transition(
                    Self::map_core_failure(error),
                    consumed,
                    produced,
                );
            }
        };
        if block_type >= block_count {
            return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            );
        }
        let mode_at = self.window_bytes() as u64
            + crate::brotli_prefix::LITERAL_CONTEXT_MODES_OFFSET as u64
            + block_type as u64;
        if mode_at >= self.workspace.len() as u64 {
            return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            );
        }
        let mode = self.workspace[mode_at as usize];
        if mode >= 4 {
            return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            );
        }
        let previous = match self.state_byte(
            crate::brotli_input::B3C_PREVIOUS_BYTE,
        ) {
            Ok(value) => value,
            Err(error) => return self.fail_transition(error, consumed, produced),
        };
        let second_previous = match self.state_byte(
            crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE,
        ) {
            Ok(value) => value,
            Err(error) => return self.fail_transition(error, consumed, produced),
        };
        let context = selected_literal_context(
            mode,
            previous,
            second_previous,
        );
        let literal_trees = match
            crate::brotli_input::body_literal_tree_count(
                self.workspace,
                self.window_bytes(),
            )
        {
            Ok(value) => value,
            Err(error) => return self.fail_transition(
                Self::map_core_failure(error),
                consumed,
                produced,
            ),
        };
        let map_len = match block_count.checked_mul(64) {
            Some(value) => value,
            None => return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            ),
        };
        let map_base = match block_type.checked_mul(64) {
            Some(value) => value,
            None => return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            ),
        };
        let map_index = match map_base.checked_add(context as u16) {
            Some(value) if value < map_len => value,
            _ => return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            ),
        };
        let tree_at = self.window_bytes() as u64
            + crate::brotli_prefix::LITERAL_CONTEXT_MAP_OFFSET as u64
            + map_index as u64;
        if tree_at >= self.workspace.len() as u64 {
            return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            );
        }
        let tree = self.workspace[tree_at as usize] as u16;
        if tree >= literal_trees {
            return self.fail_transition(
                StreamError::InvalidFormat,
                consumed,
                produced,
            );
        }
        let output_block = output_block_reason(
            self.budget.output_remaining,
            self.budget.work_remaining,
            produced < output.len(),
        );
        if output_block == 1 {
            return self.fail_transition(StreamError::ResourceLimit, consumed, produced);
        }
        if output_block == 2 {
            return self.return_transition(
                input.len(),
                end_of_input,
                consumed,
                produced,
                Status::NeedOutput,
            );
        }
        let final_input = self.committed_eof() || end_of_input;
        let symbol_step =
            crate::brotli_input::advance_serialized_body_symbol(
                self.workspace,
                self.window_bytes(),
                self.budget,
                crate::brotli_prefix::TreeRegion::Literal,
                tree,
                256,
                &input[consumed..],
                final_input,
            );
        consumed += symbol_step.consumed;
        let literal = match symbol_step.status {
            crate::brotli_input::BodySymbolStatus::NeedInput => {
                return self.return_transition(
                    input.len(),
                    end_of_input,
                    consumed,
                    produced,
                    Status::NeedInput,
                );
            }
            crate::brotli_input::BodySymbolStatus::Failed(error) => {
                return self.fail_transition(
                    Self::map_core_failure(error),
                    consumed,
                    produced,
                );
            }
            crate::brotli_input::BodySymbolStatus::Symbol(value) => {
                value as u8
            }
        };
        if let Err(error) =
            crate::brotli_input::body_decrement_block_remaining(
                self.workspace,
                self.window_bytes(),
                0,
            )
        {
            return self.fail_transition(
                Self::map_core_failure(error),
                consumed,
                produced,
            );
        }
        if let Err(error) =
            self.emit_byte(literal, output, produced, false).0
        {
            return self.fail_transition(error, consumed, produced);
        }
        proof {
            assert(produced < output.len());
            assert(output.len() <= usize::MAX);
            assert(produced < usize::MAX);
        }
        produced += 1;
        if let Err(error) = self.set_state_u32(
            crate::brotli_input::B3C_INSERT_REMAINING,
            insert_remaining - 1,
        ) {
            return self.fail_transition(error, consumed, produced);
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(90)]
    fn step_body_phase_literals(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase == 6 || body_phase == 7,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            6 | 7 => {
                let insert_remaining = match self.state_u32(
                    crate::brotli_input::B3C_INSERT_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                if insert_remaining == 0 {
                    let meta_remaining = match self.state_u32(
                        crate::brotli_input::B3C_META_REMAINING,
                    ) {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    };
                    let next = phase_after_completed_insert(meta_remaining);
                    if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        next,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else {
                    return self.step_body_emit_literal(
                        input,
                        output,
                        end_of_input,
                        consumed,
                        produced,
                        insert_remaining,
                    );
                }
            }
            _ => {
                return self.fail_transition(
                    StreamError::InvalidFormat,
                    consumed,
                    produced,
                );
            }
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(90)]
    #[verifier::spinoff_prover]
    fn step_body_phase_distance_symbol(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase == 8,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            8 => {
                let mode = match self.state_byte(
                    crate::brotli_input::B3C_COMMAND_DISTANCE_MODE,
                ) {
                    Ok(value) if value <= 2 => value,
                    _ => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                if mode == 0 {
                    let cursor = match self.state_byte(
                        crate::brotli_input::B3C_RECENT_CURSOR,
                    ) {
                        Ok(value) if value < 4 => value,
                        _ => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    let index = (cursor + 3) & 3;
                    let distance = match self.state_u32(
                        crate::brotli_input::B3C_RECENT_DISTANCES
                            + 4 * index as u16,
                    ) {
                        Ok(value) if value > 0 => value,
                        _ => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    if self.set_state_u32(
                        crate::brotli_input::B3C_RESOLVED_DISTANCE,
                        distance,
                    ).is_err()
                        || self.set_state_byte(
                            crate::brotli_input::B3C_BODY_PHASE,
                            11,
                        ).is_err()
                    {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                } else {
                    let distance_remaining = match
                        crate::brotli_input::body_block_remaining(
                            self.workspace,
                            self.window_bytes(),
                            2,
                        )
                    {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        ),
                    };
                    if distance_remaining == 0 {
                        let switch =
                            crate::brotli_input::advance_serialized_body_block_switch(
                                self.workspace,
                                self.window_bytes(),
                                self.budget,
                                2,
                                &input[consumed..],
                                self.committed_eof() || end_of_input,
                            );
                        consumed += switch.consumed;
                        match switch.status {
                            crate::brotli_input::BodySwitchStatus::NeedInput => {
                                return self.return_transition(
                                    input.len(),
                                    end_of_input,
                                    consumed,
                                    produced,
                                    Status::NeedInput,
                                );
                            }
                            crate::brotli_input::BodySwitchStatus::Complete { .. } => {
                                return Ok((consumed, produced));
                            }
                            crate::brotli_input::BodySwitchStatus::Failed(error) => {
                                return self.fail_transition(
                                    Self::map_core_failure(error),
                                    consumed,
                                    produced,
                                );
                            }
                        }
                    }
                    let block_type = match
                        crate::brotli_input::body_active_block_type(
                            self.workspace,
                            self.window_bytes(),
                            2,
                        )
                    {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        ),
                    };
                    let block_count = match crate::brotli_input::body_block_count(
                        self.workspace,
                        self.window_bytes(),
                        2,
                    ) {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        ),
                    };
                    let context = match self.state_byte(
                        crate::brotli_input::B3C_DISTANCE_CONTEXT,
                    ) {
                        Ok(value) if value < 4 => value,
                        _ => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    let tree_count = match
                        crate::brotli_input::body_distance_tree_count(
                            self.workspace,
                            self.window_bytes(),
                        )
                    {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        ),
                    };
                    let map_len = match block_count.checked_mul(4) {
                        Some(value) => value,
                        None => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    if block_type >= block_count {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    let map_base = match block_type.checked_mul(4) {
                        Some(value) => value,
                        None => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    let map_index = match map_base.checked_add(context as u16) {
                        Some(value) if value < map_len => value,
                        _ => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    let tree_at = self.window_bytes() as u64
                        + crate::brotli_prefix::DISTANCE_CONTEXT_MAP_OFFSET as u64
                        + map_index as u64;
                    if tree_at >= self.workspace.len() as u64 {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    let tree = self.workspace[tree_at as usize] as u16;
                    if tree >= tree_count {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    let alphabet = match
                        crate::brotli_input::body_distance_alphabet_size(
                            self.workspace,
                            self.window_bytes(),
                        )
                    {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        ),
                    };
                    let final_input = self.committed_eof() || end_of_input;
                    let symbol_step =
                        crate::brotli_input::advance_serialized_body_symbol(
                            self.workspace,
                            self.window_bytes(),
                            self.budget,
                            crate::brotli_prefix::TreeRegion::Distance,
                            tree,
                            alphabet,
                            &input[consumed..],
                            final_input,
                        );
                    consumed += symbol_step.consumed;
                    let symbol = match symbol_step.status {
                        crate::brotli_input::BodySymbolStatus::NeedInput => {
                            return self.return_transition(
                                input.len(),
                                end_of_input,
                                consumed,
                                produced,
                                Status::NeedInput,
                            );
                        }
                        crate::brotli_input::BodySymbolStatus::Failed(error) => {
                            return self.fail_transition(
                                Self::map_core_failure(error),
                                consumed,
                                produced,
                            );
                        }
                        crate::brotli_input::BodySymbolStatus::Symbol(value) => value,
                    };
                    if let Err(error) =
                        crate::brotli_input::body_decrement_block_remaining(
                            self.workspace,
                            self.window_bytes(),
                            2,
                        )
                    {
                        return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        );
                    }
                    if self.set_state_u16(
                        crate::brotli_input::B3C_DISTANCE_SYMBOL,
                        symbol,
                    ).is_err()
                    {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    if symbol < 16 {
                        let cursor = match self.state_byte(
                            crate::brotli_input::B3C_RECENT_CURSOR,
                        ) {
                            Ok(value) if value < 4 => value,
                            _ => return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            ),
                        };
                        let index = (cursor
                            + crate::brotli_data::distance_index_delta(symbol as u8)) & 3;
                        let base = match self.state_u32(
                            crate::brotli_input::B3C_RECENT_DISTANCES
                                + 4 * index as u16,
                        ) {
                            Ok(value) => value as i64,
                            Err(error) => return self.fail_transition(error, consumed, produced),
                        };
                        let distance = base
                            + crate::brotli_data::distance_value_delta(symbol as u8) as i64;
                        if distance <= 0 || distance > u32::MAX as i64 {
                            return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            );
                        }
                        let push_mode = if symbol == 0 { 1 } else { 2 };
                        if self.set_state_u32(
                            crate::brotli_input::B3C_RESOLVED_DISTANCE,
                            distance as u32,
                        ).is_err()
                            || self.set_state_byte(
                                crate::brotli_input::B3C_COMMAND_DISTANCE_MODE,
                                push_mode,
                            ).is_err()
                            || self.set_state_byte(
                                crate::brotli_input::B3C_BODY_PHASE,
                                11,
                            ).is_err()
                        {
                            return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            );
                        }
                    } else {
                        let (width, offset) = match
                            crate::brotli_input::body_distance_lut_entry(
                                self.workspace,
                                self.window_bytes(),
                                symbol,
                            )
                        {
                            Ok(value) => value,
                            Err(error) => return self.fail_transition(
                                Self::map_core_failure(error),
                                consumed,
                                produced,
                            ),
                        };
                        if self.set_state_byte(
                            crate::brotli_input::B3C_DISTANCE_EXTRA_WIDTH,
                            width,
                        ).is_err()
                            || self.set_state_u32(
                                crate::brotli_input::B3C_RESOLVED_DISTANCE,
                                offset,
                            ).is_err()
                            || self.set_state_byte(
                                crate::brotli_input::B3C_COMMAND_DISTANCE_MODE,
                                2,
                            ).is_err()
                            || self.set_state_byte(
                                crate::brotli_input::B3C_BODY_PHASE,
                                10,
                            ).is_err()
                        {
                            return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            );
                        }
                    }
                }
            }
            _ => {
                return self.fail_transition(
                    StreamError::InvalidFormat,
                    consumed,
                    produced,
                );
            }
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(60)]
    fn step_body_phase_copy_setup(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase == 10 || body_phase == 11 || body_phase == 12,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            10 => {
                let width = match self.state_byte(
                    crate::brotli_input::B3C_DISTANCE_EXTRA_WIDTH,
                ) {
                    Ok(value) if value <= 24 => value,
                    _ => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                let final_input = self.committed_eof() || end_of_input;
                let bits_step = crate::brotli_input::advance_serialized_body_bits(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                    width,
                    &input[consumed..],
                    final_input,
                );
                consumed += bits_step.consumed;
                let suffix = match bits_step.status {
                    crate::brotli_input::BodyBitsStatus::NeedInput => {
                        return self.return_transition(
                            input.len(),
                            end_of_input,
                            consumed,
                            produced,
                            Status::NeedInput,
                        );
                    }
                    crate::brotli_input::BodyBitsStatus::Failed(error) => {
                        return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        );
                    }
                    crate::brotli_input::BodyBitsStatus::Value(value) => value,
                };
                let base = match self.state_u32(
                    crate::brotli_input::B3C_RESOLVED_DISTANCE,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                let postfix = match
                    crate::brotli_input::body_distance_postfix_bits(
                        self.workspace,
                        self.window_bytes(),
                    )
                {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(
                        Self::map_core_failure(error),
                        consumed,
                        produced,
                    ),
                };
                let extra = match postfix {
                    0 => Some(suffix),
                    1 => suffix.checked_mul(2),
                    2 => suffix.checked_mul(4),
                    3 => suffix.checked_mul(8),
                    _ => None,
                };
                let extra = match extra {
                    Some(value) => value,
                    None => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                let distance = match base.checked_add(extra) {
                    Some(value) if value > 0 => value,
                    _ => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                if self.set_state_u32(
                    crate::brotli_input::B3C_RESOLVED_DISTANCE,
                    distance,
                ).is_err()
                    || self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        11,
                    ).is_err()
                {
                    return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    );
                }
            }
            11 => {
                let meta_remaining = match self.state_u32(
                    crate::brotli_input::B3C_META_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                if meta_remaining == 0 {
                    if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        15,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else {
                    let distance = match self.state_u32(
                        crate::brotli_input::B3C_RESOLVED_DISTANCE,
                    ) {
                        Ok(value) if value > 0 => value,
                        _ => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    let history = match self.state_u32(
                        crate::brotli_input::B3C_HISTORY_LENGTH,
                    ) {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    };
                    let copy_length = match self.state_u32(
                        crate::brotli_input::B3C_COPY_LENGTH,
                    ) {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    };
                    let next_copy_phase = copy_setup_phase(distance, history);
                    if next_copy_phase == 12 {
                        if copy_length > meta_remaining {
                            return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            );
                        }
                        let mode = match self.state_byte(
                            crate::brotli_input::B3C_COMMAND_DISTANCE_MODE,
                        ) {
                            Ok(value) if value <= 2 => value,
                            _ => return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            ),
                        };
                        if mode == 2 {
                            if self.push_recent_distance(distance).is_err() {
                                return self.fail_transition(
                                    StreamError::InvalidFormat,
                                    consumed,
                                    produced,
                                );
                            }
                        }
                        if self.set_state_u32(
                            crate::brotli_input::B3C_COPY_REMAINING,
                            copy_length,
                        ).is_err()
                            || self.set_state_byte(
                                crate::brotli_input::B3C_BODY_PHASE,
                                next_copy_phase,
                            ).is_err()
                        {
                            return self.fail_transition(
                                StreamError::InvalidFormat,
                                consumed,
                                produced,
                            );
                        }
                    } else if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        next_copy_phase,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                }
            }
            12 => {
                let copy_remaining = match self.state_u32(
                    crate::brotli_input::B3C_COPY_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                if copy_remaining == 0 {
                    if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        0,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else {
                    let position = match self.state_u32(
                        crate::brotli_input::B3C_WINDOW_POSITION,
                    ) {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    };
                    let distance = match self.state_u32(
                        crate::brotli_input::B3C_RESOLVED_DISTANCE,
                    ) {
                        Ok(value) if value > 0 && value <= self.window_bytes() => value,
                        _ => return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        ),
                    };
                    let window_bytes = self.window_bytes();
                    if position >= window_bytes {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    let output_block = output_block_reason(
                        self.budget.output_remaining,
                        self.budget.work_remaining,
                        produced < output.len(),
                    );
                    if output_block == 1 {
                        return self.fail_transition(
                            StreamError::ResourceLimit,
                            consumed,
                            produced,
                        );
                    }
                    if output_block == 2 {
                        return self.return_transition(
                            input.len(),
                            end_of_input,
                            consumed,
                            produced,
                            Status::NeedOutput,
                        );
                    }
                    let source = overlap_source_position(position, distance, window_bytes);
                    let byte = self.workspace[source as usize];
                    if let Err(error) = self.emit_byte(byte, output, produced, false).0 {
                        return self.fail_transition(error, consumed, produced);
                    }
                    produced += 1;
                    if let Err(error) = self.set_state_u32(
                        crate::brotli_input::B3C_COPY_REMAINING,
                        copy_remaining - 1,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                    if copy_remaining == 1 {
                        let next = match self.state_u32(
                            crate::brotli_input::B3C_META_REMAINING,
                        ) {
                            Ok(0) => 15,
                            Ok(_) => 0,
                            Err(error) => return self.fail_transition(error, consumed, produced),
                        };
                        if let Err(error) = self.set_state_byte(
                            crate::brotli_input::B3C_BODY_PHASE,
                            next,
                        ) {
                            return self.fail_transition(error, consumed, produced);
                        }
                    }
                }
            }
            _ => {
                return self.fail_transition(
                    StreamError::InvalidFormat,
                    consumed,
                    produced,
                );
            }
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(60)]
    fn step_body_phase_copy_emit(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase == 13 || body_phase == 14 || body_phase == 15,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            13 => {
                let copy_length = match self.state_u32(
                    crate::brotli_input::B3C_COPY_LENGTH,
                ) {
                    Ok(value) if 4 <= value && value <= 24 => value as u8,
                    _ => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                let distance = match self.state_u32(
                    crate::brotli_input::B3C_RESOLVED_DISTANCE,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                let history = match self.state_u32(
                    crate::brotli_input::B3C_HISTORY_LENGTH,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                if distance <= history {
                    return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    );
                }
                let word_id = distance - history - 1;
                let bits = crate::brotli_data::dictionary_size_bits(copy_length);
                if bits == 0 || bits >= 32 {
                    return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    );
                }
                proof { dictionary_mask_shift_is_nonzero(bits); }
                let mask = (1u32 << bits) - 1;
                let word_index = word_id & mask;
                let transform = word_id >> bits;
                if transform >= crate::brotli_data::TRANSFORM_COUNT as u32 {
                    return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    );
                }
                let meta_remaining = match self.state_u32(
                    crate::brotli_input::B3C_META_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(error) => return self.fail_transition(error, consumed, produced),
                };
                if let Err(error) =
                    crate::brotli_input::build_serialized_dictionary_word(
                        self.workspace,
                        self.window_bytes(),
                        self.budget,
                        copy_length,
                        word_index,
                        transform as u8,
                        meta_remaining,
                    )
                {
                    return self.fail_transition(
                        Self::map_core_failure(error),
                        consumed,
                        produced,
                    );
                }
                if let Err(error) = self.set_state_byte(
                    crate::brotli_input::B3C_BODY_PHASE,
                    14,
                ) {
                    return self.fail_transition(error, consumed, produced);
                }
            }
            14 => {
                let length = match self.state_byte(
                    crate::brotli_input::B3C_DICTIONARY_OUTPUT_LENGTH,
                ) {
                    Ok(value) if value <= 37 => value,
                    _ => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                let cursor = match self.state_byte(
                    crate::brotli_input::B3C_DICTIONARY_OUTPUT_CURSOR,
                ) {
                    Ok(value) if value <= length => value,
                    _ => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                };
                if cursor == length {
                    let next = match self.state_u32(
                        crate::brotli_input::B3C_META_REMAINING,
                    ) {
                        Ok(0) => 15,
                        Ok(_) => 0,
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    };
                    if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_BODY_PHASE,
                        next,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else {
                    let byte = match
                        crate::brotli_input::read_serialized_dictionary_byte(
                            self.workspace,
                            self.window_bytes(),
                            cursor,
                        )
                    {
                        Ok(value) => value,
                        Err(error) => return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        ),
                    };
                    let output_block = output_block_reason(
                        self.budget.output_remaining,
                        self.budget.work_remaining,
                        produced < output.len(),
                    );
                    if output_block == 1 {
                        return self.fail_transition(
                            StreamError::ResourceLimit,
                            consumed,
                            produced,
                        );
                    }
                    if output_block == 2 {
                        return self.return_transition(
                            input.len(),
                            end_of_input,
                            consumed,
                            produced,
                            Status::NeedOutput,
                        );
                    }
                    if let Err(error) =
                        self.emit_byte(byte, output, produced, false).0
                    {
                        return self.fail_transition(error, consumed, produced);
                    }
                    produced += 1;
                    if let Err(error) = self.set_state_byte(
                        crate::brotli_input::B3C_DICTIONARY_OUTPUT_CURSOR,
                        cursor + 1,
                    ) {
                        return self.fail_transition(error, consumed, produced);
                    }
                }
            }
            15 => {
                if let Err(error) = self.finish_meta_block() {
                    return self.fail_transition(error, consumed, produced);
                }
                if let Err(error) = self.set_state_byte(
                    crate::brotli_input::B3C_BODY_PHASE,
                    0,
                ) {
                    return self.fail_transition(error, consumed, produced);
                }
            }
            _ => {
                return self.fail_transition(
                    StreamError::InvalidFormat,
                    consumed,
                    produced,
                );
            }
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(90)]
    fn step_body_early_transition(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            body_phase <= 7,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            0 => self.step_body_phase_zero(
                input, output, end_of_input, consumed, produced, body_phase,
            ),
            4 | 5 => self.step_body_phase_lengths(
                input, output, end_of_input, consumed, produced, body_phase,
            ),
            6 | 7 => self.step_body_phase_literals(
                input, output, end_of_input, consumed, produced, body_phase,
            ),
            _ => self.fail_transition(StreamError::InvalidFormat, consumed, produced),
        }

    }

    #[verifier::rlimit(90)]
    fn step_body_late_transition(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        body_phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
            8 <= body_phase && body_phase <= 15,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match body_phase {
            8 => self.step_body_phase_distance_symbol(
                input, output, end_of_input, consumed, produced, body_phase,
            ),
            10 | 11 | 12 => self.step_body_phase_copy_setup(
                input, output, end_of_input, consumed, produced, body_phase,
            ),
            13 | 14 | 15 => self.step_body_phase_copy_emit(
                input, output, end_of_input, consumed, produced, body_phase,
            ),
            _ => self.fail_transition(StreamError::InvalidFormat, consumed, produced),
        }

    }

    #[verifier::rlimit(120)]
    fn step_body_transition(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ) == 6,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        let body_phase = match self.state_byte(crate::brotli_input::B3C_BODY_PHASE) {
            Ok(value) => value,
            Err(error) => return self.fail_transition(error, consumed, produced),
        };
        match body_phase {
            0..=7 => self.step_body_early_transition(
                input,
                output,
                end_of_input,
                consumed,
                produced,
                body_phase,
            ),
            8..=15 => self.step_body_late_transition(
                input,
                output,
                end_of_input,
                consumed,
                produced,
                body_phase,
            ),
            _ => self.fail_transition(StreamError::InvalidFormat, consumed, produced),
        }

    }

    #[verifier::rlimit(90)]
    fn step_stream_transition(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
        consumed: usize,
        produced: usize,
        phase: u8,
    ) -> (r: Result<(usize, usize), Step>)
        requires
            old(self).invariant(),
            consumed <= input.len(),
            produced <= old(output)@.len(),
            phase == crate::brotli_input::b3c_scalar_byte_at(
                old(self).workspace@,
                (1u32 << old(self).budget.limits.max_window_bits) as u32,
                crate::brotli_input::B3C_STREAM_PHASE as int,
            ),
            phase < 8,
        ensures
            final(self).invariant(),
            final(self).budget.limits == old(self).budget.limits,
            final(self).budget.work_remaining <= old(self).budget.work_remaining,
            final(output)@.len() == old(output)@.len(),
            match r {
                Ok((next_consumed, next_produced)) => {
                    &&& next_consumed <= input.len()
                    &&& produced <= next_produced
                    &&& next_produced <= old(output)@.len()
                    &&& forall|i: int| next_produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
                Err(step) => {
                    &&& step.consumed <= input.len()
                    &&& produced <= step.produced
                    &&& step.produced <= old(output)@.len()
                    &&& forall|i: int| step.produced <= i < old(output)@.len() ==>
                        final(output)@[i] == old(output)@[i]
                },
            },
    {
        proof { reveal(BrotliDecoder::valid); }
        let mut consumed = consumed;
        let mut produced = produced;
        match phase {
            0 => {
                let final_input = self.committed_eof() || end_of_input;
                let step = crate::brotli_input::advance_serialized_window_header(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                    &input[consumed..],
                    final_input,
                );
                consumed += step.consumed;
                match step.status {
                    crate::brotli_input::WindowStatus::NeedInput => {
                        return self.return_transition(
                            input.len(), end_of_input, consumed, produced, Status::NeedInput,
                        );
                    }
                    crate::brotli_input::WindowStatus::Complete { .. } => {}
                    crate::brotli_input::WindowStatus::Failed(error) => {
                        return self.fail_transition(Self::map_core_failure(error), consumed, produced);
                    }
                }
            }
            1 => {
                let final_input = self.committed_eof() || end_of_input;
                let step = crate::brotli_input::advance_serialized_meta_header(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                    &input[consumed..],
                    final_input,
                );
                consumed += step.consumed;
                match step.status {
                    crate::brotli_input::MetaStatus::NeedInput => {
                        return self.return_transition(
                            input.len(), end_of_input, consumed, produced, Status::NeedInput,
                        );
                    }
                    crate::brotli_input::MetaStatus::Failed(error) => {
                        return self.fail_transition(Self::map_core_failure(error), consumed, produced);
                    }
                    crate::brotli_input::MetaStatus::Complete(header) => {
                        if header.is_empty {
                            if header.is_last {
                                if self.write_phase(7).is_err() {
                                    return self.fail_transition(
                                        StreamError::InvalidFormat, consumed, produced,
                                    );
                                }
                            } else {
                                return self.fail_transition(
                                    StreamError::InvalidFormat, consumed, produced,
                                );
                            }
                        } else if header.is_metadata || header.is_uncompressed {
                            if self.write_phase(2).is_err() {
                                return self.fail_transition(
                                    StreamError::InvalidFormat, consumed, produced,
                                );
                            }
                        } else {
                            if let Err(error) =
                                crate::brotli_input::start_serialized_compressed_header(
                                    self.workspace,
                                    self.window_bytes(),
                                    self.budget,
                                )
                            {
                                return self.fail_transition(
                                    Self::map_core_failure(error),
                                    consumed,
                                    produced,
                                );
                            }
                            if self.write_phase(5).is_err() {
                                return self.fail_transition(
                                    StreamError::InvalidFormat, consumed, produced,
                                );
                            }
                        }
                    }
                }
            }
            2 => {
                if let Err(error) = crate::brotli_input::align_serialized_to_byte(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                ) {
                    return self.fail_transition(Self::map_core_failure(error), consumed, produced);
                }
                let flags = match crate::brotli_input::read_b3c_state_byte(
                    self.workspace,
                    self.window_bytes(),
                    crate::brotli_input::B3C_META_FLAGS,
                ) {
                    Ok(value) => value,
                    Err(_) => 0,
                };
                if flags & 8 != 0 {
                    let _ = self.write_phase(3);
                } else if flags & 4 != 0 {
                    let _ = self.write_phase(4);
                } else {
                    return self.fail_transition(StreamError::InvalidFormat, consumed, produced);
                }
            }
            3 => {
                let remaining = match crate::brotli_input::read_b3c_state_u32(
                    self.workspace,
                    self.window_bytes(),
                    crate::brotli_input::B3C_META_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(_) => u32::MAX,
                };
                if remaining == 0 {
                    if let Err(error) = self.finish_meta_block() {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else if consumed == input.len() {
                    if self.committed_eof() || end_of_input {
                        return self.fail_transition(StreamError::Truncated, consumed, produced);
                    }
                    return self.return_transition(
                        input.len(), end_of_input, consumed, produced, Status::NeedInput,
                    );
                } else if self.budget.input_remaining == 0
                    || self.budget.work_remaining < 2
                {
                    return self.fail_transition(StreamError::ResourceLimit, consumed, produced);
                } else {
                    if self.consume_metadata_byte(remaining).is_err() {
                        return self.fail_transition(
                            StreamError::InvalidFormat,
                            consumed,
                            produced,
                        );
                    }
                    consumed += 1;
                }
            }
            4 => {
                let remaining = match crate::brotli_input::read_b3c_state_u32(
                    self.workspace,
                    self.window_bytes(),
                    crate::brotli_input::B3C_META_REMAINING,
                ) {
                    Ok(value) => value,
                    Err(_) => u32::MAX,
                };
                if remaining == 0 {
                    if let Err(error) = self.finish_meta_block() {
                        return self.fail_transition(error, consumed, produced);
                    }
                } else if consumed == input.len() {
                    if self.committed_eof() || end_of_input {
                        return self.fail_transition(StreamError::Truncated, consumed, produced);
                    }
                    return self.return_transition(
                        input.len(), end_of_input, consumed, produced, Status::NeedInput,
                    );
                } else if self.budget.input_remaining == 0 {
                    return self.fail_transition(StreamError::ResourceLimit, consumed, produced);
                } else {
                    let output_block = output_block_reason(
                        self.budget.output_remaining,
                        self.budget.work_remaining,
                        produced < output.len(),
                    );
                    if output_block == 1 {
                        return self.fail_transition(
                            StreamError::ResourceLimit,
                            consumed,
                            produced,
                        );
                    }
                    if output_block == 2 {
                        return self.return_transition(
                            input.len(), end_of_input, consumed, produced, Status::NeedOutput,
                        );
                    }
                    let byte = input[consumed];
                    match self.emit_uncompressed_byte(byte, output, produced).0 {
                        Ok(()) => {
                            consumed += 1;
                            produced += 1;
                        }
                        Err(error) => return self.fail_transition(error, consumed, produced),
                    }
                }
            }
            5 => {
                let final_input = self.committed_eof() || end_of_input;
                let step = crate::brotli_input::advance_serialized_compressed_header(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                    &input[consumed..],
                    final_input,
                );
                consumed += step.consumed;
                match step.status {
                    crate::brotli_input::CompressedStatus::NeedInput => {
                        return self.return_transition(
                            input.len(),
                            end_of_input,
                            consumed,
                            produced,
                            Status::NeedInput,
                        );
                    }
                    crate::brotli_input::CompressedStatus::Complete => {
                        if let Err(error) =
                            crate::brotli_input::initialize_serialized_distance_lut(
                                self.workspace,
                                self.window_bytes(),
                                self.budget,
                            )
                        {
                            return self.fail_transition(
                                Self::map_core_failure(error),
                                consumed,
                                produced,
                            );
                        }
                        let _ = self.write_phase(6);
                    }
                    crate::brotli_input::CompressedStatus::Failed(error) => {
                        return self.fail_transition(
                            Self::map_core_failure(error),
                            consumed,
                            produced,
                        );
                    }
                }
            }
            6 => {
                match self.step_body_transition(
                    input,
                    output,
                    end_of_input,
                    consumed,
                    produced,
                ) {
                    Ok((next_consumed, next_produced)) => {
                        consumed = next_consumed;
                        produced = next_produced;
                    }
                    Err(step) => return Err(step),
                }
            }
            7 => {
                if let Err(error) = crate::brotli_input::align_serialized_to_byte(
                    self.workspace,
                    self.window_bytes(),
                    self.budget,
                ) {
                    return self.fail_transition(Self::map_core_failure(error), consumed, produced);
                }
                let _ = self.write_phase(8);
                return self.return_transition(
                    input.len(), end_of_input, consumed, produced, Status::Finished,
                );
            }
            8 | 9 => {
                match self.terminal_step(phase) {
                    Some(step) => return Err(step),
                    None => return self.fail_transition(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                }
            }
            _ => return self.fail_transition(StreamError::InvalidFormat, consumed, produced),
        }
        Ok((consumed, produced))
    }

    #[verifier::rlimit(60)]
    pub fn step(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        end_of_input: bool,
    ) -> (r: Step)
        requires old(self).valid(),
        ensures
            r.consumed <= input.len(),
            r.produced <= old(output)@.len(),
            final(self).valid(),
            final(output)@.len() == old(output)@.len(),
            forall|i: int| r.produced <= i < old(output)@.len() ==>
                final(output)@[i] == old(output)@[i],
            old(self).stored_terminal_result().is_some() ==> {
                &&& r == old(self).stored_terminal_result().unwrap()
                &&& final(self).budget_view() == old(self).budget_view()
                &&& final(self).workspace_view() == old(self).workspace_view()
                &&& final(output)@ == old(output)@
            },
    {
        let ghost entry_terminal = self.stored_terminal_result();
        proof {
            reveal(BrotliDecoder::valid);
            reveal(BrotliDecoder::stored_terminal_result);
            reveal(BrotliDecoder::budget_view);
            reveal(BrotliDecoder::workspace_view);
        }
        let phase = match self.read_phase() {
            Ok(value) => value,
            Err(error) => return self.fail(error, 0, 0),
        };
        if let Some(step) = self.terminal_step(phase) {
            proof {
                assert(entry_terminal == Some(step));
                assert(*self.budget == *old(self).budget);
                assert(self.workspace@ == old(self).workspace@);
                assert(output@ == old(output)@);
            }
            return step;
        }
        proof {
            assert(entry_terminal.is_none());
            assert(old(self).stored_terminal_result().is_none());
        }
        if self.committed_eof() && !input.is_empty() {
            return self.fail(StreamError::InvalidFormat, 0, 0);
        }
        if !self.budget.charge_call() {
            return self.fail(StreamError::ResourceLimit, 0, 0);
        }

        let mut consumed = 0usize;
        let mut produced = 0usize;
        while self.budget.work_remaining > 0
            invariant
                consumed <= input.len(),
                produced <= output.len(),
                output@.len() == old(output)@.len(),
                forall|i: int| produced <= i < old(output)@.len() ==>
                    output@[i] == old(output)@[i],
                self.invariant(),
                self.budget.valid(),
                self.budget.limits == old(self).budget.limits,
                entry_terminal.is_none(),
                old(self).stored_terminal_result().is_none(),
                crate::brotli_input::b3c_workspace_shape(
                    self.workspace@.len() as nat,
                    (1u32 << self.budget.limits.max_window_bits) as u32,
                ),
            decreases self.budget.work_remaining,
        {
            assert!(self.budget.charge_work(1));
            let phase = match self.read_phase() {
                Ok(value) => value,
                Err(error) => return self.fail(error, consumed, produced),
            };
            if phase == 8 || phase == 9 {
                match self.terminal_step(phase) {
                    Some(step) => return self.return_step(
                        input.len(),
                        end_of_input,
                        consumed,
                        produced,
                        step.status,
                    ),
                    None => return self.fail(
                        StreamError::InvalidFormat,
                        consumed,
                        produced,
                    ),
                }
            }
            match self.step_stream_transition(
                input,
                output,
                end_of_input,
                consumed,
                produced,
                phase,
            ) {
                Ok((next_consumed, next_produced)) => {
                    consumed = next_consumed;
                    produced = next_produced;
                }
                Err(step) => return step,
            }
        }
        self.fail(StreamError::ResourceLimit, consumed, produced)
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;

    fn limits() -> RequestLimits {
        RequestLimits {
            max_input: 10,
            max_output: 20,
            max_work: 1_000,
            max_calls: 30,
            max_initializations: 2,
            max_window_bits: 10,
        }
    }

    #[test]
    fn budget_and_initialization_are_exact_and_reset_does_not_refill() {
        let mut budget = RequestBudget::new(limits()).unwrap();
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5; required];
        {
            let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
            decoder.reset().unwrap();
        }
        assert_eq!(budget.input_remaining, 10);
        assert_eq!(budget.output_remaining, 20);
        assert_eq!(budget.calls_remaining, 30);
        assert_eq!(budget.initializations_remaining, 0);
        assert_eq!(budget.work_remaining, 1_000 - 2 * B3C_INITIALIZATION_WORK);
    }

    #[test]
    fn initialization_failures_have_exact_effects() {
        let mut budget = RequestBudget::new(limits()).unwrap();
        let mut short = vec![0xa5; 16];
        assert!(matches!(
            BrotliDecoder::new(&mut short, &mut budget),
            Err(InitError::WorkspaceTooSmall),
        ));
        assert!(short.iter().all(|byte| *byte == 0xa5));
        assert_eq!(budget.initializations_remaining, 2);

        let mut poor = RequestBudget::new(RequestLimits {
            max_work: B3C_INITIALIZATION_WORK - 1,
            ..limits()
        })
        .unwrap();
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5; required];
        assert!(matches!(
            BrotliDecoder::new(&mut workspace, &mut poor),
            Err(InitError::ResourceLimit),
        ));
        assert!(workspace.iter().all(|byte| *byte == 0xa5));
        assert_eq!(poor.initializations_remaining, 1);
        assert_eq!(poor.work_remaining, B3C_INITIALIZATION_WORK - 1);
    }

    #[test]
    fn reset_debits_only_initialization_and_work_and_is_atomic_on_failure() {
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
        let mut budget = RequestBudget::new(RequestLimits {
            max_input: 100,
            max_output: 100,
            max_work: 100_000_000,
            max_calls: 10,
            max_initializations: 2,
            max_window_bits: 10,
        })
        .unwrap();
        let mut workspace = vec![0xa5; required];
        let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
        let input = include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed");
        let first = decoder.step(&input[..1], &mut [0xcc; 1], false);
        assert_eq!(first.status, Status::NeedInput);
        let before = (
            decoder.budget.input_remaining,
            decoder.budget.output_remaining,
            decoder.budget.work_remaining,
            decoder.budget.calls_remaining,
            decoder.budget.initializations_remaining,
        );
        decoder.reset().unwrap();
        assert_eq!(decoder.budget.input_remaining, before.0);
        assert_eq!(decoder.budget.output_remaining, before.1);
        assert_eq!(
            decoder.budget.work_remaining,
            before.2 - B3C_INITIALIZATION_WORK
        );
        assert_eq!(decoder.budget.calls_remaining, before.3);
        assert_eq!(decoder.budget.initializations_remaining, before.4 - 1);

        let mut scarce = RequestBudget::new(RequestLimits {
            max_input: 0,
            max_output: 0,
            max_work: B3C_INITIALIZATION_WORK + (B3C_INITIALIZATION_WORK - 1),
            max_calls: 0,
            max_initializations: 2,
            max_window_bits: 10,
        })
        .unwrap();
        let mut scarce_workspace = vec![0x5a; required];
        let mut scarce_decoder = BrotliDecoder::new(&mut scarce_workspace, &mut scarce).unwrap();
        let before_workspace = scarce_decoder.workspace.to_vec();
        assert_eq!(scarce_decoder.reset(), Err(InitError::ResourceLimit));
        assert_eq!(scarce_decoder.workspace, before_workspace);
        assert_eq!(
            scarce_decoder.budget.work_remaining,
            B3C_INITIALIZATION_WORK - 1
        );
        assert_eq!(scarce_decoder.budget.initializations_remaining, 0);
    }

    fn decode_fixture(input: &[u8], input_chunk: usize, output_chunk: usize) -> (Status, Vec<u8>) {
        let mut budget = RequestBudget::new(RequestLimits {
            max_input: 1_000_000,
            max_output: 1_000_000,
            max_work: 10_000_000_000,
            max_calls: 1_100_000,
            max_initializations: 1,
            max_window_bits: 10,
        })
        .unwrap();
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5; required];
        let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
        let mut at = 0usize;
        let mut decoded = Vec::new();
        let mut out = vec![0xcc; output_chunk];
        for _ in 0..input.len() + 1_000_001 {
            let end = (at + input_chunk).min(input.len());
            out.fill(0xcc);
            let step = decoder.step(&input[at..end], &mut out, end == input.len());
            assert!(step.consumed <= end - at);
            assert!(step.produced <= out.len());
            assert!(out[step.produced..].iter().all(|byte| *byte == 0xcc));
            at += step.consumed;
            decoded.extend_from_slice(&out[..step.produced]);
            match step.status {
                Status::NeedInput => {
                    assert_eq!(at, end);
                    assert!(end < input.len());
                }
                Status::NeedOutput => {
                    assert_eq!(step.produced, output_chunk);
                }
                terminal => return (terminal, decoded),
            }
        }
        panic!("fixture did not terminate")
    }

    #[test]
    fn metadata_and_uncompressed_streams_cover_chunks_and_padding() {
        for input_chunk in 1..=4 {
            let (status, output) = decode_fixture(&[0x2c, 0x00, 0xa5, 0x03], input_chunk, 1);
            assert_eq!(status, Status::Finished);
            assert!(output.is_empty());
        }
        for input_chunk in 1..=5 {
            let (status, output) = decode_fixture(&[0x00, 0x00, 0x10, 0x5a, 0x03], input_chunk, 1);
            assert_eq!(status, Status::Finished);
            assert_eq!(output, [0x5a]);
        }
        for invalid in [
            [0x2c, 0x80, 0xa5, 0x03].as_slice(),
            [0x00, 0x00, 0x30, 0x5a, 0x03].as_slice(),
        ] {
            let (status, _) = decode_fixture(&invalid, invalid.len(), 1);
            assert_eq!(status, Status::Failed(StreamError::InvalidFormat));
        }
    }

    #[test]
    fn need_output_does_not_mask_resource_exhaustion() {
        let input = [0x00, 0x00, 0x10, 0x5a, 0x03];
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;

        let mut limited = RequestBudget::new(RequestLimits {
            max_input: input.len() as u64,
            max_output: 0,
            max_work: 100_000_000,
            max_calls: 2,
            max_initializations: 1,
            max_window_bits: 10,
        })
        .unwrap();
        let mut limited_workspace = vec![0xa5; required];
        let mut limited_decoder = BrotliDecoder::new(&mut limited_workspace, &mut limited).unwrap();
        let exhausted = limited_decoder.step(&input, &mut [], true);
        assert_eq!(exhausted.status, Status::Failed(StreamError::ResourceLimit));
        let retry = limited_decoder.step(&[0xff], &mut [0xcc], false);
        assert_eq!(
            retry,
            Step {
                consumed: 0,
                produced: 0,
                status: Status::Failed(StreamError::ResourceLimit),
            },
        );

        let mut available = RequestBudget::new(RequestLimits {
            max_input: input.len() as u64,
            max_output: 1,
            max_work: 100_000_000,
            max_calls: 2,
            max_initializations: 1,
            max_window_bits: 10,
        })
        .unwrap();
        let mut available_workspace = vec![0x5a; required];
        let mut available_decoder =
            BrotliDecoder::new(&mut available_workspace, &mut available).unwrap();
        let blocked = available_decoder.step(&input, &mut [], true);
        assert_eq!(blocked.status, Status::NeedOutput);
        assert_eq!(blocked.produced, 0);
        let mut output = [0xcc; 1];
        let finished = available_decoder.step(&input[blocked.consumed..], &mut output, true);
        assert_eq!(finished.status, Status::Finished);
        assert_eq!(output, [0x5a]);
    }

    #[test]
    fn final_truncation_is_sticky() {
        let mut budget = RequestBudget::new(RequestLimits {
            max_input: 10,
            max_output: 10,
            max_work: 10_000,
            max_calls: 10,
            max_initializations: 1,
            max_window_bits: 10,
        })
        .unwrap();
        let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
        let mut workspace = vec![0xa5; required];
        let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
        let first = decoder.step(&[0x00], &mut [], true);
        assert_eq!(first.status, Status::Failed(StreamError::Truncated));
        let second = decoder.step(&[0xff], &mut [0xcc], false);
        assert_eq!(
            second,
            Step {
                consumed: 0,
                produced: 0,
                status: Status::Failed(StreamError::Truncated),
            }
        );
    }

    #[test]
    fn compressed_overlap_fixture_decodes_completely() {
        let input = include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed");
        let (status, output) = decode_fixture(input, input.len(), 8);
        assert_eq!(status, Status::Finished);
        assert_eq!(
            output,
            include_bytes!("../tests/fixtures/brotli/corpus/10x10y")
        );
    }

    #[test]
    fn small_compressed_fixtures_cover_whole_and_one_byte_input() {
        for (compressed, expected) in [
            (
                include_bytes!("../tests/fixtures/brotli/corpus/empty.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/empty").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/x.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/x").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/xyzzy.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/xyzzy").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/64x.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/64x").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/compression.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/compression").as_slice(),
            ),
        ] {
            for input_chunk in [1usize, compressed.len()] {
                for output_chunk in [1usize, expected.len().max(1), expected.len() + 7] {
                    let (status, output) = decode_fixture(compressed, input_chunk, output_chunk);
                    assert_eq!(status, Status::Finished);
                    assert_eq!(output, expected);
                }
            }
        }
    }

    #[test]
    fn small_compressed_fixtures_cover_every_input_split() {
        for (compressed, expected) in [
            (
                include_bytes!("../tests/fixtures/brotli/corpus/x.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/x").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/xyzzy.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/xyzzy").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/64x.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/64x").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/compression.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/compression").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/quickfox_repeated.compressed")
                    .as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/quickfox_repeated").as_slice(),
            ),
        ] {
            for split in 1..compressed.len() {
                let mut budget = RequestBudget::new(RequestLimits {
                    max_input: compressed.len() as u64,
                    max_output: expected.len() as u64,
                    max_work: 10_000_000_000,
                    max_calls: 2,
                    max_initializations: 1,
                    max_window_bits: 10,
                })
                .unwrap();
                let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
                let mut workspace = vec![0xa5; required];
                let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
                let mut decoded = Vec::new();

                let mut first_output = vec![0xcc; expected.len().max(1)];
                let first = decoder.step(&compressed[..split], &mut first_output, false);
                assert_eq!(first.status, Status::NeedInput, "split={split}");
                assert_eq!(first.consumed, split);
                decoded.extend_from_slice(&first_output[..first.produced]);
                assert!(first_output[first.produced..]
                    .iter()
                    .all(|byte| *byte == 0xcc));

                let mut second_output = vec![0x5a; expected.len().max(1)];
                let second = decoder.step(&compressed[split..], &mut second_output, true);
                assert_eq!(second.status, Status::Finished, "split={split}");
                assert_eq!(second.consumed, compressed.len() - split);
                decoded.extend_from_slice(&second_output[..second.produced]);
                assert!(second_output[second.produced..]
                    .iter()
                    .all(|byte| *byte == 0x5a));
                assert_eq!(decoded, expected, "split={split}");
            }
        }
    }

    #[test]
    fn compressed_result_ignores_old_workspace_and_output_suffix() {
        for (input, expected) in [
            (
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y").as_slice(),
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/compression.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/compression").as_slice(),
            ),
        ] {
            let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
            let mut baseline: Option<(Step, Vec<u8>, (u64, u64, u64, u64, u32))> = None;
            for (workspace_fill, output_fill) in [(0x00u8, 0x00u8), (0xa5, 0xcc), (0xff, 0xff)] {
                let mut budget = RequestBudget::new(RequestLimits {
                    max_input: input.len() as u64,
                    max_output: expected.len() as u64,
                    max_work: 1_000_000_000,
                    max_calls: 1,
                    max_initializations: 1,
                    max_window_bits: 10,
                })
                .unwrap();
                let mut workspace = vec![workspace_fill; required];
                let mut output = vec![output_fill; expected.len() + 7];
                let step = {
                    let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
                    decoder.step(input, &mut output, true)
                };
                assert_eq!(step.status, Status::Finished);
                assert_eq!(&output[..step.produced], expected);
                assert!(output[step.produced..]
                    .iter()
                    .all(|byte| *byte == output_fill));
                let counters = (
                    budget.input_remaining,
                    budget.output_remaining,
                    budget.work_remaining,
                    budget.calls_remaining,
                    budget.initializations_remaining,
                );
                match &baseline {
                    None => baseline = Some((step, output[..step.produced].to_vec(), counters)),
                    Some((base_step, base_output, base_counters)) => {
                        assert_eq!(&step, base_step);
                        assert_eq!(&output[..step.produced], base_output);
                        assert_eq!(&counters, base_counters);
                    }
                }
            }
        }
    }

    #[test]
    fn compressed_work_budget_boundary_and_one_short_are_terminal() {
        let input = include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed");
        let expected = include_bytes!("../tests/fixtures/brotli/corpus/10x10y");

        fn attempt(input: &[u8], output_len: usize, max_work: u64) -> (Step, Vec<u8>, u64) {
            let mut budget = RequestBudget::new(RequestLimits {
                max_input: input.len() as u64,
                max_output: output_len as u64,
                max_work,
                max_calls: 2,
                max_initializations: 1,
                max_window_bits: 10,
            })
            .unwrap();
            let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
            let mut workspace = vec![0xa5; required];
            let mut output = vec![0xcc; output_len + 7];
            let step = {
                let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
                decoder.step(input, &mut output, true)
            };
            let used = max_work - budget.work_remaining;
            (step, output, used)
        }

        let generous = 1_000_000_000u64;
        let (baseline, baseline_output, measured_work) = attempt(input, expected.len(), generous);
        assert_eq!(baseline.status, Status::Finished);
        assert_eq!(baseline.consumed, input.len());
        assert_eq!(baseline.produced, expected.len());
        assert_eq!(&baseline_output[..expected.len()], expected);
        assert!(baseline_output[expected.len()..]
            .iter()
            .all(|byte| *byte == 0xcc));

        let (boundary, boundary_output, boundary_used) =
            attempt(input, expected.len(), measured_work);
        assert_eq!(boundary, baseline);
        assert_eq!(boundary_used, measured_work);
        assert_eq!(boundary_output, baseline_output);

        let (short, short_output, _) = attempt(input, expected.len(), measured_work - 1);
        assert_eq!(short.status, Status::Failed(StreamError::ResourceLimit));
        assert!(short.consumed <= input.len());
        assert!(short.produced <= expected.len());
        assert!(short_output[short.produced..]
            .iter()
            .all(|byte| *byte == 0xcc));
    }

    #[test]
    fn compression_dictionary_fixture_resource_boundaries() {
        let input = include_bytes!("../tests/fixtures/brotli/corpus/compression.compressed");
        let expected = include_bytes!("../tests/fixtures/brotli/corpus/compression");

        fn attempt(
            input: &[u8],
            max_input: u64,
            max_output: u64,
            max_work: u64,
        ) -> (Step, Vec<u8>, u64) {
            let mut budget = RequestBudget::new(RequestLimits {
                max_input,
                max_output,
                max_work,
                max_calls: 2,
                max_initializations: 1,
                max_window_bits: 10,
            })
            .unwrap();
            let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
            let mut workspace = vec![0xa5; required];
            let mut output = vec![0xcc; 18];
            let step = {
                let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
                decoder.step(input, &mut output, true)
            };
            (step, output, max_work - budget.work_remaining)
        }

        let generous = 1_000_000_000;
        let (baseline, output, measured_work) =
            attempt(input, input.len() as u64, expected.len() as u64, generous);
        assert_eq!(baseline.status, Status::Finished);
        assert_eq!(&output[..baseline.produced], expected);
        assert!(output[baseline.produced..].iter().all(|byte| *byte == 0xcc));

        let (boundary, boundary_output, boundary_used) = attempt(
            input,
            input.len() as u64,
            expected.len() as u64,
            measured_work,
        );
        assert_eq!(boundary, baseline);
        assert_eq!(boundary_used, measured_work);
        assert_eq!(boundary_output, output);

        for (input_limit, output_limit, work_limit) in [
            (input.len() as u64 - 1, expected.len() as u64, generous),
            (input.len() as u64, expected.len() as u64 - 1, generous),
            (input.len() as u64, expected.len() as u64, measured_work - 1),
        ] {
            let (short, short_output, _) = attempt(input, input_limit, output_limit, work_limit);
            assert_eq!(short.status, Status::Failed(StreamError::ResourceLimit));
            assert!(short_output[short.produced..]
                .iter()
                .all(|byte| *byte == 0xcc));
        }
    }

    #[test]
    fn compressed_lz77_fixtures_cover_overlap_and_large_output() {
        for (compressed, expected, input_chunk, output_chunk) in [
            (
                include_bytes!("../tests/fixtures/brotli/corpus/64x.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/64x").as_slice(),
                1usize,
                1usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/zeros.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/zeros").as_slice(),
                3usize,
                1_024usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/zeros.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/zeros").as_slice(),
                1usize,
                1usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/zeros.compressed").as_slice(),
                include_bytes!("../tests/fixtures/brotli/corpus/zeros").as_slice(),
                13usize,
                262_144usize,
            ),
        ] {
            let (status, output) = decode_fixture(compressed, input_chunk, output_chunk);
            assert_eq!(status, Status::Finished);
            assert_eq!(output, expected);
        }
    }

    #[test]
    fn every_small_fixture_prefix_is_truncated_and_sticky() {
        for (compressed, expected_len) in [
            (
                include_bytes!("../tests/fixtures/brotli/corpus/empty.compressed").as_slice(),
                0usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/x.compressed").as_slice(),
                1usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/xyzzy.compressed").as_slice(),
                5usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/10x10y.compressed").as_slice(),
                20usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/64x.compressed").as_slice(),
                64usize,
            ),
            (
                include_bytes!("../tests/fixtures/brotli/corpus/compression.compressed").as_slice(),
                11usize,
            ),
        ] {
            for prefix_len in 0..compressed.len() {
                let mut budget = RequestBudget::new(RequestLimits {
                    max_input: 1_000_000,
                    max_output: 1_000_000,
                    max_work: 10_000_000_000,
                    max_calls: 2,
                    max_initializations: 1,
                    max_window_bits: 10,
                })
                .unwrap();
                let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
                let mut workspace = vec![0xa5; required];
                let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
                let mut output = vec![0xcc; expected_len + 7];
                let first = decoder.step(&compressed[..prefix_len], &mut output, true);
                assert_eq!(
                    first.status,
                    Status::Failed(StreamError::Truncated),
                    "length={} prefix={prefix_len}",
                    compressed.len(),
                );
                assert!(output[first.produced..].iter().all(|byte| *byte == 0xcc));
                let counters = (
                    decoder.budget.input_remaining,
                    decoder.budget.output_remaining,
                    decoder.budget.work_remaining,
                    decoder.budget.calls_remaining,
                    decoder.budget.initializations_remaining,
                );
                let retry = decoder.step(&[0xff], &mut output, false);
                assert_eq!(
                    retry,
                    Step {
                        consumed: 0,
                        produced: 0,
                        status: Status::Failed(StreamError::Truncated),
                    },
                );
                assert_eq!(
                    counters,
                    (
                        decoder.budget.input_remaining,
                        decoder.budget.output_remaining,
                        decoder.budget.work_remaining,
                        decoder.budget.calls_remaining,
                        decoder.budget.initializations_remaining,
                    ),
                );
            }
        }
    }

    #[test]
    fn padding_mutations_are_permanent_at_every_split() {
        for invalid in [
            [0x2c, 0x80, 0xa5, 0x03, 0x00],
            [0x00, 0x00, 0x30, 0x5a, 0x03],
        ] {
            for split in 0..=invalid.len() {
                let mut budget = RequestBudget::new(RequestLimits {
                    max_input: 100,
                    max_output: 100,
                    max_work: 1_000_000_000,
                    max_calls: 3,
                    max_initializations: 1,
                    max_window_bits: 10,
                })
                .unwrap();
                let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
                let mut workspace = vec![0xa5; required];
                let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
                let mut output = [0xcc; 1];
                let first = decoder.step(&invalid[..split], &mut output, false);
                let terminal = match first.status {
                    Status::NeedInput => {
                        assert_eq!(first.consumed, split);
                        decoder.step(&invalid[split..], &mut output, true)
                    }
                    Status::Failed(error) => Step {
                        consumed: first.consumed,
                        produced: first.produced,
                        status: Status::Failed(error),
                    },
                    other => panic!("unexpected first status at split {split}: {other:?}"),
                };
                assert_eq!(terminal.status, Status::Failed(StreamError::InvalidFormat));
                assert_eq!(terminal.produced, 0);
                assert_eq!(output, [0xcc]);
                let retry = decoder.step(&[0xff], &mut output, false);
                assert_eq!(
                    retry,
                    Step {
                        consumed: 0,
                        produced: 0,
                        status: Status::Failed(StreamError::InvalidFormat),
                    },
                );
            }
        }
    }

    #[test]
    fn pinned_native_quickfox_decodes_after_pending_span_drain() {
        let compressed =
            include_bytes!("../tests/fixtures/brotli/corpus/quickfox_repeated.compressed");
        let expected = include_bytes!("../tests/fixtures/brotli/corpus/quickfox_repeated");
        for input_chunk in [1usize, 7, compressed.len()] {
            for output_chunk in [1usize, 31, expected.len(), expected.len() + 7] {
                let (status, output) = decode_fixture(compressed, input_chunk, output_chunk);
                assert_eq!(
                    status,
                    Status::Finished,
                    "input={input_chunk} output={output_chunk}"
                );
                assert_eq!(
                    output, expected,
                    "input={input_chunk} output={output_chunk}"
                );
            }
        }
    }

    #[test]
    fn pinned_native_monkey_rejection_has_zero_output() {
        // F2 retains this checkpoint's rejection. Native accepts these bytes;
        // ContextMapRepeat is an unresolved disagreement, not a coverage case.
        let compressed = include_bytes!("../tests/fixtures/brotli/corpus/monkey.compressed");
        for input_chunk in [1usize, 7, compressed.len()] {
            for output_chunk in [1usize, 31, 843] {
                let (status, output) = decode_fixture(compressed, input_chunk, output_chunk);
                assert_eq!(status, Status::Failed(StreamError::InvalidFormat));
                assert!(output.is_empty());
            }
        }
    }

    #[test]
    fn pinned_native_monkey_rejection_is_sticky() {
        for compressed in
            [include_bytes!("../tests/fixtures/brotli/corpus/monkey.compressed").as_slice()]
        {
            let mut budget = RequestBudget::new(RequestLimits {
                max_input: compressed.len() as u64 + 1,
                max_output: 1_000_000,
                max_work: 10_000_000_000,
                max_calls: 2,
                max_initializations: 1,
                max_window_bits: 10,
            })
            .unwrap();
            let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
            let mut workspace = vec![0xa5; required];
            let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
            let mut output = [0xcc; 1];
            let first = decoder.step(compressed, &mut output, true);
            assert_eq!(first.status, Status::Failed(StreamError::InvalidFormat));
            assert_eq!(first.produced, 0);
            assert_eq!(output, [0xcc]);
            let retry = decoder.step(&[0xff], &mut output, false);
            assert_eq!(
                retry,
                Step {
                    consumed: 0,
                    produced: 0,
                    status: Status::Failed(StreamError::InvalidFormat),
                },
            );
            assert_eq!(output, [0xcc]);
        }
    }

    #[test]
    fn node_block_switch_witness_is_permanent_across_all_chunk_sizes() {
        let witness = [
            0x20, 0x00, 0x10, 0x41, 0x41, 0x41, 0xfc, 0xff, 0xff, 0x07, 0x00, 0x22, 0x28, 0xf0,
            0x0b, 0x60, 0xf7, 0xf4, 0x1f, 0x00, 0x00, 0x00,
        ];
        for input_chunk in 1..=witness.len() {
            let mut budget = RequestBudget::new(RequestLimits {
                max_input: 1_000,
                max_output: 20_000_000,
                max_work: 1_000_000_000_000,
                max_calls: 30_000,
                max_initializations: 1,
                max_window_bits: 24,
            })
            .unwrap();
            let required = crate::brotli_prefix::required_workspace_bytes(24).unwrap() as usize;
            let mut workspace = vec![0xa5; required];
            let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
            let mut at = 0usize;
            let mut attempts = 0usize;
            let terminal = loop {
                attempts += 1;
                assert!(attempts <= 30_000);
                let end = (at + input_chunk).min(witness.len());
                let mut output = vec![0xccu8; 1 << 20];
                let step = decoder.step(&witness[at..end], &mut output, end == witness.len());
                assert!(step.consumed <= end - at);
                assert!(step.produced <= output.len());
                assert!(output[step.produced..].iter().all(|byte| *byte == 0xcc));
                at += step.consumed;
                match step.status {
                    Status::NeedInput => {
                        assert_eq!(at, end);
                        assert!(end < witness.len());
                    }
                    Status::NeedOutput => {}
                    status => break status,
                }
            };
            assert_eq!(
                terminal,
                Status::Failed(StreamError::InvalidFormat),
                "chunk={input_chunk} consumed={at} body={:?} meta={:?} insert={:?} copy={:?} work={} calls={}",
                decoder.state_byte(crate::brotli_input::B3C_BODY_PHASE),
                decoder.state_u32(crate::brotli_input::B3C_META_REMAINING),
                decoder.state_u32(crate::brotli_input::B3C_INSERT_REMAINING),
                decoder.state_u32(crate::brotli_input::B3C_COPY_REMAINING),
                decoder.budget.work_remaining,
                decoder.budget.calls_remaining,
            );

            let mut retry_output = [0xccu8; 1];
            let retry = decoder.step(&[0xff], &mut retry_output, false);
            assert_eq!(
                retry,
                Step {
                    consumed: 0,
                    produced: 0,
                    status: Status::Failed(StreamError::InvalidFormat),
                },
            );
            assert_eq!(retry_output, [0xcc]);
        }
    }
    #[test]
    fn e3_emission_exact_write_budget_and_one_short_preserve_state() {
        for (work, consumes_input, wrapper) in [
            (24, false, false), (24, true, false), (24, true, true),
            (23, false, false), (23, true, false), (23, true, true),
            (8, true, true), (0, false, false),
        ] {
            let mut budget = RequestBudget::new(limits()).unwrap();
            let required = crate::brotli_prefix::required_workspace_bytes(10).unwrap() as usize;
            let mut workspace = vec![0xa5; required];
            let mut decoder = BrotliDecoder::new(&mut workspace, &mut budget).unwrap();
            decoder.write_phase(4).unwrap();
            decoder.set_state_byte(crate::brotli_input::B3C_STREAM_WINDOW_BITS, 10).unwrap();
            decoder.set_state_byte(crate::brotli_input::B3C_PREVIOUS_BYTE, 0x44).unwrap();
            decoder.set_state_u32(crate::brotli_input::B3C_META_REMAINING, 1).unwrap();
            decoder.set_state_u32(crate::brotli_input::B3C_WINDOW_POSITION, 1023).unwrap();
            let history = if consumes_input { 0 } else { 1008 };
            decoder.set_state_u32(crate::brotli_input::B3C_HISTORY_LENGTH, history).unwrap();
            decoder.budget.work_remaining = work;
            let before_budget = *decoder.budget;
            let before_workspace = decoder.workspace.to_vec();
            let mut output = [0xcc];
            let (result, _) = if wrapper {
                decoder.emit_uncompressed_byte(0x5a, &mut output, 0)
            } else {
                decoder.emit_byte(0x5a, &mut output, 0, consumes_input)
            };
            if work == 24 {
                assert_eq!(result, Ok(()));
                assert_eq!(decoder.budget.work_remaining, 0);
                assert_eq!(decoder.budget.output_remaining + 1, before_budget.output_remaining);
                assert_eq!(decoder.budget.input_remaining + u64::from(consumes_input), before_budget.input_remaining);
                assert_eq!(decoder.budget.calls_remaining, before_budget.calls_remaining);
                assert_eq!(decoder.budget.initializations_remaining, before_budget.initializations_remaining);
                assert_eq!(output, [0x5a]);
                assert_eq!(decoder.workspace[1023], output[0]);
                assert_eq!(decoder.state_u32(crate::brotli_input::B3C_WINDOW_POSITION), Ok(0));
                assert_eq!(decoder.state_u32(crate::brotli_input::B3C_HISTORY_LENGTH), Ok(if history == 0 { 1 } else { 1008 }));
                assert_eq!(decoder.state_u32(crate::brotli_input::B3C_META_REMAINING), Ok(0));
                assert_eq!(decoder.state_byte(crate::brotli_input::B3C_PREVIOUS_BYTE), Ok(0x5a));
                assert_eq!(decoder.state_byte(crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE), Ok(0x44));
                assert_eq!(crate::brotli_input::read_b3c_state_u64(
                    decoder.workspace, 1024, crate::brotli_input::B3C_TOTAL_PRODUCED,
                ), Ok(1));
            } else {
                assert_eq!(result, Err(StreamError::ResourceLimit));
                assert_eq!(*decoder.budget, before_budget);
                assert_eq!(decoder.workspace, before_workspace.as_slice());
                assert_eq!(output, [0xcc]);
            }
        }
        assert_eq!(output_block_reason(1, 23, false), 1);
        assert_eq!(output_block_reason(1, 24, false), 2);
        assert_eq!(output_block_reason(1, 24, true), 0);
        assert_eq!(output_block_reason(0, 24, false), 1);
    }

    #[test]
    fn e3_internal_store_receipts_have_no_runtime_storage() {
        assert_eq!(std::mem::size_of::<Ghost<nat>>(), 0);
        assert_eq!(std::mem::size_of::<(Result<(), StreamError>, Ghost<nat>)>(),
            std::mem::size_of::<Result<(), StreamError>>());
        assert_eq!(std::mem::align_of::<(Result<(), StreamError>, Ghost<nat>)>(),
            std::mem::align_of::<Result<(), StreamError>>());
        assert_eq!(std::mem::size_of::<(Result<(), crate::brotli_prefix::WorkspaceError>, Ghost<nat>)>(),
            std::mem::size_of::<Result<(), crate::brotli_prefix::WorkspaceError>>());
        assert_eq!(std::mem::align_of::<(Result<(), crate::brotli_prefix::WorkspaceError>, Ghost<nat>)>(),
            std::mem::align_of::<Result<(), crate::brotli_prefix::WorkspaceError>>());
    }

}
