//! Private Brotli B2 block-switch state core.
//!
//! This models the literal, command and distance integration point corrected
//! by CVE-2026-111497. Prefix-code construction/bit parsing is layered above
//! this state transition and a complete decoder remains out of scope for B2.

#![allow(dead_code)]

use crate::brotli_prefix::{decode_block_length, PrefixCode};
use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockKind {
    Literal,
    Command,
    Distance,
}

impl BlockKind {
    spec fn index(self) -> int {
        match self {
            BlockKind::Literal => 0,
            BlockKind::Command => 1,
            BlockKind::Distance => 2,
        }
    }

    fn as_index(self) -> (r: usize)
        ensures r == self.index(), r < 3,
    {
        match self {
            BlockKind::Literal => 0,
            BlockKind::Command => 1,
            BlockKind::Distance => 2,
        }
    }
}

fn same_kind(a: BlockKind, b: BlockKind) -> (r: bool)
    ensures r == (a == b), r == (a.index() == b.index()),
{
    match a {
        BlockKind::Literal => match b {
            BlockKind::Literal => true,
            _ => false,
        },
        BlockKind::Command => match b {
            BlockKind::Command => true,
            _ => false,
        },
        BlockKind::Distance => match b {
            BlockKind::Distance => true,
            _ => false,
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockSwitchError {
    InvalidDeclaration,
    InvalidBlockSwitch,
    InvalidPrefixSymbol,
    InvalidBlockLength,
    InvalidSequence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SwitchStatus {
    NeedInput,
    Complete { kind: BlockKind, block_type: u16, block_length: u32 },
    Failed(BlockSwitchError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SwitchStep {
    consumed_fields: u8,
    status: SwitchStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SwitchPhase {
    Ready,
    AwaitLength { kind: BlockKind, block_type: u16 },
    Failed(BlockSwitchError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BlockSwitchCore {
    num_types: [u16; 3],
    ring: [u16; 6],
    remaining: [u32; 3],
    phase: SwitchPhase,
}

// Approved B3b E2 adapter. This is the only crate-private boundary that exposes
// the logical B2 switch state; the original B2 types remain module-private.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum B3bSwitchFailure {
    InvalidDeclaration,
    InvalidBlockSwitch,
    InvalidPrefixSymbol,
    InvalidBlockLength,
    InvalidSequence,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum B3bSwitchPhase {
    Ready,
    AwaitLength { kind: u8, block_type: u16 },
    Failed(B3bSwitchFailure),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct B3bSwitchState {
    pub(crate) num_types: [u16; 3],
    pub(crate) ring: [u16; 6],
    pub(crate) remaining: [u32; 3],
    pub(crate) phase: B3bSwitchPhase,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum B3bSwitchOutcome {
    NeedInput,
    Complete { kind: u8, block_type: u16, block_length: u32 },
    Failed(B3bSwitchFailure),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct B3bSwitchResult {
    pub(crate) state: B3bSwitchState,
    pub(crate) consumed_fields: u8,
    pub(crate) outcome: B3bSwitchOutcome,
}

impl B3bSwitchState {
    pub(crate) open spec fn valid(&self) -> bool {
        &&& 1 <= self.num_types@[0] <= 256
        &&& 1 <= self.num_types@[1] <= 256
        &&& 1 <= self.num_types@[2] <= 256
        &&& self.ring@[1] < self.num_types@[0]
        &&& self.ring@[3] < self.num_types@[1]
        &&& self.ring@[5] < self.num_types@[2]
        &&& self.ring@[0] <= self.num_types@[0]
        &&& self.ring@[2] <= self.num_types@[1]
        &&& self.ring@[4] <= self.num_types@[2]
        &&& (self.num_types@[0] > 1 ==> self.ring@[0] < self.num_types@[0])
        &&& (self.num_types@[1] > 1 ==> self.ring@[2] < self.num_types@[1])
        &&& (self.num_types@[2] > 1 ==> self.ring@[4] < self.num_types@[2])
        &&& match self.phase {
            B3bSwitchPhase::AwaitLength { kind, block_type } => {
                &&& kind < 3
                &&& self.num_types@[kind as int] > 1
                &&& block_type < self.num_types@[kind as int]
                &&& self.remaining@[kind as int] == 0
            },
            _ => true,
        }
    }
}

fn b3b_failure_to_b2(error: B3bSwitchFailure) -> (r: BlockSwitchError)
    ensures match error {
        B3bSwitchFailure::InvalidDeclaration => r == BlockSwitchError::InvalidDeclaration,
        B3bSwitchFailure::InvalidBlockSwitch => r == BlockSwitchError::InvalidBlockSwitch,
        B3bSwitchFailure::InvalidPrefixSymbol => r == BlockSwitchError::InvalidPrefixSymbol,
        B3bSwitchFailure::InvalidBlockLength => r == BlockSwitchError::InvalidBlockLength,
        B3bSwitchFailure::InvalidSequence => r == BlockSwitchError::InvalidSequence,
    },
{
    match error {
        B3bSwitchFailure::InvalidDeclaration => BlockSwitchError::InvalidDeclaration,
        B3bSwitchFailure::InvalidBlockSwitch => BlockSwitchError::InvalidBlockSwitch,
        B3bSwitchFailure::InvalidPrefixSymbol => BlockSwitchError::InvalidPrefixSymbol,
        B3bSwitchFailure::InvalidBlockLength => BlockSwitchError::InvalidBlockLength,
        B3bSwitchFailure::InvalidSequence => BlockSwitchError::InvalidSequence,
    }
}

fn b2_failure_to_b3b(error: BlockSwitchError) -> (r: B3bSwitchFailure)
    ensures match error {
        BlockSwitchError::InvalidDeclaration => r == B3bSwitchFailure::InvalidDeclaration,
        BlockSwitchError::InvalidBlockSwitch => r == B3bSwitchFailure::InvalidBlockSwitch,
        BlockSwitchError::InvalidPrefixSymbol => r == B3bSwitchFailure::InvalidPrefixSymbol,
        BlockSwitchError::InvalidBlockLength => r == B3bSwitchFailure::InvalidBlockLength,
        BlockSwitchError::InvalidSequence => r == B3bSwitchFailure::InvalidSequence,
    },
{
    match error {
        BlockSwitchError::InvalidDeclaration => B3bSwitchFailure::InvalidDeclaration,
        BlockSwitchError::InvalidBlockSwitch => B3bSwitchFailure::InvalidBlockSwitch,
        BlockSwitchError::InvalidPrefixSymbol => B3bSwitchFailure::InvalidPrefixSymbol,
        BlockSwitchError::InvalidBlockLength => B3bSwitchFailure::InvalidBlockLength,
        BlockSwitchError::InvalidSequence => B3bSwitchFailure::InvalidSequence,
    }
}

fn b3b_kind_to_b2(kind: u8) -> (r: BlockKind)
    requires kind < 3,
    ensures r.index() == kind as int,
{
    if kind == 0 {
        BlockKind::Literal
    } else if kind == 1 {
        BlockKind::Command
    } else {
        BlockKind::Distance
    }
}

fn b2_kind_to_b3b(kind: BlockKind) -> (r: u8)
    ensures r < 3, r as int == kind.index(),
{
    match kind {
        BlockKind::Literal => 0,
        BlockKind::Command => 1,
        BlockKind::Distance => 2,
    }
}

fn restore_b3b_switch(state: B3bSwitchState) -> (r: BlockSwitchCore)
    requires state.valid(),
    ensures r.valid(), r.num_types == state.num_types,
        r.ring == state.ring, r.remaining == state.remaining,
        match state.phase {
            B3bSwitchPhase::Ready => r.phase == SwitchPhase::Ready,
            B3bSwitchPhase::AwaitLength { kind, block_type } => {
                &&& kind < 3
                &&& match r.phase {
                    SwitchPhase::AwaitLength { kind: restored, block_type: restored_type } => {
                        &&& restored.index() == kind as int
                        &&& restored_type == block_type
                    },
                    _ => false,
                }
            },
            B3bSwitchPhase::Failed(error) => match r.phase {
                SwitchPhase::Failed(restored) => match error {
                    B3bSwitchFailure::InvalidDeclaration =>
                        restored == BlockSwitchError::InvalidDeclaration,
                    B3bSwitchFailure::InvalidBlockSwitch =>
                        restored == BlockSwitchError::InvalidBlockSwitch,
                    B3bSwitchFailure::InvalidPrefixSymbol =>
                        restored == BlockSwitchError::InvalidPrefixSymbol,
                    B3bSwitchFailure::InvalidBlockLength =>
                        restored == BlockSwitchError::InvalidBlockLength,
                    B3bSwitchFailure::InvalidSequence =>
                        restored == BlockSwitchError::InvalidSequence,
                },
                _ => false,
            },
        },
{
    let phase = match state.phase {
        B3bSwitchPhase::Ready => SwitchPhase::Ready,
        B3bSwitchPhase::AwaitLength { kind, block_type } => {
            let decoded = b3b_kind_to_b2(kind);
            SwitchPhase::AwaitLength { kind: decoded, block_type }
        }
        B3bSwitchPhase::Failed(error) => {
            SwitchPhase::Failed(b3b_failure_to_b2(error))
        }
    };
    BlockSwitchCore {
        num_types: state.num_types,
        ring: state.ring,
        remaining: state.remaining,
        phase,
    }
}

fn snapshot_b3b_switch(core: BlockSwitchCore) -> (r: B3bSwitchState)
    requires core.valid(),
    ensures r.valid(), r.num_types == core.num_types,
        r.ring == core.ring, r.remaining == core.remaining,
        match core.phase {
            SwitchPhase::Ready => r.phase == B3bSwitchPhase::Ready,
            SwitchPhase::AwaitLength { kind, block_type } => match r.phase {
                B3bSwitchPhase::AwaitLength {
                    kind: stored,
                    block_type: stored_type,
                } => {
                    &&& stored as int == kind.index()
                    &&& stored_type == block_type
                },
                _ => false,
            },
            SwitchPhase::Failed(error) => match r.phase {
                B3bSwitchPhase::Failed(stored) => match error {
                    BlockSwitchError::InvalidDeclaration =>
                        stored == B3bSwitchFailure::InvalidDeclaration,
                    BlockSwitchError::InvalidBlockSwitch =>
                        stored == B3bSwitchFailure::InvalidBlockSwitch,
                    BlockSwitchError::InvalidPrefixSymbol =>
                        stored == B3bSwitchFailure::InvalidPrefixSymbol,
                    BlockSwitchError::InvalidBlockLength =>
                        stored == B3bSwitchFailure::InvalidBlockLength,
                    BlockSwitchError::InvalidSequence =>
                        stored == B3bSwitchFailure::InvalidSequence,
                },
                _ => false,
            },
        },
{
    let phase = match core.phase {
        SwitchPhase::Ready => B3bSwitchPhase::Ready,
        SwitchPhase::AwaitLength { kind, block_type } => {
            B3bSwitchPhase::AwaitLength {
                kind: b2_kind_to_b3b(kind),
                block_type,
            }
        }
        SwitchPhase::Failed(error) => B3bSwitchPhase::Failed(b2_failure_to_b3b(error)),
    };
    B3bSwitchState {
        num_types: core.num_types,
        ring: core.ring,
        remaining: core.remaining,
        phase,
    }
}

spec fn declarations_valid(num_types: Seq<u16>) -> bool {
    num_types.len() == 3
        && 1 <= num_types[0] <= 256
        && 1 <= num_types[1] <= 256
        && 1 <= num_types[2] <= 256
}

spec fn resolved_type(previous: u16, current: u16, max_type: u16, symbol: u16) -> u16 {
    let raw = if symbol == 1 {
        (current as int + 1) as u16
    } else if symbol == 0 {
        previous
    } else {
        (symbol as int - 2) as u16
    };
    if raw >= max_type { (raw as int - max_type as int) as u16 } else { raw }
}

fn resolve_type(previous: u16, current: u16, max_type: u16, symbol: u16) -> (r: u16)
    requires 2 <= max_type <= 256,
        previous < max_type, current < max_type, symbol < max_type + 2,
    ensures r == resolved_type(previous, current, max_type, symbol), r < max_type,
{
    let raw = if symbol == 1 {
        current + 1
    } else if symbol == 0 {
        previous
    } else {
        symbol - 2
    };
    if raw >= max_type { raw - max_type } else { raw }
}

spec fn switch_arrays_unchanged(old: BlockSwitchCore, next: BlockSwitchCore) -> bool {
    &&& next.num_types == old.num_types
    &&& next.ring == old.ring
    &&& next.remaining == old.remaining
}

spec fn switch_updated(
    old: BlockSwitchCore,
    next: BlockSwitchCore,
    kind: BlockKind,
    block_type: u16,
    block_length: u32,
) -> bool {
    let k = kind.index();
    &&& next.num_types == old.num_types
    &&& next.phase == SwitchPhase::Ready
    &&& next.remaining@ == old.remaining@.update(k, block_length)
    &&& next.ring@ == old.ring@
        .update(2 * k, old.ring@[2 * k + 1])
        .update(2 * k + 1, block_type)
}

spec fn switch_transition_holds(
    old: BlockSwitchCore,
    kind: BlockKind,
    type_symbol: Option<u16>,
    block_length: Option<u32>,
    next: BlockSwitchCore,
    step: SwitchStep,
) -> bool {
    let k = kind.index();
    match old.phase {
        SwitchPhase::Failed(error) => {
            &&& next == old
            &&& step == (SwitchStep {
                consumed_fields: 0,
                status: SwitchStatus::Failed(error),
            })
        },
        SwitchPhase::AwaitLength { kind: waiting, block_type } => {
            if waiting != kind {
                &&& switch_arrays_unchanged(old, next)
                &&& next.phase == SwitchPhase::Failed(BlockSwitchError::InvalidSequence)
                &&& step == (SwitchStep {
                    consumed_fields: 0,
                    status: SwitchStatus::Failed(BlockSwitchError::InvalidSequence),
                })
            } else {
                match block_length {
                    None => {
                        &&& next == old
                        &&& step == (SwitchStep {
                            consumed_fields: 0,
                            status: SwitchStatus::NeedInput,
                        })
                    },
                    Some(0) => {
                        &&& switch_arrays_unchanged(old, next)
                        &&& next.phase == SwitchPhase::Failed(
                            BlockSwitchError::InvalidBlockLength,
                        )
                        &&& step == (SwitchStep {
                            consumed_fields: 1,
                            status: SwitchStatus::Failed(
                                BlockSwitchError::InvalidBlockLength,
                            ),
                        })
                    },
                    Some(length) => {
                        &&& switch_updated(old, next, kind, block_type, length)
                        &&& step == (SwitchStep {
                            consumed_fields: 1,
                            status: SwitchStatus::Complete {
                                kind,
                                block_type,
                                block_length: length,
                            },
                        })
                    },
                }
            }
        },
        SwitchPhase::Ready => {
            let max_type = old.num_types@[k];
            if max_type <= 1 {
                &&& switch_arrays_unchanged(old, next)
                &&& next.phase == SwitchPhase::Failed(
                    BlockSwitchError::InvalidBlockSwitch,
                )
                &&& step == (SwitchStep {
                    consumed_fields: 0,
                    status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch),
                })
            } else {
                match type_symbol {
                    None => {
                        &&& next == old
                        &&& step == (SwitchStep {
                            consumed_fields: 0,
                            status: SwitchStatus::NeedInput,
                        })
                    },
                    Some(symbol) => {
                        if symbol >= max_type + 2 {
                            &&& switch_arrays_unchanged(old, next)
                            &&& next.phase == SwitchPhase::Failed(
                                BlockSwitchError::InvalidPrefixSymbol,
                            )
                            &&& step == (SwitchStep {
                                consumed_fields: 1,
                                status: SwitchStatus::Failed(
                                    BlockSwitchError::InvalidPrefixSymbol,
                                ),
                            })
                        } else {
                            let block_type = resolved_type(
                                old.ring@[2 * k],
                                old.ring@[2 * k + 1],
                                max_type,
                                symbol,
                            );
                            match block_length {
                                None => {
                                    &&& switch_arrays_unchanged(old, next)
                                    &&& next.phase == SwitchPhase::AwaitLength {
                                        kind,
                                        block_type,
                                    }
                                    &&& step == (SwitchStep {
                                        consumed_fields: 1,
                                        status: SwitchStatus::NeedInput,
                                    })
                                },
                                Some(0) => {
                                    &&& switch_arrays_unchanged(old, next)
                                    &&& next.phase == SwitchPhase::Failed(
                                        BlockSwitchError::InvalidBlockLength,
                                    )
                                    &&& step == (SwitchStep {
                                        consumed_fields: 2,
                                        status: SwitchStatus::Failed(
                                            BlockSwitchError::InvalidBlockLength,
                                        ),
                                    })
                                },
                                Some(length) => {
                                    &&& switch_updated(old, next, kind, block_type, length)
                                    &&& step == (SwitchStep {
                                        consumed_fields: 2,
                                        status: SwitchStatus::Complete {
                                            kind,
                                            block_type,
                                            block_length: length,
                                        },
                                    })
                                },
                            }
                        }
                    },
                }
            }
        },
    }
}

spec fn b3b_arrays_unchanged(old: B3bSwitchState, next: B3bSwitchState) -> bool {
    &&& next.num_types == old.num_types
    &&& next.ring == old.ring
    &&& next.remaining == old.remaining
}

spec fn b3b_updated(
    old: B3bSwitchState,
    next: B3bSwitchState,
    kind: u8,
    block_type: u16,
    block_length: u32,
) -> bool {
    &&& next.num_types == old.num_types
    &&& next.phase == B3bSwitchPhase::Ready
    &&& next.remaining@ == old.remaining@.update(kind as int, block_length)
    &&& next.ring@ == old.ring@
        .update(2 * kind as int, old.ring@[2 * kind as int + 1])
        .update(2 * kind as int + 1, block_type)
}

pub(crate) closed spec fn b3b_switch_transition_holds(
    old: B3bSwitchState,
    requested_kind: u8,
    type_symbol: Option<u16>,
    block_length: Option<u32>,
    result: B3bSwitchResult,
) -> bool {
    let k = requested_kind as int;
    match old.phase {
        B3bSwitchPhase::Failed(error) => {
            &&& result.state == old
            &&& result.consumed_fields == 0
            &&& result.outcome == B3bSwitchOutcome::Failed(error)
        },
        B3bSwitchPhase::AwaitLength { kind: waiting, block_type } => {
            if waiting != requested_kind {
                &&& b3b_arrays_unchanged(old, result.state)
                &&& result.state.phase == B3bSwitchPhase::Failed(
                    B3bSwitchFailure::InvalidSequence,
                )
                &&& result.consumed_fields == 0
                &&& result.outcome == B3bSwitchOutcome::Failed(
                    B3bSwitchFailure::InvalidSequence,
                )
            } else {
                match block_length {
                    None => {
                        &&& result.state == old
                        &&& result.consumed_fields == 0
                        &&& result.outcome == B3bSwitchOutcome::NeedInput
                    },
                    Some(0) => {
                        &&& b3b_arrays_unchanged(old, result.state)
                        &&& result.state.phase == B3bSwitchPhase::Failed(
                            B3bSwitchFailure::InvalidBlockLength,
                        )
                        &&& result.consumed_fields == 1
                        &&& result.outcome == B3bSwitchOutcome::Failed(
                            B3bSwitchFailure::InvalidBlockLength,
                        )
                    },
                    Some(length) => {
                        &&& b3b_updated(
                            old,
                            result.state,
                            requested_kind,
                            block_type,
                            length,
                        )
                        &&& result.consumed_fields == 1
                        &&& result.outcome == B3bSwitchOutcome::Complete {
                            kind: requested_kind,
                            block_type,
                            block_length: length,
                        }
                    },
                }
            }
        },
        B3bSwitchPhase::Ready => {
            let max_type = old.num_types@[k];
            if max_type <= 1 {
                &&& b3b_arrays_unchanged(old, result.state)
                &&& result.state.phase == B3bSwitchPhase::Failed(
                    B3bSwitchFailure::InvalidBlockSwitch,
                )
                &&& result.consumed_fields == 0
                &&& result.outcome == B3bSwitchOutcome::Failed(
                    B3bSwitchFailure::InvalidBlockSwitch,
                )
            } else {
                match type_symbol {
                    None => {
                        &&& result.state == old
                        &&& result.consumed_fields == 0
                        &&& result.outcome == B3bSwitchOutcome::NeedInput
                    },
                    Some(symbol) => {
                        if symbol >= max_type + 2 {
                            &&& b3b_arrays_unchanged(old, result.state)
                            &&& result.state.phase == B3bSwitchPhase::Failed(
                                B3bSwitchFailure::InvalidPrefixSymbol,
                            )
                            &&& result.consumed_fields == 1
                            &&& result.outcome == B3bSwitchOutcome::Failed(
                                B3bSwitchFailure::InvalidPrefixSymbol,
                            )
                        } else {
                            let block_type = resolved_type(
                                old.ring@[2 * k],
                                old.ring@[2 * k + 1],
                                max_type,
                                symbol,
                            );
                            match block_length {
                                None => {
                                    &&& b3b_arrays_unchanged(old, result.state)
                                    &&& result.state.phase == B3bSwitchPhase::AwaitLength {
                                        kind: requested_kind,
                                        block_type,
                                    }
                                    &&& result.consumed_fields == 1
                                    &&& result.outcome == B3bSwitchOutcome::NeedInput
                                },
                                Some(0) => {
                                    &&& b3b_arrays_unchanged(old, result.state)
                                    &&& result.state.phase == B3bSwitchPhase::Failed(
                                        B3bSwitchFailure::InvalidBlockLength,
                                    )
                                    &&& result.consumed_fields == 2
                                    &&& result.outcome == B3bSwitchOutcome::Failed(
                                        B3bSwitchFailure::InvalidBlockLength,
                                    )
                                },
                                Some(length) => {
                                    &&& b3b_updated(
                                        old,
                                        result.state,
                                        requested_kind,
                                        block_type,
                                        length,
                                    )
                                    &&& result.consumed_fields == 2
                                    &&& result.outcome == B3bSwitchOutcome::Complete {
                                        kind: requested_kind,
                                        block_type,
                                        block_length: length,
                                    }
                                },
                            }
                        }
                    },
                }
            }
        },
    }
}

impl BlockSwitchCore {
    spec fn valid(&self) -> bool {
        &&& declarations_valid(self.num_types@)
        &&& self.ring@[1] < self.num_types@[0]
        &&& self.ring@[3] < self.num_types@[1]
        &&& self.ring@[5] < self.num_types@[2]
        &&& self.ring@[0] <= self.num_types@[0]
        &&& self.ring@[2] <= self.num_types@[1]
        &&& self.ring@[4] <= self.num_types@[2]
        &&& (self.num_types@[0] > 1 ==> self.ring@[0] < self.num_types@[0])
        &&& (self.num_types@[1] > 1 ==> self.ring@[2] < self.num_types@[1])
        &&& (self.num_types@[2] > 1 ==> self.ring@[4] < self.num_types@[2])
        &&& match self.phase {
            SwitchPhase::AwaitLength { kind, block_type } => {
                let k = kind.index();
                &&& self.num_types@[k] > 1
                &&& block_type < self.num_types@[k]
                &&& self.remaining@[k] == 0
            },
            _ => true,
        }
    }

    fn new(num_types: [u16; 3]) -> (r: Result<Self, BlockSwitchError>)
        ensures r.is_ok() ==> r.unwrap().valid(),
            r.is_err() ==> r == Err(BlockSwitchError::InvalidDeclaration),
    {
        if num_types[0] == 0 || num_types[0] > 256
            || num_types[1] == 0 || num_types[1] > 256
            || num_types[2] == 0 || num_types[2] > 256
        {
            return Err(BlockSwitchError::InvalidDeclaration);
        }
        Ok(Self {
            num_types,
            ring: [1, 0, 1, 0, 1, 0],
            remaining: [0, 0, 0],
            phase: SwitchPhase::Ready,
        })
    }

    fn reset(&mut self)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).num_types == old(self).num_types,
            final(self).ring == [1, 0, 1, 0, 1, 0],
            final(self).remaining == [0, 0, 0],
            final(self).phase == SwitchPhase::Ready,
    {
        self.ring = [1, 0, 1, 0, 1, 0];
        self.remaining = [0, 0, 0];
        self.phase = SwitchPhase::Ready;
    }

    fn consume(&mut self, kind: BlockKind, amount: u32)
        requires old(self).valid(), amount <= old(self).remaining@[kind.index()],
        ensures final(self).valid(), final(self).num_types == old(self).num_types,
            final(self).ring == old(self).ring,
            final(self).phase == old(self).phase,
            final(self).remaining@[kind.index()]
                == old(self).remaining@[kind.index()] - amount,
            forall|k: int| 0 <= k < 3 && k != kind.index()
                ==> final(self).remaining@[k] == old(self).remaining@[k],
    {
        let k = kind.as_index();
        self.remaining[k] = self.remaining[k] - amount;
    }

    fn advance(
        &mut self,
        kind: BlockKind,
        type_symbol: Option<u16>,
        block_length: Option<u32>,
    ) -> (r: SwitchStep)
        requires old(self).valid(),
            match old(self).phase {
                SwitchPhase::Ready => old(self).remaining@[kind.index()] == 0,
                _ => true,
            },
        ensures final(self).valid(), r.consumed_fields <= 2,
            switch_transition_holds(
                *old(self),
                kind,
                type_symbol,
                block_length,
                *final(self),
                r,
            ),
            old(self).num_types == final(self).num_types,
            match old(self).phase {
                SwitchPhase::Failed(error) => r == SwitchStep {
                    consumed_fields: 0,
                    status: SwitchStatus::Failed(error),
                } && *final(self) == *old(self),
                _ => true,
            },
            old(self).phase == SwitchPhase::Ready
                && old(self).num_types@[kind.index()] <= 1
                ==> r == (SwitchStep { consumed_fields: 0,
                    status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch) })
                    && final(self).phase == SwitchPhase::Failed(BlockSwitchError::InvalidBlockSwitch)
                    && final(self).ring == old(self).ring
                    && final(self).remaining == old(self).remaining,
            old(self).phase == SwitchPhase::Ready
                && old(self).num_types@[kind.index()] > 1
                && type_symbol.is_some() && block_length.is_some()
                ==> r.status != SwitchStatus::NeedInput,
            match r.status {
                SwitchStatus::NeedInput => {
                    &&& match final(self).phase {
                        SwitchPhase::Failed(_) => false,
                        _ => true,
                    }
                    &&& old(self).num_types@[kind.index()] > 1
                },
                SwitchStatus::Failed(error) =>
                    final(self).phase == SwitchPhase::Failed(error),
                SwitchStatus::Complete { kind: completed_kind, block_type, block_length } => {
                    &&& completed_kind == kind
                    &&& block_length > 0
                    &&& block_type < final(self).num_types@[kind.index()]
                    &&& final(self).phase == SwitchPhase::Ready
                    &&& final(self).remaining@[kind.index()] == block_length
                    &&& final(self).ring@[2 * kind.index()]
                        == old(self).ring@[2 * kind.index() + 1]
                    &&& final(self).ring@[2 * kind.index() + 1] == block_type
                },
            },
    {
        let ghost before = *self;
        match self.phase {
            SwitchPhase::Failed(error) => {
                proof { assert(*self == before); }
                return SwitchStep { consumed_fields: 0, status: SwitchStatus::Failed(error) };
            }
            SwitchPhase::AwaitLength { kind: waiting, block_type } => {
                proof {
                    assert(before.phase == SwitchPhase::AwaitLength { kind: waiting, block_type });
                }
                if !same_kind(waiting, kind) {
                    self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidSequence);
                    proof { assert(self.valid()); }
                    return SwitchStep { consumed_fields: 0,
                        status: SwitchStatus::Failed(BlockSwitchError::InvalidSequence) };
                }
                proof {
                    assert(waiting == kind);
                    assert(waiting.index() == kind.index());
                }
                let length = match block_length {
                    None => {
                        proof { assert(*self == before); }
                        return SwitchStep { consumed_fields: 0, status: SwitchStatus::NeedInput };
                    }
                    Some(value) => value,
                };
                if length == 0 {
                    self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidBlockLength);
                    proof { assert(self.valid()); }
                    return SwitchStep { consumed_fields: 1,
                        status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockLength) };
                }
                let k = kind.as_index();
                self.ring[2 * k] = self.ring[2 * k + 1];
                self.ring[2 * k + 1] = block_type;
                self.remaining[k] = length;
                self.phase = SwitchPhase::Ready;
                proof { assert(self.valid()); }
                return SwitchStep { consumed_fields: 1,
                    status: SwitchStatus::Complete { kind, block_type, block_length: length } };
            }
            SwitchPhase::Ready => {
                proof { assert(before.phase == SwitchPhase::Ready); }
            }
        }

        let k = kind.as_index();
        let max_type = self.num_types[k];
        if max_type <= 1 {
            self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidBlockSwitch);
            return SwitchStep { consumed_fields: 0,
                status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch) };
        }
        let symbol = match type_symbol {
            None => return SwitchStep { consumed_fields: 0, status: SwitchStatus::NeedInput },
            Some(value) => value,
        };
        if symbol >= max_type + 2 {
            self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidPrefixSymbol);
            return SwitchStep { consumed_fields: 1,
                status: SwitchStatus::Failed(BlockSwitchError::InvalidPrefixSymbol) };
        }
        let block_type = resolve_type(self.ring[2 * k], self.ring[2 * k + 1], max_type, symbol);
        let length = match block_length {
            None => {
                self.phase = SwitchPhase::AwaitLength { kind, block_type };
                return SwitchStep { consumed_fields: 1, status: SwitchStatus::NeedInput };
            }
            Some(value) => value,
        };
        if length == 0 {
            self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidBlockLength);
            return SwitchStep { consumed_fields: 2,
                status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockLength) };
        }
        self.ring[2 * k] = self.ring[2 * k + 1];
        self.ring[2 * k + 1] = block_type;
        self.remaining[k] = length;
        self.phase = SwitchPhase::Ready;
        SwitchStep { consumed_fields: 2,
            status: SwitchStatus::Complete { kind, block_type, block_length: length } }
    }

    fn advance_literal(&mut self, symbol: Option<u16>, length: Option<u32>) -> (r: SwitchStep)
        requires old(self).valid(),
            old(self).phase == SwitchPhase::Ready,
            old(self).remaining@[BlockKind::Literal.index()] == 0,
        ensures final(self).valid(),
    {
        self.advance(BlockKind::Literal, symbol, length)
    }

    fn advance_command(&mut self, symbol: Option<u16>, length: Option<u32>) -> (r: SwitchStep)
        requires old(self).valid(),
            old(self).phase == SwitchPhase::Ready,
            old(self).remaining@[BlockKind::Command.index()] == 0,
        ensures final(self).valid(),
    {
        self.advance(BlockKind::Command, symbol, length)
    }

    fn advance_distance(&mut self, symbol: Option<u16>, length: Option<u32>) -> (r: SwitchStep)
        requires old(self).valid(),
            old(self).phase == SwitchPhase::Ready,
            old(self).remaining@[BlockKind::Distance.index()] == 0,
        ensures final(self).valid(),
    {
        self.advance(BlockKind::Distance, symbol, length)
    }

    fn advance_from_prefixes(
        &mut self,
        kind: BlockKind,
        type_code: &PrefixCode,
        type_bits: u32,
        type_width: u8,
        length_symbol: u8,
        length_suffix: u32,
    ) -> (r: SwitchStep)
        requires old(self).valid(), old(self).phase == SwitchPhase::Ready,
            old(self).remaining@[kind.index()] == 0,
            1 <= type_width <= 15, type_code.symbols <= 258,
        ensures final(self).valid(),
            old(self).num_types@[kind.index()] <= 1 ==> {
                &&& r == (SwitchStep { consumed_fields: 0,
                    status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch) })
                &&& final(self).phase
                    == SwitchPhase::Failed(BlockSwitchError::InvalidBlockSwitch)
            },
            r.status != SwitchStatus::NeedInput,
    {
        let k = kind.as_index();
        if self.num_types[k] <= 1 {
            return self.advance(kind, None, None);
        }
        let symbol = match type_code.decode_exact(type_bits, type_width) {
            Some(value) => value,
            None => {
                self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidPrefixSymbol);
                return SwitchStep { consumed_fields: 1,
                    status: SwitchStatus::Failed(BlockSwitchError::InvalidPrefixSymbol) };
            }
        };
        let length = match decode_block_length(length_symbol, length_suffix) {
            Ok(value) => value,
            Err(_) => {
                self.phase = SwitchPhase::Failed(BlockSwitchError::InvalidBlockLength);
                return SwitchStep { consumed_fields: 2,
                    status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockLength) };
            }
        };
        self.advance(kind, Some(symbol), Some(length))
    }
}

pub(crate) fn advance_b3b_switch(
    state: B3bSwitchState,
    requested_kind: u8,
    type_symbol: Option<u16>,
    block_length: Option<u32>,
) -> (r: B3bSwitchResult)
    requires state.valid(), requested_kind < 3,
        state.phase == B3bSwitchPhase::Ready
            ==> state.remaining@[requested_kind as int] == 0,
    ensures
        r.state.valid(),
        r.consumed_fields <= 2,
        b3b_switch_transition_holds(
            state,
            requested_kind,
            type_symbol,
            block_length,
            r,
        ),
        r.state.num_types == state.num_types,
        match state.phase {
            B3bSwitchPhase::Failed(error) => {
                &&& r.state == state
                &&& r.consumed_fields == 0
                &&& r.outcome == B3bSwitchOutcome::Failed(error)
            },
            _ => true,
        },
        state.phase == B3bSwitchPhase::Ready
            && state.num_types@[requested_kind as int] <= 1
            ==> {
                &&& r.consumed_fields == 0
                &&& r.outcome == B3bSwitchOutcome::Failed(
                    B3bSwitchFailure::InvalidBlockSwitch,
                )
                &&& r.state.phase == B3bSwitchPhase::Failed(
                    B3bSwitchFailure::InvalidBlockSwitch,
                )
                &&& r.state.ring == state.ring
                &&& r.state.remaining == state.remaining
            },
        match r.outcome {
            B3bSwitchOutcome::NeedInput => {
                &&& state.num_types@[requested_kind as int] > 1
                &&& match r.state.phase {
                    B3bSwitchPhase::Failed(_) => false,
                    _ => true,
                }
            },
            B3bSwitchOutcome::Complete {
                kind, block_type, block_length,
            } => {
                &&& kind == requested_kind
                &&& block_length > 0
                &&& block_type < r.state.num_types@[requested_kind as int]
                &&& r.state.phase == B3bSwitchPhase::Ready
                &&& r.state.remaining@[requested_kind as int] == block_length
            },
            B3bSwitchOutcome::Failed(error) => {
                &&& r.state.phase == B3bSwitchPhase::Failed(error)
            },
        },
{
    if let B3bSwitchPhase::Failed(error) = state.phase {
        return B3bSwitchResult {
            state,
            consumed_fields: 0,
            outcome: B3bSwitchOutcome::Failed(error),
        };
    }
    let requested = b3b_kind_to_b2(requested_kind);
    let mut core = restore_b3b_switch(state);
    proof {
        match state.phase {
            B3bSwitchPhase::Ready => {
                assert(core.phase == SwitchPhase::Ready);
                assert(core.remaining@[requested.index()]
                    == state.remaining@[requested_kind as int]);
            },
            B3bSwitchPhase::AwaitLength { .. } => {},
            B3bSwitchPhase::Failed(_) => { assert(false); },
        }
    }
    let step = core.advance(requested, type_symbol, block_length);
    let next_state = snapshot_b3b_switch(core);
    let outcome = match step.status {
        SwitchStatus::NeedInput => B3bSwitchOutcome::NeedInput,
        SwitchStatus::Complete { kind, block_type, block_length } => {
            B3bSwitchOutcome::Complete {
                kind: b2_kind_to_b3b(kind),
                block_type,
                block_length,
            }
        }
        SwitchStatus::Failed(error) => {
            B3bSwitchOutcome::Failed(b2_failure_to_b3b(error))
        }
    };
    B3bSwitchResult {
        state: next_state,
        consumed_fields: step.consumed_fields,
        outcome,
    }
}

}

#[cfg(test)]
mod tests {
    use super::*;

    fn adapter_state(num_types: [u16; 3]) -> B3bSwitchState {
        B3bSwitchState {
            num_types,
            ring: [1, 0, 1, 0, 1, 0],
            remaining: [0, 0, 0],
            phase: B3bSwitchPhase::Ready,
        }
    }

    #[test]
    fn b3b_adapter_preserves_switch_completion_suspension_and_failure() {
        let completed = advance_b3b_switch(adapter_state([3, 4, 2]), 0, Some(1), Some(9));
        assert_eq!(completed.consumed_fields, 2);
        assert_eq!(
            completed.outcome,
            B3bSwitchOutcome::Complete {
                kind: 0,
                block_type: 1,
                block_length: 9,
            }
        );
        assert_eq!(completed.state.remaining[0], 9);
        assert_eq!(completed.state.ring[..2], [0, 1]);

        let waiting = advance_b3b_switch(adapter_state([3, 4, 2]), 1, Some(3), None);
        assert_eq!(waiting.consumed_fields, 1);
        assert_eq!(waiting.outcome, B3bSwitchOutcome::NeedInput);
        assert_eq!(
            waiting.state.phase,
            B3bSwitchPhase::AwaitLength {
                kind: 1,
                block_type: 1,
            }
        );
        let resumed = advance_b3b_switch(waiting.state, 1, None, Some(7));
        assert_eq!(
            resumed.outcome,
            B3bSwitchOutcome::Complete {
                kind: 1,
                block_type: 1,
                block_length: 7,
            }
        );

        let failed = advance_b3b_switch(adapter_state([1, 4, 2]), 0, None, None);
        assert_eq!(
            failed.outcome,
            B3bSwitchOutcome::Failed(B3bSwitchFailure::InvalidBlockSwitch)
        );
        let sticky = advance_b3b_switch(failed.state, 0, Some(0), Some(1));
        assert_eq!(sticky.state, failed.state);
        assert_eq!(sticky.consumed_fields, 0);
        assert_eq!(sticky.outcome, failed.outcome);
    }

    #[test]
    fn all_three_integration_paths_preserve_status() {
        let mut core = BlockSwitchCore::new([3, 4, 2]).unwrap();
        assert_eq!(
            core.advance_literal(Some(1), Some(9)).status,
            SwitchStatus::Complete {
                kind: BlockKind::Literal,
                block_type: 1,
                block_length: 9
            }
        );
        assert_eq!(
            core.advance_command(Some(3), Some(7)).status,
            SwitchStatus::Complete {
                kind: BlockKind::Command,
                block_type: 1,
                block_length: 7
            }
        );
        assert_eq!(
            core.advance_distance(Some(0), Some(5)).status,
            SwitchStatus::Complete {
                kind: BlockKind::Distance,
                block_type: 1,
                block_length: 5
            }
        );
    }

    #[test]
    fn invalid_single_type_switch_is_permanent_without_field_reads() {
        let mut core = BlockSwitchCore::new([1, 2, 2]).unwrap();
        let first = core.advance_literal(None, None);
        assert_eq!(first.consumed_fields, 0);
        assert_eq!(
            first.status,
            SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch)
        );
        let retry = core.advance(BlockKind::Literal, Some(0), Some(1));
        assert_eq!(
            retry,
            SwitchStep {
                consumed_fields: 0,
                status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch)
            }
        );
    }

    #[test]
    fn suspension_retains_type_and_wrong_sequence_fails() {
        let mut core = BlockSwitchCore::new([3, 3, 3]).unwrap();
        assert_eq!(
            core.advance_literal(Some(1), None),
            SwitchStep {
                consumed_fields: 1,
                status: SwitchStatus::NeedInput
            }
        );
        assert_eq!(
            core.advance(BlockKind::Literal, None, None),
            SwitchStep {
                consumed_fields: 0,
                status: SwitchStatus::NeedInput
            }
        );
        assert_eq!(
            core.advance(BlockKind::Literal, None, Some(11)).status,
            SwitchStatus::Complete {
                kind: BlockKind::Literal,
                block_type: 1,
                block_length: 11
            }
        );
        core.consume(BlockKind::Literal, 11);
        assert_eq!(
            core.advance_literal(Some(0), None).status,
            SwitchStatus::NeedInput
        );
        assert_eq!(
            core.advance(BlockKind::Command, None, Some(4)).status,
            SwitchStatus::Failed(BlockSwitchError::InvalidSequence)
        );
    }

    #[test]
    fn reset_is_the_only_terminal_recovery() {
        let mut core = BlockSwitchCore::new([1, 2, 2]).unwrap();
        assert!(matches!(
            core.advance_literal(None, None).status,
            SwitchStatus::Failed(_)
        ));
        assert!(matches!(
            core.advance_command(Some(0), Some(1)).status,
            SwitchStatus::Failed(_)
        ));
        core.reset();
        assert_eq!(
            core.advance_command(Some(1), Some(4)).status,
            SwitchStatus::Complete {
                kind: BlockKind::Command,
                block_type: 1,
                block_length: 4
            }
        );
    }

    #[test]
    fn canonical_prefix_results_reach_the_real_switch_transition() {
        let code = PrefixCode::from_lengths(&[1, 2, 3, 3]).unwrap();
        let mut core = BlockSwitchCore::new([3, 3, 3]).unwrap();
        assert_eq!(
            core.advance_from_prefixes(BlockKind::Literal, &code, 2, 2, 0, 3),
            SwitchStep {
                consumed_fields: 2,
                status: SwitchStatus::Complete {
                    kind: BlockKind::Literal,
                    block_type: 1,
                    block_length: 4
                }
            },
        );

        let mut invalid = BlockSwitchCore::new([1, 3, 3]).unwrap();
        assert_eq!(
            invalid.advance_from_prefixes(BlockKind::Literal, &code, 99, 2, 99, u32::MAX,),
            SwitchStep {
                consumed_fields: 0,
                status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch)
            },
        );
    }
}
