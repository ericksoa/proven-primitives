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

}

#[cfg(test)]
mod tests {
    use super::*;

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
