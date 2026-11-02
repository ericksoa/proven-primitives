//! Immutable RFC tables for the checked Brotli B3c decoder.
//!
//! Sources are pinned to google/brotli v1.2.1 commit
//! db24a98aed38a16de78cc05ca15cdd8dc2a0d92d. See
//! BROTLI_B3C_PROPOSAL.md for exact file hashes and binary encodings.

#![allow(dead_code)]

use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CommandEntry {
    pub(crate) insert_extra_bits: u8,
    pub(crate) copy_extra_bits: u8,
    pub(crate) distance_mode: i8,
    pub(crate) distance_context: u8,
    pub(crate) insert_offset: u16,
    pub(crate) copy_offset: u16,
}



impl CommandEntry {
    pub(crate) open spec fn valid(&self) -> bool {
        &&& self.insert_extra_bits <= 24
        &&& self.copy_extra_bits <= 24
        &&& (self.distance_mode == -1 || self.distance_mode == 0)
        &&& self.distance_context < 4
        &&& self.copy_offset >= 2
    }
}

pub(crate) const COMMAND_SYMBOLS: usize = 704;

pub(crate) const INSERT_LENGTH_EXTRA_BITS: [u8; 24] = [
    0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3,
    4, 4, 5, 5, 6, 7, 8, 9, 10, 12, 14, 24,
];

pub(crate) const COPY_LENGTH_EXTRA_BITS: [u8; 24] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2,
    3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24,
];

pub(crate) const INSERT_LENGTH_OFFSETS: [u16; 24] = [
    0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 18, 26,
    34, 50, 66, 98, 130, 194, 322, 578, 1090, 2114, 6210, 22594,
];

pub(crate) const COPY_LENGTH_OFFSETS: [u16; 24] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18,
    22, 30, 38, 54, 70, 102, 134, 198, 326, 582, 1094, 2118,
];

pub(crate) open spec fn command_cell_position_spec(cell: nat) -> nat {
    if cell == 0 { 0 }
    else if cell == 1 { 1 }
    else if cell == 2 { 0 }
    else if cell == 3 { 1 }
    else if cell == 4 { 8 }
    else if cell == 5 { 9 }
    else if cell == 6 { 2 }
    else if cell == 7 { 16 }
    else if cell == 8 { 10 }
    else if cell == 9 { 17 }
    else if cell == 10 { 18 }
    else { 0 }
}

pub(crate) open spec fn command_copy_code_spec(symbol: u16) -> nat {
    let cell = symbol as nat / 64;
    let position = command_cell_position_spec(cell);
    (position % 8) * 8 + symbol as nat % 8
}

pub(crate) open spec fn command_insert_code_spec(symbol: u16) -> nat {
    let cell = symbol as nat / 64;
    let position = command_cell_position_spec(cell);
    (position / 8) * 8 + (symbol as nat / 8) % 8
}

pub(crate) fn command_entry_formula(symbol: u16) -> (r: CommandEntry)
    requires symbol < COMMAND_SYMBOLS,
    ensures
        r.valid(),
        r.distance_mode == if symbol as nat / 64 >= 2 { -1i8 } else { 0i8 },
        r.distance_context == if r.copy_offset <= 4 {
            (r.copy_offset - 2) as u8
        } else {
            3u8
        },
{
    let cell = symbol as usize / 64;
    let position = match cell {
        0 => 0usize, 1 => 1, 2 => 0, 3 => 1, 4 => 8, 5 => 9,
        6 => 2, 7 => 16, 8 => 10, 9 => 17, 10 => 18,
        _ => 0,
    };
    let copy_code = (position % 8) * 8 + symbol as usize % 8;
    let insert_code = (position / 8) * 8 + (symbol as usize / 8) % 8;
    proof {
        reveal(command_cell_position_spec);
        reveal(command_copy_code_spec);
        reveal(command_insert_code_spec);
        assert(cell <= 10);
        assert(position <= 18);
        assert(copy_code < 24);
        assert(insert_code < 24);
    }
    let copy_offset = COPY_LENGTH_OFFSETS[copy_code];
    let entry = CommandEntry {
        insert_extra_bits: INSERT_LENGTH_EXTRA_BITS[insert_code],
        copy_extra_bits: COPY_LENGTH_EXTRA_BITS[copy_code],
        distance_mode: if cell >= 2 { -1 } else { 0 },
        distance_context: if copy_offset <= 4 { (copy_offset - 2) as u8 } else { 3 },
        insert_offset: INSERT_LENGTH_OFFSETS[insert_code],
        copy_offset,
    };
    if entry.insert_extra_bits > 24
        || entry.copy_extra_bits > 24
        || entry.copy_offset < 2
        || entry.distance_context >= 4
    {
        return CommandEntry {
            insert_extra_bits: 0,
            copy_extra_bits: 0,
            distance_mode: if cell >= 2 { -1 } else { 0 },
            distance_context: 0,
            insert_offset: 0,
            copy_offset: 2,
        };
    }
    entry
}

pub(crate) const COMMAND_TABLE: [CommandEntry; COMMAND_SYMBOLS] = [
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 0, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 0, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 0, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 1, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 1, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 1, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 2, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 2, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 2, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 3, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 3, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 3, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 4, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 4, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 4, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 5, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 5, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 5, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 6, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 6, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 6, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 0, insert_offset: 8, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 1, insert_offset: 8, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 2, insert_offset: 8, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 0, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 1, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 2, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 3, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 4, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 5, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 6, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: 0, distance_context: 3, insert_offset: 8, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 0, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 0, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 0, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 1, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 1, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 1, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 2, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 2, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 2, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 3, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 3, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 3, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 4, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 4, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 4, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 5, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 5, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 5, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 6, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 6, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 6, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 8, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 8, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 8, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 10, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 10, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 10, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 14, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 14, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 14, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 18, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 18, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 18, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 26, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 26, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 26, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 34, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 34, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 34, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 50, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 50, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 50, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 66, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 66, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 66, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 98, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 98, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 98, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 0, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 1, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 2, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 3, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 4, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 0, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 5, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 6, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 1, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 8, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 130, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 130, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 130, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 194, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 194, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 194, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 322, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 322, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 322, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 578, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 578, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 578, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 1090, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 1090, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 1090, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 2114, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 2114, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 2114, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 6210, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 6210, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 6210, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 0, insert_offset: 22594, copy_offset: 2 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 1, insert_offset: 22594, copy_offset: 3 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 2, insert_offset: 22594, copy_offset: 4 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 5 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 6 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 7 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 8 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 0, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 9 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 10, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 2, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 14, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 18, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 3, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 26, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 34, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 4, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 50, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 66, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 5, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 98, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 10 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 1, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 12 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 14 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 2, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 18 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 22 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 3, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 30 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 38 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 4, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 54 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 6, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 130, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 7, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 194, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 8, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 322, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 9, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 578, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 10, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 1090, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 12, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 2114, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 14, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 6210, copy_offset: 2118 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 70 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 5, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 102 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 6, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 134 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 7, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 198 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 8, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 326 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 9, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 582 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 10, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 1094 },
    CommandEntry { insert_extra_bits: 24, copy_extra_bits: 24, distance_mode: -1, distance_context: 3, insert_offset: 22594, copy_offset: 2118 },
];

pub(crate) fn command_entry(symbol: u16) -> (r: CommandEntry)
    requires symbol < COMMAND_SYMBOLS,
    ensures r == COMMAND_TABLE@[symbol as int],
{
    COMMAND_TABLE[symbol as usize]
}

pub(crate) const LITERAL_CONTEXT_TABLE: [u8; 2048] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
    4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7,
    8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11,
    12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15,
    16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19,
    20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23,
    24, 24, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27,
    28, 28, 28, 28, 29, 29, 29, 29, 30, 30, 30, 30, 31, 31, 31, 31,
    32, 32, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 35, 35,
    36, 36, 36, 36, 37, 37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39,
    40, 40, 40, 40, 41, 41, 41, 41, 42, 42, 42, 42, 43, 43, 43, 43,
    44, 44, 44, 44, 45, 45, 45, 45, 46, 46, 46, 46, 47, 47, 47, 47,
    48, 48, 48, 48, 49, 49, 49, 49, 50, 50, 50, 50, 51, 51, 51, 51,
    52, 52, 52, 52, 53, 53, 53, 53, 54, 54, 54, 54, 55, 55, 55, 55,
    56, 56, 56, 56, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 59, 59,
    60, 60, 60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 63,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 4, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    8, 12, 16, 12, 12, 20, 12, 16, 24, 28, 12, 12, 32, 12, 36, 12,
    44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 32, 32, 24, 40, 28, 12,
    12, 48, 52, 52, 52, 48, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48,
    52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 24, 12, 28, 12, 12,
    12, 56, 60, 60, 60, 56, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56,
    60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 24, 12, 28, 12, 0,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1,
    1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1,
    1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
    40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
    40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40,
    48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 56,
    0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7,
];

pub(crate) fn literal_context(mode: u8, previous: u8, second_previous: u8) -> (r: u8)
    requires mode < 4,
    ensures r == (LITERAL_CONTEXT_TABLE@[(mode as int) * 512 + previous as int]
        | LITERAL_CONTEXT_TABLE@[(mode as int) * 512 + 256 + second_previous as int]),
{
    let base = mode as usize * 512;
    LITERAL_CONTEXT_TABLE[base + previous as usize]
        | LITERAL_CONTEXT_TABLE[base + 256 + second_previous as usize]
}

pub(crate) const DICTIONARY_SIZE_BITS: [u8; 32] = [
    0, 0, 0, 0, 10, 10, 11, 11, 10, 10, 10, 10, 10, 9, 9, 8,
    7, 7, 8, 7, 7, 6, 6, 5, 5, 0, 0, 0, 0, 0, 0, 0,
];

pub(crate) const DICTIONARY_OFFSETS: [u32; 32] = [
    0, 0, 0, 0, 0, 4096, 9216, 21504,
    35840, 44032, 53248, 63488, 74752, 87040, 93696, 100864,
    104704, 106752, 108928, 113536, 115968, 118528, 119872, 121280,
    122016, 122784, 122784, 122784, 122784, 122784, 122784, 122784,
];

pub(crate) fn dictionary_size_bits(length: u8) -> (r: u8)
    requires length < 32,
    ensures r == DICTIONARY_SIZE_BITS@[length as int],
{
    DICTIONARY_SIZE_BITS[length as usize]
}

pub(crate) fn dictionary_offset(length: u8) -> (r: u32)
    requires length < 32,
    ensures r == DICTIONARY_OFFSETS@[length as int],
{
    DICTIONARY_OFFSETS[length as usize]
}

pub(crate) const PREFIX_SUFFIX_BYTES: [u8; 217] = [
    1, 32, 2, 44, 32, 8, 32, 111, 102, 32, 116, 104, 101, 32, 4, 32,
    111, 102, 32, 2, 115, 32, 1, 46, 5, 32, 97, 110, 100, 32, 4, 32,
    105, 110, 32, 1, 34, 4, 32, 116, 111, 32, 2, 34, 62, 1, 10, 2,
    46, 32, 1, 93, 5, 32, 102, 111, 114, 32, 3, 32, 97, 32, 6, 32,
    116, 104, 97, 116, 32, 1, 39, 6, 32, 119, 105, 116, 104, 32, 6, 32,
    102, 114, 111, 109, 32, 4, 32, 98, 121, 32, 1, 40, 6, 46, 32, 84,
    104, 101, 32, 4, 32, 111, 110, 32, 4, 32, 97, 115, 32, 4, 32, 105,
    115, 32, 4, 105, 110, 103, 32, 2, 10, 9, 1, 58, 3, 101, 100, 32,
    2, 61, 34, 4, 32, 97, 116, 32, 3, 108, 121, 32, 1, 44, 2, 61,
    39, 5, 46, 99, 111, 109, 47, 7, 46, 32, 84, 104, 105, 115, 32, 5,
    32, 110, 111, 116, 32, 3, 101, 114, 32, 3, 97, 108, 32, 4, 102, 117,
    108, 32, 4, 105, 118, 101, 32, 5, 108, 101, 115, 115, 32, 4, 101, 115,
    116, 32, 4, 105, 122, 101, 32, 2, 194, 160, 4, 111, 117, 115, 32, 5,
    32, 116, 104, 101, 32, 2, 101, 32, 0,
];

pub(crate) const PREFIX_SUFFIX_MAP: [u16; 50] = [
    0, 2, 5, 14, 19, 22, 24, 30, 35, 37,
    42, 45, 47, 50, 52, 58, 62, 69, 71, 78,
    85, 90, 92, 99, 104, 109, 114, 119, 122, 124,
    128, 131, 136, 140, 142, 145, 151, 159, 165, 169,
    173, 178, 183, 189, 194, 199, 202, 207, 213, 216,
];

pub(crate) const TRANSFORM_RECORDS: [u8; 363] = [
    49, 0, 49, 49, 0, 0, 0, 0, 0, 49, 12, 49,
    49, 10, 0, 49, 0, 47, 0, 0, 49, 4, 0, 0,
    49, 0, 3, 49, 10, 49, 49, 0, 6, 49, 13, 49,
    49, 1, 49, 1, 0, 0, 49, 0, 1, 0, 10, 0,
    49, 0, 7, 49, 0, 9, 48, 0, 0, 49, 0, 8,
    49, 0, 5, 49, 0, 10, 49, 0, 11, 49, 3, 49,
    49, 0, 13, 49, 0, 14, 49, 14, 49, 49, 2, 49,
    49, 0, 15, 49, 0, 16, 0, 10, 49, 49, 0, 12,
    5, 0, 49, 0, 0, 1, 49, 15, 49, 49, 0, 18,
    49, 0, 17, 49, 0, 19, 49, 0, 20, 49, 16, 49,
    49, 17, 49, 47, 0, 49, 49, 4, 49, 49, 0, 22,
    49, 11, 49, 49, 0, 23, 49, 0, 24, 49, 0, 25,
    49, 7, 49, 49, 1, 26, 49, 0, 27, 49, 0, 28,
    0, 0, 12, 49, 0, 29, 49, 20, 49, 49, 18, 49,
    49, 6, 49, 49, 0, 21, 49, 10, 1, 49, 8, 49,
    49, 0, 31, 49, 0, 32, 47, 0, 3, 49, 5, 49,
    49, 9, 49, 0, 10, 1, 49, 10, 8, 5, 0, 21,
    49, 11, 0, 49, 10, 10, 49, 0, 30, 0, 0, 5,
    35, 0, 49, 47, 0, 2, 49, 10, 17, 49, 0, 36,
    49, 0, 33, 5, 0, 0, 49, 10, 21, 49, 10, 5,
    49, 0, 37, 0, 0, 30, 49, 0, 38, 0, 11, 0,
    49, 0, 39, 0, 11, 49, 49, 0, 34, 49, 11, 8,
    49, 10, 12, 0, 0, 21, 49, 0, 40, 0, 10, 12,
    49, 0, 41, 49, 0, 42, 49, 11, 17, 49, 0, 43,
    0, 10, 5, 49, 11, 10, 0, 0, 34, 49, 10, 33,
    49, 0, 44, 49, 11, 5, 45, 0, 49, 0, 0, 33,
    49, 10, 30, 49, 11, 30, 49, 0, 46, 49, 11, 1,
    49, 10, 34, 0, 10, 33, 0, 11, 30, 0, 11, 1,
    49, 11, 33, 49, 11, 21, 49, 11, 12, 0, 11, 5,
    49, 11, 34, 0, 11, 12, 0, 10, 30, 0, 11, 34,
    0, 10, 34,
];

pub(crate) const TRANSFORM_COUNT: usize = 121;

pub(crate) const DISTANCE_INDEX_DELTAS: [u8; 16] = [
    3, 2, 1, 0, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2,
];

pub(crate) const DISTANCE_VALUE_DELTAS: [i8; 16] = [
    0, 0, 0, 0, -1, 1, -2, 2, -3, 3, -1, 1, -2, 2, -3, 3,
];

pub(crate) fn distance_index_delta(symbol: u8) -> (r: u8)
    requires symbol < 16,
    ensures r == match symbol {
        0 => 3u8, 1 => 2u8, 2 => 1u8, 3 => 0u8,
        4 | 5 | 6 | 7 | 8 | 9 => 3u8,
        10 | 11 | 12 | 13 | 14 | 15 => 2u8,
        _ => 0u8,
    },
{
    match symbol {
        0 => 3, 1 => 2, 2 => 1, 3 => 0,
        4 | 5 | 6 | 7 | 8 | 9 => 3,
        10 | 11 | 12 | 13 | 14 | 15 => 2,
        _ => 0,
    }
}

pub(crate) fn distance_value_delta(symbol: u8) -> (r: i8)
    requires symbol < 16,
    ensures r == match symbol {
        0 | 1 | 2 | 3 => 0i8,
        4 | 10 => -1i8,
        5 | 11 => 1i8,
        6 | 12 => -2i8,
        7 | 13 => 2i8,
        8 | 14 => -3i8,
        9 | 15 => 3i8,
        _ => 0i8,
    },
{
    match symbol {
        0 | 1 | 2 | 3 => 0,
        4 | 10 => -1,
        5 | 11 => 1,
        6 | 12 => -2,
        7 | 13 => 2,
        8 | 14 => -3,
        9 | 15 => 3,
        _ => 0,
    }
}

pub(crate) fn transform_record(index: u8) -> (r: (u8, u8, u8))
    requires index < TRANSFORM_COUNT,
    ensures r.0 == TRANSFORM_RECORDS@[(index as int) * 3],
        r.1 == TRANSFORM_RECORDS@[(index as int) * 3 + 1],
        r.2 == TRANSFORM_RECORDS@[(index as int) * 3 + 2],
{
    let at = index as usize * 3;
    (TRANSFORM_RECORDS[at], TRANSFORM_RECORDS[at + 1], TRANSFORM_RECORDS[at + 2])
}

fn decoder_transform_record(index: u8) -> (r: (u8, u8, u8))
    requires index < TRANSFORM_COUNT,
    ensures
        index == 42 ==> r == (49u8, 4u8, 49u8),
        index != 42 ==> {
            &&& r.0 == TRANSFORM_RECORDS@[(index as int) * 3]
            &&& r.1 == TRANSFORM_RECORDS@[(index as int) * 3 + 1]
            &&& r.2 == TRANSFORM_RECORDS@[(index as int) * 3 + 2]
        },
{
    if index == 42 {
        (49, 4, 49)
    } else {
        transform_record(index)
    }
}

fn decoder_prefix_suffix(id: u8) -> (r: (usize, usize))
    requires id < 50,
    ensures
        id == 49 ==> r == (216usize, 0usize),
        id != 49 ==> {
            let at = PREFIX_SUFFIX_MAP@[id as int] as nat;
            if at < PREFIX_SUFFIX_BYTES.len() {
                &&& r.0 as nat == at
                &&& r.1 as nat == PREFIX_SUFFIX_BYTES@[at as int] as nat
            } else {
                &&& r.0 == PREFIX_SUFFIX_BYTES.len()
                &&& r.1 == 0
            }
        },
        r.0 <= PREFIX_SUFFIX_BYTES.len(),
        r.1 <= 255,
{
    if id == 49 {
        (216, 0)
    } else {
        let at = PREFIX_SUFFIX_MAP[id as usize] as usize;
        if at < PREFIX_SUFFIX_BYTES.len() {
            (at, PREFIX_SUFFIX_BYTES[at] as usize)
        } else {
            (PREFIX_SUFFIX_BYTES.len(), 0)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DictionaryTransformError {
    InvalidLength,
    InvalidIndex,
    InvalidTransform,
    InvalidData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TransformedWord {
    pub(crate) bytes: [u8; 40],
    pub(crate) len: u8,
}

pub(crate) open spec fn toggle_32_spec(byte: u8) -> nat {
    if ((byte as nat) / 32) % 2 == 0 {
        byte as nat + 32
    } else {
        (byte as nat - 32) as nat
    }
}

pub(crate) open spec fn toggle_5_spec(byte: u8) -> nat {
    let base = (byte as nat - (byte as nat) % 8) as nat;
    let low = (byte as nat) % 8;
    base + if low == 0 { 5nat }
        else if low == 1 { 4nat }
        else if low == 2 { 7nat }
        else if low == 3 { 6nat }
        else if low == 4 { 1nat }
        else if low == 5 { 0nat }
        else if low == 6 { 3nat }
        else { 2nat }
}

fn toggle_32(byte: u8) -> (r: u8)
    ensures r as nat == toggle_32_spec(byte),
{
    let block = byte / 32;
    if block % 2 == 0 {
        proof {
            assert(byte as nat <= 223);
        }
        byte + 32
    } else {
        proof {
            assert(byte as nat >= 32);
        }
        byte - 32
    }
}

fn toggle_5(byte: u8) -> (r: u8)
    ensures r as nat == toggle_5_spec(byte),
{
    let low = byte % 8;
    let mapped = if low == 0 { 5u8 }
        else if low == 1 { 4 }
        else if low == 2 { 7 }
        else if low == 3 { 6 }
        else if low == 4 { 1 }
        else if low == 5 { 0 }
        else if low == 6 { 3 }
        else { 2 };
    byte - low + mapped
}

pub(crate) open spec fn ferment_step_spec(
    before: Seq<u8>,
    start: usize,
    len: usize,
    position: usize,
) -> nat {
    let at = start + position;
    if before[at as int] < 0xc0 {
        1
    } else if before[at as int] < 0xe0 {
        2
    } else {
        3
    }
}

pub(crate) open spec fn ferment_bytes_spec(
    before: Seq<u8>,
    start: usize,
    len: usize,
    position: usize,
) -> Seq<u8> {
    let at = start + position;
    if before[at as int] < 0xc0 {
        if b'a' <= before[at as int] <= b'z' {
            before.update(at as int, (before[at as int] - 32) as u8)
        } else {
            before
        }
    } else if before[at as int] < 0xe0 {
        if position + 1 < len {
            before.update(
                at as int + 1,
                toggle_32_spec(before[at as int + 1]) as u8,
            )
        } else {
            before
        }
    } else if position + 2 < len {
        before.update(
            at as int + 2,
            toggle_5_spec(before[at as int + 2]) as u8,
        )
    } else {
        before
    }
}

pub(crate) open spec fn ferment_all_spec(
    bytes: Seq<u8>,
    start: usize,
    len: usize,
    position: usize,
) -> Seq<u8>
    decreases len - position,
{
    if position >= len {
        bytes
    } else {
        let next_bytes = ferment_bytes_spec(bytes, start, len, position);
        let step = ferment_step_spec(bytes, start, len, position);
        let advanced = position as nat + step;
        let next_position = if advanced < len { advanced } else { len as nat };
        ferment_all_spec(next_bytes, start, len, next_position as usize)
    }
}

fn ferment(bytes: &mut [u8; 40], start: usize, len: usize, position: usize) -> (r: usize)
    requires start + len <= 40, position < len,
    ensures
        1 <= r <= 3,
        r as nat == ferment_step_spec(old(bytes)@, start, len, position),
        final(bytes)@ == ferment_bytes_spec(old(bytes)@, start, len, position),
{
    let at = start + position;
    if bytes[at] < 0xc0 {
        if b'a' <= bytes[at] && bytes[at] <= b'z' {
            bytes[at] = bytes[at] - 32;
        }
        1
    } else if bytes[at] < 0xe0 {
        if position + 1 < len {
            bytes[at + 1] = toggle_32(bytes[at + 1]);
        }
        2
    } else {
        if position + 2 < len {
            bytes[at + 2] = toggle_5(bytes[at + 2]);
        }
        3
    }
}

fn copy_affix(
    output: &mut [u8; 40],
    output_start: usize,
    table_at: usize,
    length: usize,
)
    requires
        output_start + length <= 40,
        table_at + 1 + length <= PREFIX_SUFFIX_BYTES.len(),
    ensures
        final(output)@.len() == old(output)@.len(),
        forall|i: int| 0 <= i < length ==> #[trigger]
            final(output)@[output_start as int + i]
                == PREFIX_SUFFIX_BYTES@[table_at as int + 1 + i],
        forall|i: int| 0 <= i < 40
            && !(output_start <= i < output_start + length) ==> #[trigger]
                final(output)@[i] == old(output)@[i],
{
    let ghost before = output@;
    let mut i = 0usize;
    while i < length
        invariant
            i <= length,
            output_start + length <= 40,
            table_at + 1 + length <= PREFIX_SUFFIX_BYTES.len(),
            output@.len() == before.len(),
            forall|j: int| 0 <= j < i ==> #[trigger]
                output@[output_start as int + j]
                    == PREFIX_SUFFIX_BYTES@[table_at as int + 1 + j],
            forall|j: int| 0 <= j < 40
                && !(output_start <= j < output_start + i) ==> #[trigger]
                    output@[j] == before[j],
        decreases length - i,
    {
        output[output_start + i] = PREFIX_SUFFIX_BYTES[table_at + 1 + i];
        i += 1;
    }
}

fn copy_dictionary_slice(
    output: &mut [u8; 40],
    output_start: usize,
    source: usize,
    body_start: usize,
    length: usize,
)
    requires
        output_start + length <= 40,
        source + body_start + length <= crate::brotli_dictionary::RFC_DICTIONARY_LEN,
    ensures
        final(output)@.len() == old(output)@.len(),
        forall|i: int| 0 <= i < length ==> #[trigger]
            final(output)@[output_start as int + i]
                == crate::brotli_dictionary::RFC_DICTIONARY@[
                    source as int + body_start as int + i
                ],
        forall|i: int| 0 <= i < 40
            && !(output_start <= i < output_start + length) ==> #[trigger]
                final(output)@[i] == old(output)@[i],
{
    let ghost before = output@;
    let mut i = 0usize;
    while i < length
        invariant
            i <= length,
            output_start + length <= 40,
            source + body_start + length
                <= crate::brotli_dictionary::RFC_DICTIONARY_LEN,
            output@.len() == before.len(),
            forall|j: int| 0 <= j < i ==> #[trigger]
                output@[output_start as int + j]
                    == crate::brotli_dictionary::RFC_DICTIONARY@[
                        source as int + body_start as int + j
                    ],
            forall|j: int| 0 <= j < 40
                && !(output_start <= j < output_start + i) ==> #[trigger]
                    output@[j] == before[j],
        decreases length - i,
    {
        output[output_start + i] = crate::brotli_dictionary::dictionary_byte(
            source + body_start + i,
        );
        i += 1;
    }
}

fn validate_dictionary_transform_shape(
    length: u8,
    transform_index: u8,
) -> (r: Result<(), DictionaryTransformError>)
    ensures
        r.is_ok() ==> 4 <= length <= 24
            && (transform_index as usize) < TRANSFORM_COUNT,
        (length < 4 || length > 24)
            ==> r == Err(DictionaryTransformError::InvalidLength),
        4 <= length <= 24 && (transform_index as usize) >= TRANSFORM_COUNT
            ==> r == Err(DictionaryTransformError::InvalidTransform),
        4 <= length <= 24 && (transform_index as usize) < TRANSFORM_COUNT
            ==> r.is_ok(),
{
    if length < 4 || length > 24 {
        Err(DictionaryTransformError::InvalidLength)
    } else if transform_index as usize >= TRANSFORM_COUNT {
        Err(DictionaryTransformError::InvalidTransform)
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DictionaryTransformPlan {
    prefix_at: usize,
    prefix_len: usize,
    body_start: usize,
    body_len: usize,
    suffix_at: usize,
    suffix_len: usize,
    transform: u8,
}

spec fn decoder_transform_component(index: u8, component: nat) -> nat {
    if index == 42 {
        if component == 0 { 49 }
        else if component == 1 { 4 }
        else { 49 }
    } else {
        TRANSFORM_RECORDS@[(index as int) * 3 + component as int] as nat
    }
}

spec fn decoder_affix_at(id: nat) -> nat {
    if id == 49 {
        216
    } else {
        PREFIX_SUFFIX_MAP@[id as int] as nat
    }
}

spec fn decoder_affix_len(id: nat) -> nat {
    let at = decoder_affix_at(id);
    if id == 49 {
        0
    } else if at < PREFIX_SUFFIX_BYTES.len() {
        PREFIX_SUFFIX_BYTES@[at as int] as nat
    } else {
        0
    }
}

spec fn dictionary_transform_plan_matches(
    length: u8,
    transform_index: u8,
    plan: DictionaryTransformPlan,
) -> bool {
    let prefix_id = decoder_transform_component(transform_index, 0);
    let transform = decoder_transform_component(transform_index, 1);
    let suffix_id = decoder_transform_component(transform_index, 2);
    let prefix_at = decoder_affix_at(prefix_id);
    let prefix_len = decoder_affix_len(prefix_id);
    let suffix_at = decoder_affix_at(suffix_id);
    let suffix_len = decoder_affix_len(suffix_id);
    let omitted_first = if transform >= 12 {
        let amount = (transform - 11) as nat;
        if amount < length as nat { amount } else { length as nat }
    } else {
        0
    };
    let body_start = omitted_first;
    let body_len = if transform <= 9 {
        if transform < length as nat {
            (length as nat - transform) as nat
        } else {
            0
        }
    } else {
        (length as nat - omitted_first) as nat
    };
    &&& prefix_id < 50
    &&& suffix_id < 50
    &&& transform <= 20
    &&& prefix_at < PREFIX_SUFFIX_BYTES.len()
    &&& suffix_at < PREFIX_SUFFIX_BYTES.len()
    &&& prefix_at + 1 + prefix_len <= PREFIX_SUFFIX_BYTES.len()
    &&& suffix_at + 1 + suffix_len <= PREFIX_SUFFIX_BYTES.len()
    &&& prefix_len + body_len + suffix_len <= 37
    &&& plan.prefix_at as nat == prefix_at
    &&& plan.prefix_len as nat == prefix_len
    &&& plan.body_start as nat == body_start
    &&& plan.body_len as nat == body_len
    &&& plan.suffix_at as nat == suffix_at
    &&& plan.suffix_len as nat == suffix_len
    &&& plan.transform as nat == transform
}

spec fn initial_dictionary_transform_buffer(
    plan: DictionaryTransformPlan,
    source: nat,
) -> Seq<u8> {
    Seq::new(40, |i: int| {
        if i < plan.prefix_len {
            PREFIX_SUFFIX_BYTES@[plan.prefix_at as int + 1 + i]
        } else if i < plan.prefix_len + plan.body_len {
            crate::brotli_dictionary::RFC_DICTIONARY@[
                source as int + plan.body_start as int + i - plan.prefix_len as int
            ]
        } else {
            0u8
        }
    })
}

spec fn transformed_dictionary_body_buffer(
    plan: DictionaryTransformPlan,
    source: nat,
) -> Seq<u8> {
    let initial = initial_dictionary_transform_buffer(plan, source);
    if plan.transform == 10 && plan.body_len > 0 {
        ferment_bytes_spec(initial, plan.prefix_len, plan.body_len, 0)
    } else if plan.transform == 11 {
        ferment_all_spec(initial, plan.prefix_len, plan.body_len, 0)
    } else {
        initial
    }
}

spec fn complete_dictionary_transform_buffer(
    plan: DictionaryTransformPlan,
    source: nat,
) -> Seq<u8> {
    let body = transformed_dictionary_body_buffer(plan, source);
    let suffix_start = plan.prefix_len + plan.body_len;
    Seq::new(40, |i: int| {
        if suffix_start <= i < suffix_start + plan.suffix_len {
            PREFIX_SUFFIX_BYTES@[
                plan.suffix_at as int + 1 + i - suffix_start as int
            ]
        } else {
            body[i]
        }
    })
}

pub(crate) closed spec fn transformed_word_matches(
    length: u8,
    word_index: u32,
    transform_index: u8,
    result: TransformedWord,
) -> bool {
    exists|plan: DictionaryTransformPlan| {
        let source = DICTIONARY_OFFSETS@[length as int] as nat
            + word_index as nat * length as nat;
        &&& #[trigger] dictionary_transform_plan_matches(length, transform_index, plan)
        &&& source + length as nat <= crate::brotli_dictionary::RFC_DICTIONARY_LEN
        &&& result.len as nat == plan.prefix_len + plan.body_len + plan.suffix_len
        &&& result.bytes@ == complete_dictionary_transform_buffer(plan, source)
    }
}

fn zero_length_dictionary_transform_plan() -> (r: DictionaryTransformPlan)
    ensures r == (DictionaryTransformPlan {
        prefix_at: 216,
        prefix_len: 0,
        body_start: 0,
        body_len: 0,
        suffix_at: 216,
        suffix_len: 0,
        transform: 4,
    }),
{
    DictionaryTransformPlan {
        prefix_at: 216,
        prefix_len: 0,
        body_start: 0,
        body_len: 0,
        suffix_at: 216,
        suffix_len: 0,
        transform: 4,
    }
}

fn dictionary_transform_plan(
    length: u8,
    transform_index: u8,
) -> (r: Result<DictionaryTransformPlan, DictionaryTransformError>)
    requires 4 <= length <= 24, (transform_index as usize) < TRANSFORM_COUNT,
    ensures r.is_ok() ==> {
        let plan = r.unwrap();
        &&& plan.prefix_at + 1 + plan.prefix_len <= PREFIX_SUFFIX_BYTES.len()
        &&& plan.suffix_at + 1 + plan.suffix_len <= PREFIX_SUFFIX_BYTES.len()
        &&& plan.body_start + plan.body_len <= length as usize
        &&& plan.prefix_len + plan.body_len + plan.suffix_len <= 37
        &&& plan.transform <= 20
        &&& dictionary_transform_plan_matches(length, transform_index, plan)
    },
{
    if length == 4 && transform_index == 42 {
        return Ok(zero_length_dictionary_transform_plan());
    }
    let (prefix_id, transform, suffix_id) = decoder_transform_record(transform_index);
    if prefix_id >= 50 || suffix_id >= 50 || transform > 20 {
        return Err(DictionaryTransformError::InvalidTransform);
    }
    let (prefix_at, prefix_len) = decoder_prefix_suffix(prefix_id);
    let (suffix_at, suffix_len) = decoder_prefix_suffix(suffix_id);
    if prefix_at >= PREFIX_SUFFIX_BYTES.len() || suffix_at >= PREFIX_SUFFIX_BYTES.len() {
        return Err(DictionaryTransformError::InvalidData);
    }
    proof {
        if length == 4 && transform_index == 42 {
            assert(prefix_at == 216);
            assert(suffix_at == 216);
            assert(prefix_len == 0);
            assert(suffix_len == 0);
        }
    }
    if prefix_at + 1 + prefix_len > PREFIX_SUFFIX_BYTES.len()
        || suffix_at + 1 + suffix_len > PREFIX_SUFFIX_BYTES.len()
    {
        return Err(DictionaryTransformError::InvalidData);
    }
    let mut body_start = 0usize;
    let mut body_len = length as usize;
    if transform <= 9 {
        body_len = body_len.saturating_sub(transform as usize);
    } else if transform >= 12 {
        let omit = transform as usize - 11;
        body_start = omit.min(body_len);
        body_len -= body_start;
    }
    if prefix_len + body_len + suffix_len > 37 {
        return Err(DictionaryTransformError::InvalidData);
    }
    let plan = DictionaryTransformPlan {
        prefix_at,
        prefix_len,
        body_start,
        body_len,
        suffix_at,
        suffix_len,
        transform,
    };
    Ok(plan)
}

pub(crate) fn transform_dictionary_word(
    length: u8,
    word_index: u32,
    transform_index: u8,
) -> (r: Result<TransformedWord, DictionaryTransformError>)
    ensures r.is_ok() ==> transformed_word_matches(
        length,
        word_index,
        transform_index,
        r.unwrap(),
    ),
{
    if let Err(error) = validate_dictionary_transform_shape(length, transform_index) {
        return Err(error);
    }
    let bits = dictionary_size_bits(length);
    if bits == 0 || word_index >= (1u32 << bits) {
        return Err(DictionaryTransformError::InvalidIndex);
    }
    let scaled_index = match word_index.checked_mul(length as u32) {
        Some(value) => value,
        None => return Err(DictionaryTransformError::InvalidData),
    };
    let source = match dictionary_offset(length).checked_add(scaled_index) {
        Some(value) => value as usize,
        None => return Err(DictionaryTransformError::InvalidData),
    };
    if source > crate::brotli_dictionary::RFC_DICTIONARY_LEN
        || length as usize > crate::brotli_dictionary::RFC_DICTIONARY_LEN - source
    {
        return Err(DictionaryTransformError::InvalidData);
    }
    let plan = match dictionary_transform_plan(length, transform_index) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let prefix_at = plan.prefix_at;
    let prefix_len = plan.prefix_len;
    let body_start = plan.body_start;
    let body_len = plan.body_len;
    let suffix_at = plan.suffix_at;
    let suffix_len = plan.suffix_len;
    let transform = plan.transform;
    proof {
        assert(scaled_index as nat == word_index as nat * length as nat);
        assert(source as nat == DICTIONARY_OFFSETS@[length as int] as nat
            + word_index as nat * length as nat);
        assert(dictionary_transform_plan_matches(length, transform_index, plan));
    }
    let mut output = [0u8; 40];
    let ghost zero_buffer = output@;
    copy_affix(&mut output, 0, prefix_at, prefix_len);
    let ghost after_prefix = output@;
    let mut produced = prefix_len;
    let body_output_start = produced;
    copy_dictionary_slice(
        &mut output,
        body_output_start,
        source,
        body_start,
        body_len,
    );
    proof {
        reveal(initial_dictionary_transform_buffer);
        assert(output@ == initial_dictionary_transform_buffer(plan, source as nat)) by {
            assert(output@.len() == 40);
            assert forall|i: int| 0 <= i < 40 implies
                output@[i] == initial_dictionary_transform_buffer(plan, source as nat)[i] by {
                if i < prefix_len {
                    assert(0 <= i < prefix_len);
                    assert(!(body_output_start <= i
                        < body_output_start + body_len));
                    assert(output@[i] == after_prefix[i]);
                    assert(after_prefix[0 + i]
                        == PREFIX_SUFFIX_BYTES@[prefix_at as int + 1 + i]);
                    assert(output@[i] == PREFIX_SUFFIX_BYTES@[prefix_at as int + 1 + i]);
                } else if i < prefix_len + body_len {
                    let body_index = i - prefix_len as int;
                    assert(0 <= body_index < body_len);
                    assert(i == body_output_start as int + body_index);
                    assert(output@[body_output_start as int + body_index]
                        == crate::brotli_dictionary::RFC_DICTIONARY@[
                            source as int + body_start as int + body_index
                        ]);
                    assert(output@[i] == crate::brotli_dictionary::RFC_DICTIONARY@[
                        source as int + body_start as int + body_index
                    ]);
                } else {
                    assert(!(body_output_start <= i
                        < body_output_start + body_len));
                    assert(output@[i] == after_prefix[i]);
                    assert(!(0 <= i < prefix_len));
                    assert(after_prefix[i] == zero_buffer[i]);
                    assert(zero_buffer[i] == 0);
                    assert(output@[i] == 0);
                }
            }
        }
    }
    produced += body_len;
    let ghost before_transform = output@;
    if transform == 10 && body_len > 0 {
        let _ = ferment(&mut output, body_output_start, body_len, 0);
    } else if transform == 11 {
        let ghost before_ferment = output@;
        let mut position = 0usize;
        while position < body_len
            invariant position <= body_len,
                body_output_start + body_len <= 40,
                ferment_all_spec(
                    output@,
                    body_output_start,
                    body_len,
                    position,
                ) == ferment_all_spec(
                    before_ferment,
                    body_output_start,
                    body_len,
                    0,
                ),
            decreases body_len - position,
        {
            let old_position = position;
            let ghost before_step = output@;
            let step = ferment(&mut output, body_output_start, body_len, position);
            let next_position = (position + step).min(body_len);
            proof {
                reveal(ferment_all_spec);
                assert(ferment_all_spec(
                    before_step,
                    body_output_start,
                    body_len,
                    old_position,
                ) == ferment_all_spec(
                    output@,
                    body_output_start,
                    body_len,
                    next_position,
                ));
            }
            position = next_position;
        }
        proof {
            reveal(ferment_all_spec);
            assert(output@ == ferment_all_spec(
                before_ferment,
                body_output_start,
                body_len,
                0,
            ));
        }
    }
    proof {
        reveal(transformed_dictionary_body_buffer);
        if transform == 10 && body_len > 0 {
            assert(output@ == ferment_bytes_spec(
                before_transform,
                body_output_start,
                body_len,
                0,
            ));
        } else if transform == 11 {
            assert(output@ == ferment_all_spec(
                before_transform,
                body_output_start,
                body_len,
                0,
            ));
        } else {
            assert(output@ == before_transform);
        }
        assert(before_transform == initial_dictionary_transform_buffer(plan, source as nat));
        assert(output@ == transformed_dictionary_body_buffer(plan, source as nat));
    }
    let ghost before_suffix = output@;
    let suffix_output_start = produced;
    copy_affix(&mut output, suffix_output_start, suffix_at, suffix_len);
    produced += suffix_len;
    let result = TransformedWord { bytes: output, len: produced as u8 };
    proof {
        reveal(complete_dictionary_transform_buffer);
        assert(output@ == complete_dictionary_transform_buffer(plan, source as nat)) by {
            assert(output@.len() == 40);
            assert forall|i: int| 0 <= i < 40 implies
                output@[i] == complete_dictionary_transform_buffer(plan, source as nat)[i] by {
                if suffix_output_start <= i < suffix_output_start + suffix_len {
                    let suffix_index = i - suffix_output_start as int;
                    assert(0 <= suffix_index < suffix_len);
                    assert(i == suffix_output_start as int + suffix_index);
                    assert(output@[suffix_output_start as int + suffix_index]
                        == PREFIX_SUFFIX_BYTES@[
                            suffix_at as int + 1 + suffix_index
                        ]);
                    assert(output@[i] == PREFIX_SUFFIX_BYTES@[
                        suffix_at as int + 1 + suffix_index
                    ]);
                } else {
                    assert(output@[i] == before_suffix[i]);
                }
            }
        }
        reveal(transformed_word_matches);
        assert(result.len as nat == plan.prefix_len + plan.body_len + plan.suffix_len);
        assert(exists|candidate: DictionaryTransformPlan|
            #[trigger] dictionary_transform_plan_matches(
                length,
                transform_index,
                candidate,
            ) && candidate == plan && {
                let expected_source = DICTIONARY_OFFSETS@[length as int] as nat
                    + word_index as nat * length as nat;
                &&& expected_source + length as nat
                    <= crate::brotli_dictionary::RFC_DICTIONARY_LEN
                &&& result.len as nat
                    == candidate.prefix_len + candidate.body_len + candidate.suffix_len
                &&& result.bytes@
                    == complete_dictionary_transform_buffer(candidate, expected_source)
            });
    }
    Ok(result)
}

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn committed_tables_match_pinned_reference_bytes() {
        let command = include_bytes!("../tests/fixtures/brotli/reference/command.bin");
        assert_eq!(command.len(), COMMAND_SYMBOLS * 8);
        for (index, entry) in COMMAND_TABLE.iter().enumerate() {
            assert_eq!(command_entry_formula(index as u16), *entry);
            let at = index * 8;
            assert_eq!(command[at], entry.insert_extra_bits);
            assert_eq!(command[at + 1], entry.copy_extra_bits);
            assert_eq!(command[at + 2], entry.distance_mode as u8);
            assert_eq!(command[at + 3], entry.distance_context);
            assert_eq!(&command[at + 4..at + 6], &entry.insert_offset.to_le_bytes());
            assert_eq!(&command[at + 6..at + 8], &entry.copy_offset.to_le_bytes());
        }

        let context = include_bytes!("../tests/fixtures/brotli/reference/context.bin");
        assert_eq!(LITERAL_CONTEXT_TABLE.as_slice(), context);

        let dictionary_meta =
            include_bytes!("../tests/fixtures/brotli/reference/dictionary-meta.bin");
        assert_eq!(&dictionary_meta[..32], DICTIONARY_SIZE_BITS.as_slice());
        for (index, value) in DICTIONARY_OFFSETS.iter().enumerate() {
            let at = 32 + 4 * index;
            assert_eq!(&dictionary_meta[at..at + 4], &value.to_le_bytes());
        }

        let transforms = include_bytes!("../tests/fixtures/brotli/reference/transforms.bin");
        assert_eq!(&transforms[..217], PREFIX_SUFFIX_BYTES.as_slice());
        for (index, value) in PREFIX_SUFFIX_MAP.iter().enumerate() {
            let at = 217 + 2 * index;
            assert_eq!(&transforms[at..at + 2], &value.to_le_bytes());
        }
        assert_eq!(&transforms[317..], TRANSFORM_RECORDS.as_slice());
    }

    #[test]
    fn arithmetic_transform_toggles_match_byte_xor() {
        for value in 0u16..=255 {
            let byte = value as u8;
            assert_eq!(toggle_32(byte), byte ^ 32);
            assert_eq!(toggle_5(byte), byte ^ 5);
        }
    }
}
