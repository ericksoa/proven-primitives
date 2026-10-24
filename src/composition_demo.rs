//! Checked Base64-to-percent composition demonstration.
//!
//! This module is crate-private. It verifies one exact caller and does not
//! claim that arbitrary applications compose the public primitives correctly.

#![allow(dead_code)]

#[cfg(verus_keep_ghost)]
use crate::written;
use crate::{base64, percent, Error};
use vstd::prelude::*;

verus! {

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComposeError {
    Base64Invalid,
    ScratchTooSmall,
    PercentInvalid,
    OutputTooSmall,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DecodeCaller {
    published_len: Option<usize>,
}

pub open spec fn composed(input: Seq<u8>) -> Option<Seq<u8>> {
    match base64::decoded(input) {
        None => None,
        Some(middle) => percent::decoded(middle),
    }
}

spec fn expected_result(input: Seq<u8>, scratch_len: nat, output_len: nat)
    -> Result<usize, ComposeError>
{
    match base64::decoded(input) {
        None => Err(ComposeError::Base64Invalid),
        Some(middle) => if middle.len() > scratch_len {
            Err(ComposeError::ScratchTooSmall)
        } else {
            match percent::decoded(middle) {
                None => Err(ComposeError::PercentInvalid),
                Some(bytes) => if bytes.len() > output_len {
                    Err(ComposeError::OutputTooSmall)
                } else {
                    Ok(bytes.len() as usize)
                },
            }
        },
    }
}

impl DecodeCaller {
    fn new() -> (r: Self)
        ensures r.published_len == None,
    {
        Self { published_len: None }
    }

    fn decode(
        &mut self,
        input: &[u8],
        scratch: &mut [u8],
        output: &mut [u8],
    ) -> (r: Result<usize, ComposeError>)
        ensures r == expected_result(
                input@, old(scratch)@.len(), old(output)@.len()),
            final(self).published_len == match r {
                Ok(n) => Some(n),
                Err(_) => None,
            },
            match base64::decoded(input@) {
                None => final(scratch)@ == old(scratch)@
                    && final(output)@ == old(output)@,
                Some(middle) => if middle.len() > old(scratch)@.len() {
                    final(scratch)@ == old(scratch)@
                        && final(output)@ == old(output)@
                } else {
                    &&& written(old(scratch)@, final(scratch)@, middle)
                    &&& match percent::decoded(middle) {
                        None => final(output)@ == old(output)@,
                        Some(bytes) => if bytes.len() > old(output)@.len() {
                            final(output)@ == old(output)@
                        } else {
                            written(old(output)@, final(output)@, bytes)
                        },
                    }
                },
            },
    {
        self.published_len = None;
        let ghost mut adapter_transitions: nat = 1;
        let ghost scratch_capacity = scratch.len();
        let ghost scratch_before = scratch@;
        assert(scratch_before.len() == scratch_capacity);
        proof { adapter_transitions = adapter_transitions + 1; }
        let middle_n = match base64::decode_into(input, scratch) {
            Ok(n) => {
                proof { adapter_transitions = adapter_transitions + 1; }
                n
            }
            Err(Error::InvalidInput) => {
                proof { assert(adapter_transitions <= 8); }
                return Err(ComposeError::Base64Invalid);
            }
            Err(Error::OutputTooSmall) => {
                proof { assert(adapter_transitions <= 8); }
                return Err(ComposeError::ScratchTooSmall);
            }
        };
        proof {
            assert(base64::decoded(input@).is_some());
            let middle = base64::decoded(input@).unwrap();
            assert(middle_n == middle.len() as usize);
            assert(written(scratch_before, scratch@, middle));
            reveal(written);
            assert(middle.len() <= scratch_before.len());
            assert(middle.len() <= scratch_capacity);
            assert(middle_n as int == middle.len());
            assert(scratch@.take(middle.len() as int) =~= middle);
            assert(scratch@.take(middle_n as int) == middle);
            adapter_transitions = adapter_transitions + 1;
        }
        let middle = &scratch[..middle_n];
        proof { adapter_transitions = adapter_transitions + 1; }
        let n = match percent::decode_into(middle, output) {
            Ok(n) => {
                proof { adapter_transitions = adapter_transitions + 1; }
                n
            }
            Err(Error::InvalidInput) => {
                proof { assert(adapter_transitions <= 8); }
                return Err(ComposeError::PercentInvalid);
            }
            Err(Error::OutputTooSmall) => {
                proof { assert(adapter_transitions <= 8); }
                return Err(ComposeError::OutputTooSmall);
            }
        };
        self.published_len = Some(n);
        proof {
            adapter_transitions = adapter_transitions + 1;
            let decoded_middle = base64::decoded(input@).unwrap();
            let decoded_output = percent::decoded(decoded_middle).unwrap();
            successful_work_bound(input@, decoded_middle, decoded_output);
            adapter_transitions = adapter_transitions + 1;
            assert(adapter_transitions == 8);
        }
        Ok(n)
    }
}

proof fn handoff_is_current_prefix(
    before: Seq<u8>, after: Seq<u8>, middle: Seq<u8>,
)
    requires written(before, after, middle),
    ensures after.take(middle.len() as int) == middle,
{}

proof fn composed_prefix_is_independent_of_previous_storage(
    input: Seq<u8>,
    before_a: Seq<u8>, after_a: Seq<u8>,
    before_b: Seq<u8>, after_b: Seq<u8>,
)
    requires composed(input).is_some(),
        written(before_a, after_a, composed(input).unwrap()),
        written(before_b, after_b, composed(input).unwrap()),
    ensures after_a.take(composed(input).unwrap().len() as int)
        == after_b.take(composed(input).unwrap().len() as int),
{}

pub open spec fn successful_work(input: Seq<u8>, middle: Seq<u8>, output: Seq<u8>) -> nat {
    8 * input.len() + 12 * middle.len() + 4 * output.len() + 56
}

proof fn successful_work_bound(input: Seq<u8>, middle: Seq<u8>, output: Seq<u8>)
    requires base64::decoded(input) == Some(middle),
        percent::decoded(middle) == Some(output),
    ensures successful_work(input, middle, output) <= 21 * input.len() + 56,
{
    base64::decoded_length_bound(input);
    percent::decoded_length_bound(middle);
    assert(input.len() % 4 == 0);
    assert(middle.len() <= 3 * (input.len() / 4));
    assert(output.len() <= middle.len());
    assert(4 * (input.len() / 4) == input.len());
}

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_prefix_handoff_and_state_transitions() {
        let mut caller = DecodeCaller::new();
        let mut scratch = [0xa5; 32];
        let mut output = [0x5a; 32];

        // Base64("a%20b") followed by strict percent decoding.
        assert_eq!(caller.decode(b"YSUyMGI=", &mut scratch, &mut output), Ok(3));
        assert_eq!(caller.published_len, Some(3));
        assert_eq!(&output[..3], b"a b");
        assert!(output[3..].iter().all(|b| *b == 0x5a));
        assert_eq!(&scratch[..5], b"a%20b");
        assert!(scratch[5..].iter().all(|b| *b == 0xa5));

        let scratch_before = scratch;
        let output_before = output;
        assert_eq!(
            caller.decode(b"!!!!", &mut scratch, &mut output),
            Err(ComposeError::Base64Invalid),
        );
        assert_eq!(caller.published_len, None);
        assert_eq!(scratch, scratch_before);
        assert_eq!(output, output_before);

        assert_eq!(caller.decode(b"eCUyNQ==", &mut scratch, &mut output), Ok(2));
        assert_eq!(caller.published_len, Some(2));
        assert_eq!(&output[..2], b"x%");
    }

    #[test]
    fn stage_errors_preserve_exact_effects() {
        let mut caller = DecodeCaller::new();
        let mut short_scratch = [0x11; 4];
        let mut output = [0x22; 8];
        let output_before = output;
        assert_eq!(
            caller.decode(b"YSUyMGI=", &mut short_scratch, &mut output),
            Err(ComposeError::ScratchTooSmall),
        );
        assert_eq!(short_scratch, [0x11; 4]);
        assert_eq!(output, output_before);

        let mut scratch = [0x33; 16];
        assert_eq!(
            caller.decode(b"eCU=", &mut scratch, &mut output),
            Err(ComposeError::PercentInvalid),
        );
        assert_eq!(&scratch[..2], b"x%");
        assert!(scratch[2..].iter().all(|b| *b == 0x33));
        assert_eq!(output, output_before);
        assert_eq!(caller.published_len, None);

        let mut tiny = [0x44; 2];
        let tiny_before = tiny;
        assert_eq!(
            caller.decode(b"YSUyMGI=", &mut scratch, &mut tiny),
            Err(ComposeError::OutputTooSmall),
        );
        assert_eq!(&scratch[..5], b"a%20b");
        assert_eq!(tiny, tiny_before);
        assert_eq!(caller.published_len, None);
    }

    #[test]
    fn empty_and_binary_compositions() {
        let mut caller = DecodeCaller::new();
        let mut scratch = [0xcc; 16];
        let mut output = [0xdd; 16];
        assert_eq!(caller.decode(b"", &mut scratch, &mut output), Ok(0));
        assert_eq!(caller.published_len, Some(0));
        assert_eq!(scratch, [0xcc; 16]);
        assert_eq!(output, [0xdd; 16]);

        // Base64([0xff, '%', '0', '0']) -> [0xff, 0].
        assert_eq!(caller.decode(b"/yUwMA==", &mut scratch, &mut output), Ok(2));
        assert_eq!(&output[..2], &[0xff, 0]);
    }
}
