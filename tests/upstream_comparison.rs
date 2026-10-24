//! Applicable upstream assertions and deterministic differential comparisons.
//! Adapted fixture assertions: rust-base64 0.23.1 tests/{encode,tests}.rs and
//! lz4_flex 0.14.0 src/block/decompress_safe.rs. See THIRD_PARTY_NOTICES.md.
use base64_ref::{engine::general_purpose::STANDARD, Engine};
use proven_primitives::{base64, lz4, Error};
use std::fs;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    Ok(usize),
    Invalid,
    TooSmall,
}

fn ours(result: Result<usize, Error>) -> Outcome {
    match result {
        Ok(n) => Outcome::Ok(n),
        Err(Error::InvalidInput) => Outcome::Invalid,
        Err(Error::OutputTooSmall) => Outcome::TooSmall,
    }
}

fn upstream_encode(input: &[u8], output: &mut [u8]) -> Outcome {
    STANDARD
        .encode_slice(input, output)
        .map_or(Outcome::TooSmall, Outcome::Ok)
}

fn upstream_decode(input: &[u8], output: &mut [u8]) -> Outcome {
    match STANDARD.decode_slice(input, output) {
        Ok(n) => Outcome::Ok(n),
        Err(base64_ref::DecodeSliceError::OutputSliceTooSmall) => Outcome::TooSmall,
        Err(base64_ref::DecodeSliceError::DecodeError(_)) => Outcome::Invalid,
    }
}

fn upstream_lz4(input: &[u8], output: &mut [u8]) -> Outcome {
    match lz4_ref::block::decompress_into(input, output) {
        Ok(n) => Outcome::Ok(n),
        Err(lz4_ref::block::DecompressError::OutputTooSmall { .. }) => Outcome::TooSmall,
        Err(_) => Outcome::Invalid,
    }
}

#[derive(Default)]
struct Counts {
    cases: usize,
    both_ok: usize,
    both_error: usize,
    strict_rejections: usize,
    error_priority_differences: usize,
    upstream_changed_buffer_on_error: usize,
    upstream_changed_success_suffix: usize,
    differences: Vec<String>,
}

impl Counts {
    fn compare(
        &mut self,
        name: &str,
        input: &[u8],
        capacity: usize,
        implementation: fn(&[u8], &mut [u8]) -> Result<usize, Error>,
        reference: fn(&[u8], &mut [u8]) -> Outcome,
        permits_upstream_only_acceptance: bool,
    ) -> (Outcome, Outcome) {
        self.cases += 1;
        let mut a = vec![0xa5; capacity];
        let mut b = a.clone();
        let ar = ours(implementation(input, &mut a));
        let br = reference(input, &mut b);
        match ar {
            Outcome::Ok(n) => assert!(a[n..].iter().all(|v| *v == 0xa5)),
            _ => assert!(a.iter().all(|v| *v == 0xa5)),
        }
        match (ar, br) {
            (Outcome::Ok(n), Outcome::Ok(m)) => {
                assert_eq!(n, m, "{name}: returned lengths");
                assert_eq!(a[..n], b[..m], "{name}: returned bytes");
                self.both_ok += 1;
                self.upstream_changed_success_suffix +=
                    usize::from(b[m..].iter().any(|v| *v != 0xa5));
            }
            (Outcome::Invalid, Outcome::Ok(_)) if permits_upstream_only_acceptance => {
                self.strict_rejections += 1;
            }
            (Outcome::Ok(_), _) | (_, Outcome::Ok(_)) => {
                panic!(
                    "unexpected acceptance difference for {name}: ours={ar:?}, reference={br:?}"
                );
            }
            _ => {
                self.both_error += 1;
                if ar != br {
                    assert_eq!((ar, br), (Outcome::Invalid, Outcome::TooSmall), "{name}");
                    self.error_priority_differences += 1;
                }
                self.upstream_changed_buffer_on_error += usize::from(b.iter().any(|v| *v != 0xa5));
            }
        }
        if ar != br && self.differences.len() < 16 {
            // Names below are fixed ASCII identifiers, not arbitrary JSON text.
            let input_hex: String = input.iter().map(|b| format!("{b:02x}")).collect();
            self.differences.push(format!(
                "{{\"case\":\"{name}\",\"input_hex\":\"{input_hex}\",\"capacity\":{capacity},\"ours\":\"{ar:?}\",\"upstream\":\"{br:?}\"}}"
            ));
        }
        (ar, br)
    }

    fn json(&self) -> String {
        format!(
            "{{\"cases\":{},\"both_ok\":{},\"both_error\":{},\"strict_rejections\":{},\"error_priority_differences\":{},\"upstream_changed_buffer_on_error\":{},\"upstream_changed_success_suffix\":{},\"unexpected_differences\":0,\"difference_examples\":[{}]}}",
            self.cases, self.both_ok, self.both_error, self.strict_rejections,
            self.error_priority_differences, self.upstream_changed_buffer_on_error,
            self.upstream_changed_success_suffix, self.differences.join(",")
        )
    }
}

fn data(size: usize, pattern: usize) -> Vec<u8> {
    let mut state = 0x5eeda1b2c3d4u64;
    (0..size)
        .map(|i| match pattern {
            0 => 0,
            1 => b"common-library-pattern"[i % 22],
            _ => {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                state as u8
            }
        })
        .collect()
}

#[test]
fn upstream_compatibility_and_historical_security_replay() {
    let mut encode = Counts::default();
    let mut decode = Counts::default();
    let mut block = Counts::default();

    // Preserve the upstream exact-capacity progression assertion for all
    // triples in tests/tests.rs::encode_engine_slice_error_when_buffer_too_small.
    for triples in 1..100 {
        let input = b"AAA".repeat(triples);
        for capacity in (triples - 1) * 4..=triples * 4 {
            let actual = encode.compare(
                "upstream_encode_capacity",
                &input,
                capacity,
                base64::encode_into,
                upstream_encode,
                false,
            );
            let expected = if capacity < triples * 4 {
                Outcome::TooSmall
            } else {
                Outcome::Ok(triples * 4)
            };
            assert_eq!(actual, (expected, expected));
        }
    }
    // Expected bytes from tests/encode.rs::encode_all_bytes.
    let all_bytes: Vec<u8> = (0..=255).collect();
    let expected = concat!(
        "AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4OTo7P",
        "D0+P0BBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWltcXV5fYGFiY2RlZmdoaWprbG1ub3BxcnN0dXZ3eHl6e3x9fn",
        "+AgYKDhIWGh4iJiouMjY6PkJGSk5SVlpeYmZqbnJ2en6ChoqOkpaanqKmqq6ytrq+wsbKztLW2t7i5uru8vb6",
        "/wMHCw8TFxsfIycrLzM3Oz9DR0tPU1dbX2Nna29zd3t/g4eLj5OXm5+jp6uvs7e7v8PHy8/T19vf4+fr7/P3+/w=="
    );
    assert_eq!(STANDARD.encode(&all_bytes), expected);
    let mut actual = vec![0; expected.len()];
    assert_eq!(
        base64::encode_into(&all_bytes, &mut actual),
        Ok(expected.len())
    );
    assert_eq!(actual, expected.as_bytes());

    let sizes = (0..=512).chain([1023, 1024, 4095, 4096, 65535, 262144]);
    for size in sizes {
        for pattern in 0..3 {
            let input = data(size, pattern);
            let text = STANDARD.encode(&input);
            let compressed = lz4_ref::block::compress(&input);
            // Existing generated sizes cover every batch/remainder boundary
            // through 64. Add a late invalid byte to test validation before writes.
            if (1..=64).contains(&size) {
                let mut malformed = text.as_bytes().to_vec();
                *malformed.last_mut().unwrap() = b'!';
                for capacity in [0, size, size + 17] {
                    decode.compare(
                        "batch_malformed_suffix",
                        &malformed,
                        capacity,
                        base64::decode_into,
                        upstream_decode,
                        false,
                    );
                }
            }
            for capacity in [0, text.len().saturating_sub(1), text.len(), text.len() + 17] {
                encode.compare(
                    "generated",
                    &input,
                    capacity,
                    base64::encode_into,
                    upstream_encode,
                    false,
                );
            }
            for capacity in [0, size.saturating_sub(1), size, size + 17] {
                decode.compare(
                    "generated",
                    text.as_bytes(),
                    capacity,
                    base64::decode_into,
                    upstream_decode,
                    false,
                );
                block.compare(
                    "upstream_compressed",
                    &compressed,
                    capacity,
                    lz4::decompress_block_into,
                    upstream_lz4,
                    false,
                );
            }
        }
    }
    // Exhaust every 0-, 1-, and 2-byte input at a sufficient output capacity.
    for length in 0..=2 {
        for value in 0..1usize << (8 * length) {
            let input = (value as u16).to_le_bytes();
            decode.compare(
                "exhaustive_short",
                &input[..length],
                256,
                base64::decode_into,
                upstream_decode,
                false,
            );
            block.compare(
                "exhaustive_short",
                &input[..length],
                256,
                lz4::decompress_block_into,
                upstream_lz4,
                false,
            );
        }
    }
    // Strict padding, trailing-bit, alphabet, and late-error examples.
    for input in [
        b"Zh==".as_slice(),
        b"Zm9=",
        b"QUJDZh==",
        b"Zg=",
        b"=g==",
        b"Zg==AAAA",
        b"Zg==\n",
        b"AAAA====",
        b"-___",
        b"\xffAAA",
    ] {
        for capacity in [0, 1, 2, 3, 8, 256] {
            decode.compare(
                "malformed_base64",
                input,
                capacity,
                base64::decode_into,
                upstream_decode,
                false,
            );
        }
    }
    // Exercise every possible classifier byte in every four-character position.
    // Compare the complete compiled APIs, including separate padding handling.
    for position in 0..4 {
        for byte in 0u8..=255 {
            let mut input = *b"AAAA";
            input[position] = byte;
            decode.compare(
                "exhaustive_quad_position",
                &input,
                3,
                base64::decode_into,
                upstream_decode,
                false,
            );
        }
    }
    // A complete first batch followed by a malformed later group must
    // outrank a known-small destination and preserve its entire contents.
    for input in [b"AAAAAAAAAAAAAA!A".as_slice(), b"AAAAAAAAAAAAZh=="] {
        for capacity in [0, 1, 5, 6, 9, 12, 16] {
            decode.compare(
                "validation_small_before_invalid",
                input,
                capacity,
                base64::decode_into,
                upstream_decode,
                false,
            );
        }
    }
    // Every classifier byte in both groups of the new batch path; the
    // final group remains available for the original padding-aware path.
    for position in 0..8 {
        for byte in 0u8..=255 {
            let mut input = *b"AAAAAAAAAAAA";
            input[position] = byte;
            decode.compare(
                "exhaustive_batch_position",
                &input,
                9,
                base64::decode_into,
                upstream_decode,
                false,
            );
        }
    }
    // Applicable upstream decompress_safe.rs assertions, preserving rejection.
    for (index, input) in [
        b"".as_slice(),
        &[0xf0],
        &[0x0f, 0],
        &[0x0f, 1, 0],
        &[0x40, b'a', 1, 0],
        &[
            0x0e, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ],
        &[0x0f, 1, 0, 1, 0x70, 0, 0, 0, 0, 0, 0, 0],
    ]
    .into_iter()
    .enumerate()
    {
        let mut destination = [0xa5; 256];
        let result = lz4_ref::block::decompress_into(input, &mut destination);
        match index {
            0..=3 => assert!(matches!(
                result,
                Err(lz4_ref::block::DecompressError::ExpectedAnotherByte)
            )),
            4 => assert!(matches!(
                result,
                Err(lz4_ref::block::DecompressError::LiteralOutOfBounds)
            )),
            _ => assert!(matches!(
                result,
                Err(lz4_ref::block::DecompressError::OffsetOutOfBounds)
            )),
        }
        block.compare(
            "upstream_invalid_block",
            input,
            256,
            lz4::decompress_block_into,
            upstream_lz4,
            false,
        );
    }
    block.compare(
        "upstream_all_literal",
        &[0x30, b'a', b'4', b'9'],
        3,
        lz4::decompress_block_into,
        upstream_lz4,
        false,
    );
    let mut all_literal = [0; 3];
    assert_eq!(
        lz4::decompress_block_into(&[0x30, b'a', b'4', b'9'], &mut all_literal),
        Ok(3)
    );
    assert_eq!(&all_literal, b"a49");
    // Probe end rules and record which inputs current upstream accepts.
    for (name, input) in [
        ("no_final_literal_sequence", &[0x10, b'a', 1, 0][..]),
        (
            "fewer_than_five_final_literals",
            &[0x10, b'a', 1, 0, 0x40, b'a', b'a', b'a', b'a'][..],
        ),
        (
            "last_match_too_close_to_end",
            &[0x10, b'a', 1, 0, 0x50, b'a', b'a', b'a', b'a', b'a'][..],
        ),
    ] {
        block.compare(
            name,
            input,
            256,
            lz4::decompress_block_into,
            upstream_lz4,
            true,
        );
    }
    // Actual historical safe-decoder replay, with fully initialized buffers.
    let malicious = [0x0e, 0, 0, 0x70, 0, 0, 0, 0, 0, 0, 0];
    let mut old_zero = [0u8; 256];
    let mut old_secret = [0xa5u8; 256];
    let n = lz4_vulnerable::block::decompress_into(&malicious, &mut old_zero).unwrap();
    let m = lz4_vulnerable::block::decompress_into(&malicious, &mut old_secret).unwrap();
    assert_eq!((n, m), (25, 25));
    assert_ne!(old_zero[..n], old_secret[..m]);
    assert_eq!(old_secret[..18], [0xa5; 18]);
    let mut current = [0xa5u8; 256];
    assert!(matches!(
        lz4_ref::block::decompress_into(&malicious, &mut current),
        Err(lz4_ref::block::DecompressError::OffsetZero)
    ));
    let mut protected = [0xa5u8; 256];
    assert_eq!(
        lz4::decompress_block_into(&malicious, &mut protected),
        Err(Error::InvalidInput)
    );
    assert_eq!(protected, [0xa5; 256]);

    let report = format!(
        "{{\n\"claim\":\"tested compatibility, not universal upstream equivalence\",\n\"base64_encode\":{},\n\"base64_decode\":{},\n\"lz4_decode\":{},\n\"historical_lz4\":{{\"version\":\"0.12.0\",\"commit\":\"975bfa7ac9583da879b5d7578b423232d84f69fe\",\"safe_decode\":true,\"returned_bytes\":25,\"stale_bytes_disclosed\":18,\"current_reference_rejects\":true,\"proven_primitive_rejects_and_preserves_buffer\":true}}\n}}\n",
        encode.json(), decode.json(), block.json()
    );
    fs::create_dir_all("evidence").unwrap();
    fs::write("evidence/validation-upstream-comparison.json", &report).unwrap();
    println!("{report}");
}
