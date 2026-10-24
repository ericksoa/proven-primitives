use proven_primitives::{base64, lz4, percent, Error};

type Codec = fn(&[u8], &mut [u8]) -> Result<usize, Error>;

fn succeeds(codec: Codec, input: &[u8], expected: &[u8]) {
    let mut out = vec![0xa5; expected.len() + 7];
    assert_eq!(codec(input, &mut out), Ok(expected.len()));
    assert_eq!(&out[..expected.len()], expected);
    assert!(out[expected.len()..].iter().all(|b| *b == 0xa5));
    let mut exact = vec![0x5a; expected.len()];
    assert_eq!(codec(input, &mut exact), Ok(expected.len()));
    assert_eq!(exact, expected);
    if !expected.is_empty() {
        let mut short = vec![0xc3; expected.len() - 1];
        let before = short.clone();
        assert_eq!(codec(input, &mut short), Err(Error::OutputTooSmall));
        assert_eq!(short, before);
    }
}

fn invalid(codec: Codec, input: &[u8]) {
    for capacity in [0, 1, 8, 1024] {
        let mut out = vec![0xa5; capacity];
        let before = out.clone();
        assert_eq!(
            codec(input, &mut out),
            Err(Error::InvalidInput),
            "input {input:?}"
        );
        assert_eq!(out, before);
    }
}

fn generated(n: usize) -> Vec<u8> {
    let mut state = 0x5eeda1b2c3d4u64;
    (0..n)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state as u8
        })
        .collect()
}

// An independent streaming-bit oracle, rather than the library's 24-bit groups.
fn reference_base64(bytes: &[u8]) -> Vec<u8> {
    let alphabet = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = Vec::new();
    let mut bits = 0u32;
    let mut held = 0u32;
    for byte in bytes {
        held = (held << 8) | *byte as u32;
        bits += 8;
        while bits >= 6 {
            bits -= 6;
            out.push(alphabet[((held >> bits) & 63) as usize]);
        }
    }
    if bits != 0 {
        out.push(alphabet[((held << (6 - bits)) & 63) as usize]);
    }
    while out.len() % 4 != 0 {
        out.push(b'=');
    }
    out
}

fn reference_percent(bytes: &[u8]) -> Vec<u8> {
    let mut out = String::new();
    for b in bytes {
        if b.is_ascii_alphanumeric() || b"-._~".contains(b) {
            out.push(*b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out.into_bytes()
}

#[test]
fn base64_standard_vectors_and_canonical_rules() {
    for (plain, encoded) in [
        (b"".as_slice(), b"".as_slice()),
        (b"f", b"Zg=="),
        (b"fo", b"Zm8="),
        (b"foo", b"Zm9v"),
        (b"foob", b"Zm9vYg=="),
        (b"fooba", b"Zm9vYmE="),
        (b"foobar", b"Zm9vYmFy"),
        (&[0xff, 0xff, 0xff], b"////"),
        (&[0xfb, 0xef, 0xbe], b"++++"),
    ] {
        succeeds(base64::encode_into, plain, encoded);
        succeeds(base64::decode_into, encoded, plain);
    }
    for text in [
        b"Zg=".as_slice(),
        b"Zg===",
        b"=g==",
        b"Z=g=",
        b"Zg==AAAA",
        b"Zh==",
        b"Zm9=",
        b" Zg==",
        b"Zg==\n",
        b"-___",
        b"\xffAAA",
        b"AAAA====",
    ] {
        invalid(base64::decode_into, text);
    }
}

#[test]
fn base64_all_bytes_and_generated_inputs() {
    for byte in 0u8..=255 {
        let data = [byte];
        let encoded = reference_base64(&data);
        succeeds(base64::encode_into, &data, &encoded);
        succeeds(base64::decode_into, &encoded, &data);
    }
    for size in 0..512 {
        let data = generated(size);
        let encoded = reference_base64(&data);
        succeeds(base64::encode_into, &data, &encoded);
        succeeds(base64::decode_into, &encoded, &data);
    }
}

#[test]
fn percent_vectors_binary_bytes_and_strict_errors() {
    succeeds(percent::encode_into, b"a b+c/?%", b"a%20b%2Bc%2F%3F%25");
    succeeds(percent::decode_into, b"a%20b%2bc%2f%3f%25", b"a b+c/?%");
    succeeds(percent::decode_into, b"a+b", b"a+b");
    succeeds(percent::decode_into, &[0xff, b'%', b'0', b'0'], &[0xff, 0]);
    for data in [
        b"%".as_slice(),
        b"%0",
        b"%GG",
        b"%0g",
        b"ok%20then%",
        b"%ff%2",
    ] {
        invalid(percent::decode_into, data);
    }
    for byte in 0u8..=255 {
        let data = [byte];
        let encoded = reference_percent(&data);
        succeeds(percent::encode_into, &data, &encoded);
        succeeds(percent::decode_into, &encoded, &data);
    }
    for n in 0..256 {
        let data = generated(n);
        let encoded = reference_percent(&data);
        succeeds(percent::encode_into, &data, &encoded);
        succeeds(percent::decode_into, &encoded, &data);
    }
}

fn length_extension(out: &mut Vec<u8>, length: usize) {
    let mut extra = length - 15;
    while extra >= 255 {
        out.push(255);
        extra -= 255;
    }
    out.push(extra as u8);
}

fn literal_block(plain: &[u8]) -> Vec<u8> {
    let mut block = vec![(plain.len().min(15) as u8) << 4];
    if plain.len() >= 15 {
        length_extension(&mut block, plain.len());
    }
    block.extend_from_slice(plain);
    block
}

// Construct a valid independent block with a known repeating-window result.
fn match_block(seed: &[u8], offset: usize, count: usize) -> (Vec<u8>, Vec<u8>) {
    assert!(offset != 0 && offset <= seed.len() && count >= 4);
    let mut block = vec![((seed.len().min(15) as u8) << 4) | ((count - 4).min(15) as u8)];
    if seed.len() >= 15 {
        length_extension(&mut block, seed.len());
    }
    block.extend_from_slice(seed);
    block.extend_from_slice(&(offset as u16).to_le_bytes());
    if count >= 19 {
        length_extension(&mut block, count - 4);
    }
    let final_literals = b"final-literals";
    block.extend_from_slice(&literal_block(final_literals));
    let mut expected = seed.to_vec();
    let repeated = &seed[seed.len() - offset..];
    expected.extend((0..count).map(|i| repeated[i % repeated.len()]));
    expected.extend_from_slice(final_literals);
    (block, expected)
}

#[test]
fn lz4_literals_overlap_and_length_extensions() {
    succeeds(lz4::decompress_block_into, &[0], b"");
    succeeds(
        lz4::decompress_block_into,
        &[0x50, b'h', b'e', b'l', b'l', b'o'],
        b"hello",
    );
    // A minimal independent block: one literal, seven overlapping copies, five final literals.
    succeeds(
        lz4::decompress_block_into,
        &[0x13, b'a', 1, 0, 0x50, b'a', b'a', b'a', b'a', b'a'],
        b"aaaaaaaaaaaaa",
    );
    for n in [0, 1, 4, 5, 14, 15, 16, 269, 270, 271, 4096] {
        let plain = generated(n);
        succeeds(lz4::decompress_block_into, &literal_block(&plain), &plain);
    }
    for n in [4, 7, 18, 19, 20, 273, 274, 275, 4096] {
        for offset in 1..=16 {
            let (block, expected) = match_block(b"abcdefghijklmnop", offset, n);
            succeeds(lz4::decompress_block_into, &block, &expected);
        }
    }
}

#[test]
fn lz4_malformed_inputs_preserve_output_even_when_too_small() {
    for block in [
        b"".as_slice(),
        &[0xf0],
        &[0xf0, 255],
        &[0x10],
        &[0x10, b'a', 0, 0],
        &[0x10, b'a', 2, 0],
        &[0x10, b'a', 1],
        &[0x1f, b'a', 1, 0, 255],
        &[0x10, b'a', 1, 0], // A block must finish with a literal-only sequence.
        &[0x10, b'a', 1, 0, 0x40, b'a', b'a', b'a', b'a'], // Fewer than five final literals.
        &[0x10, b'a', 1, 0, 0x50, b'a', b'a', b'a', b'a', b'a'], // Last match is too close to decoded end.
    ] {
        invalid(lz4::decompress_block_into, block);
    }
    let (valid, _) = match_block(b"abcdefghijklmnop", 1, 4096);
    let mut malformed = valid;
    malformed.push(0); // Destroys the final literal-only sequence.
    invalid(lz4::decompress_block_into, &malformed);
}

#[test]
fn large_inputs_use_bounded_stack_and_preserve_tail() {
    let bytes = generated(262_144);
    let encoded = reference_base64(&bytes);
    succeeds(base64::encode_into, &bytes, &encoded);
    succeeds(base64::decode_into, &encoded, &bytes);
    let escaped = reference_percent(&bytes);
    succeeds(percent::encode_into, &bytes, &escaped);
    succeeds(percent::decode_into, &escaped, &bytes);
    succeeds(lz4::decompress_block_into, &literal_block(&bytes), &bytes);
    let (block, expected) = match_block(b"seed", 1, 262_144);
    succeeds(lz4::decompress_block_into, &block, &expected);
}

#[test]
fn cve_2026_32829_zero_offset_cannot_disclose_old_destination_bytes() {
    // Upstream regression fixture, independently exercised against our API:
    // PSeitz/lz4_flex@1bffdcbbf906a234b913937cb2f57c0245915038,
    // src/block/decompress_safe.rs::tests::offset_0.
    let zero_offset = [0x0e, 0, 0, 0x70, 0, 0, 0, 0, 0, 0, 0];
    for capacity in [0, 1, 17, 25, 256] {
        for previous_contents in [0, 0x5a, 0xa5, 0xff] {
            let mut destination = vec![previous_contents; capacity];
            let before = destination.clone();
            assert_eq!(
                lz4::decompress_block_into(&zero_offset, &mut destination),
                Err(Error::InvalidInput)
            );
            assert_eq!(destination, before);
        }
    }
}

#[test]
fn successful_lz4_output_is_independent_of_previous_destination_contents() {
    for offset in 1..=16 {
        for count in [7, 19, 274, 4096] {
            let (block, expected) = match_block(b"abcdefghijklmnop", offset, count);
            for previous_contents in [0, 0x5a, 0xa5, 0xff] {
                let mut destination = vec![previous_contents; expected.len() + 17];
                let n = lz4::decompress_block_into(&block, &mut destination).unwrap();
                assert_eq!(&destination[..n], expected);
                assert!(destination[n..].iter().all(|b| *b == previous_contents));
            }
        }
    }
}

#[test]
fn cve_2017_1000430_original_size_arithmetic_wraps_without_large_allocations() {
    // Model the NoWrap sizing expression before upstream fix 24ead980daf11ba:
    // (input_length / 3) * 4, plus four when input_length % 3 is nonzero.
    // Wrapping explicitly models release integer arithmetic. This exercises
    // the original expression, not the old encoder or an actual allocation.
    fn old_size_32(n: u32) -> u32 {
        (n / 3)
            .wrapping_mul(4)
            .wrapping_add(if n % 3 == 0 { 0 } else { 4 })
    }
    fn old_size_64(n: u64) -> u64 {
        (n / 3)
            .wrapping_mul(4)
            .wrapping_add(if n % 3 == 0 { 0 } else { 4 })
    }
    let n32 = (u32::MAX / 4 + 1) * 3;
    let n64 = (u64::MAX / 4 + 1) * 3;
    assert_eq!(old_size_32(n32), 0);
    assert_eq!(old_size_64(n64), 0);
    assert_eq!(4 * ((n32 as u128 + 2) / 3), 1u128 << 32);
    assert_eq!(4 * ((n64 as u128 + 2) / 3), 1u128 << 64);
    // No claim is made that these lengths can be allocated as valid Rust
    // slices, or that this reproduces a historically reachable exploit.
    for n in 0usize..128 {
        let input = generated(n);
        let required = 4 * n.div_ceil(3);
        let mut destination = vec![0xa5; required];
        assert_eq!(base64::encode_into(&input, &mut destination), Ok(required));
        if required > 0 {
            let mut short = vec![0x5a; required - 1];
            let before = short.clone();
            assert_eq!(
                base64::encode_into(&input, &mut short),
                Err(Error::OutputTooSmall)
            );
            assert_eq!(short, before);
        }
    }
}
