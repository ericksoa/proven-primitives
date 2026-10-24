use proven_primitives::{base64, lz4, percent, Error};

fn main() -> Result<(), Error> {
    let mut encoded = [0u8; 8];
    let n = base64::encode_into(b"proof", &mut encoded)?;
    assert_eq!(&encoded[..n], b"cHJvb2Y=");

    let mut decoded = [0u8; 5];
    assert_eq!(base64::decode_into(&encoded[..n], &mut decoded)?, 5);
    assert_eq!(&decoded, b"proof");

    let mut escaped = [0u8; 16];
    let n = percent::encode_into(b"a+b c", &mut escaped)?;
    assert_eq!(&escaped[..n], b"a%2Bb%20c");

    let raw_block = [0x13, b'a', 1, 0, 0x50, b'a', b'a', b'a', b'a', b'a'];
    let mut expanded = [0u8; 13];
    let n = lz4::decompress_block_into(&raw_block, &mut expanded)?;
    assert_eq!(&expanded[..n], b"aaaaaaaaaaaaa");

    let mut destination = [0xa5u8; 8];
    assert_eq!(
        base64::decode_into(b"Zh==", &mut destination),
        Err(Error::InvalidInput)
    );
    assert_eq!(destination, [0xa5; 8]);
    println!("All three primitives produced the expected bytes; invalid input preserved its destination.");
    Ok(())
}
