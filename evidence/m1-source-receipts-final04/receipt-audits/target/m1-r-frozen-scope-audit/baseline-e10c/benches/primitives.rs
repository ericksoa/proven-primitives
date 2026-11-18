use base64_ref::{engine::general_purpose::STANDARD, Engine};
use proven_primitives::{base64, lz4, percent, Error};
use std::hint::black_box;
use std::time::Instant;

type Codec = fn(&[u8], &mut [u8]) -> Result<usize, Error>;

fn measure(name: &str, codec: Codec, input: &[u8], output: &mut [u8], logical_bytes: usize) {
    let size = codec(input, output).expect("valid benchmark input and sufficient destination");
    let iterations = (16 * 1024 * 1024 / logical_bytes.max(1)).clamp(3, 10_000);
    let started = Instant::now();
    for _ in 0..iterations {
        assert_eq!(
            black_box(codec(black_box(input), black_box(output))),
            Ok(size)
        );
    }
    let elapsed = started.elapsed();
    let mib_per_second =
        logical_bytes as f64 * iterations as f64 / (1024.0 * 1024.0) / elapsed.as_secs_f64();
    println!(
        "{name},{},{size},{iterations},{},{mib_per_second:.2}",
        input.len(),
        elapsed.as_nanos()
    );
}

fn literal_block(input: &[u8]) -> Vec<u8> {
    let mut out = vec![(input.len().min(15) as u8) << 4];
    if input.len() >= 15 {
        let mut extra = input.len() - 15;
        while extra >= 255 {
            out.push(255);
            extra -= 255;
        }
        out.push(extra as u8);
    }
    out.extend_from_slice(input);
    out
}

fn overlap_block(size: usize) -> Vec<u8> {
    let count = size - 6;
    let mut out = vec![0x1f, b'a', 1, 0];
    let mut extra = count - 19;
    while extra >= 255 {
        out.push(255);
        extra -= 255;
    }
    out.push(extra as u8);
    out.extend_from_slice(&[0x50, b'a', b'a', b'a', b'a', b'a']);
    out
}

fn main() {
    if std::env::args().any(|arg| arg == "--compare") {
        compare_upstream();
        return;
    }
    println!("primitive,input_bytes,output_bytes,iterations,elapsed_ns,logical_mib_per_second");
    for size in [64usize, 4096, 262_144] {
        let input: Vec<u8> = (0..size)
            .map(|i| (i.wrapping_mul(73).wrapping_add(19)) as u8)
            .collect();
        let mut b64 = vec![0; size.div_ceil(3) * 4];
        let mut escaped = vec![0; size * 3];
        let mut decoded = vec![0; size];
        measure("base64_encode", base64::encode_into, &input, &mut b64, size);
        measure(
            "base64_decode",
            base64::decode_into,
            &b64,
            &mut decoded,
            size,
        );
        let n = percent::encode_into(&input, &mut escaped).unwrap();
        measure(
            "percent_encode",
            percent::encode_into,
            &input,
            &mut escaped,
            size,
        );
        measure(
            "percent_decode",
            percent::decode_into,
            &escaped[..n],
            &mut decoded,
            size,
        );
        measure(
            "lz4_literals",
            lz4::decompress_block_into,
            &literal_block(&input),
            &mut decoded,
            size,
        );
        measure(
            "lz4_overlap",
            lz4::decompress_block_into,
            &overlap_block(size),
            &mut decoded,
            size,
        );
    }
}

type ComparisonCodec<'a> = dyn Fn(&[u8], &mut [u8]) -> Result<usize, ()> + 'a;

fn comparison_case(
    workload: &str,
    input: &[u8],
    capacity: usize,
    logical_bytes: usize,
    codecs: &[(&str, &ComparisonCodec<'_>)],
) {
    // Save the exact corpus outside timing for independent SHA-256 checks.
    std::fs::create_dir_all("evidence/corpus").unwrap();
    std::fs::write(
        format!("evidence/corpus/{workload}-{logical_bytes}.bin"),
        input,
    )
    .unwrap();
    let mut outputs = vec![vec![0xa5; capacity]; codecs.len()];
    let expected = (codecs[0].1)(input, &mut outputs[0]);
    for (i, (_, codec)) in codecs.iter().enumerate() {
        let result = codec(input, &mut outputs[i]);
        assert_eq!(result, expected, "{workload}: reference result");
        if let Ok(n) = result {
            assert_eq!(
                outputs[i][..n],
                outputs[0][..n],
                "{workload}: reference bytes"
            );
        }
        for _ in 0..10 {
            let _ = black_box(codec(black_box(input), black_box(&mut outputs[i])));
        }
    }
    let iterations = (2 * 1024 * 1024 / input.len().max(logical_bytes).max(1)).clamp(4, 50_000);
    for sample in 0..9 {
        // Rotate which implementation runs first to reduce ordering bias.
        for offset in 0..codecs.len() {
            let i = (sample + offset) % codecs.len();
            let (implementation, codec) = codecs[i];
            let output = &mut outputs[i];
            output.fill(0xa5);
            let start = Instant::now();
            for _ in 0..iterations {
                let _ = black_box(codec(black_box(input), black_box(&mut *output)));
            }
            let elapsed = start.elapsed().as_nanos();
            println!("{workload},{implementation},{logical_bytes},{},{capacity},{sample},{iterations},{elapsed},{:.6}",
                input.len(), elapsed as f64 / iterations as f64);
        }
    }
}

fn compare_upstream() {
    let own_encode = |i: &[u8], o: &mut [u8]| base64::encode_into(i, o).map_err(|_| ());
    let own_decode = |i: &[u8], o: &mut [u8]| base64::decode_into(i, o).map_err(|_| ());
    let scalar_encode = |i: &[u8], o: &mut [u8]| STANDARD.encode_slice(i, o).map_err(|_| ());
    let scalar_decode = |i: &[u8], o: &mut [u8]| STANDARD.decode_slice(i, o).map_err(|_| ());
    let own_lz4 = |i: &[u8], o: &mut [u8]| lz4::decompress_block_into(i, o).map_err(|_| ());
    let current_lz4 =
        |i: &[u8], o: &mut [u8]| lz4_ref::block::decompress_into(i, o).map_err(|_| ());
    let mut encoders: Vec<(&str, &ComparisonCodec<'_>)> =
        vec![("proven", &own_encode), ("base64_scalar", &scalar_encode)];
    let mut decoders: Vec<(&str, &ComparisonCodec<'_>)> =
        vec![("proven", &own_decode), ("base64_scalar", &scalar_decode)];
    #[cfg(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "neon")
    ))]
    let simd = base64_ref::engine::Simd::standard(base64_ref::engine::general_purpose::PAD);
    #[cfg(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "neon")
    ))]
    let simd_encode = |i: &[u8], o: &mut [u8]| simd.encode_slice(i, o).map_err(|_| ());
    #[cfg(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "neon")
    ))]
    let simd_decode = |i: &[u8], o: &mut [u8]| simd.decode_slice(i, o).map_err(|_| ());
    #[cfg(any(
        target_arch = "x86_64",
        all(target_arch = "aarch64", target_feature = "neon")
    ))]
    {
        encoders.push(("base64_simd", &simd_encode));
        decoders.push(("base64_simd", &simd_decode));
    }
    let lz4_codecs: [(&str, &ComparisonCodec<'_>); 2] =
        [("proven", &own_lz4), ("lz4_flex_safe", &current_lz4)];
    println!("workload,implementation,logical_bytes,input_bytes,capacity,sample,iterations,elapsed_ns,ns_per_call");
    for size in [8usize, 64, 4096, 262_144] {
        let input: Vec<u8> = (0..size)
            .map(|i| i.wrapping_mul(73).wrapping_add(19) as u8)
            .collect();
        let text = STANDARD.encode(&input);
        comparison_case("base64_encode", &input, text.len(), size, &encoders);
        comparison_case("base64_decode", text.as_bytes(), size, size, &decoders);
        comparison_case(
            "base64_decode_small_output",
            text.as_bytes(),
            size - 1,
            size,
            &decoders,
        );
        let mut malformed = text.into_bytes();
        *malformed.last_mut().unwrap() = b'!';
        comparison_case(
            "base64_decode_late_invalid",
            &malformed,
            size,
            size,
            &decoders,
        );
        comparison_case(
            "lz4_literals",
            &literal_block(&input),
            size,
            size,
            &lz4_codecs,
        );
        comparison_case(
            "lz4_upstream_compressed",
            &lz4_ref::block::compress(&input),
            size,
            size,
            &lz4_codecs,
        );
        if size >= 64 {
            let compressed = overlap_block(size);
            comparison_case("lz4_overlap", &compressed, size, size, &lz4_codecs);
            comparison_case(
                "lz4_overlap_small_output",
                &compressed,
                size - 1,
                size,
                &lz4_codecs,
            );
        }
    }
    comparison_case(
        "lz4_zero_offset",
        &[0x0e, 0, 0, 0x70, 0, 0, 0, 0, 0, 0, 0],
        256,
        0,
        &lz4_codecs,
    );
}
