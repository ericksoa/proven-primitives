//! Reproducible negative controls: compilation alone must not count as a proof.
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[test]
fn project_source_contains_no_proof_trust_bypasses() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    for name in [
        "lib.rs",
        "base64.rs",
        "percent.rs",
        "lz4.rs",
        "brotli_input.rs",
        "brotli_block.rs",
        "brotli_prefix.rs",
        "composition_demo.rs",
    ] {
        let source = fs::read_to_string(root.join(name)).unwrap();
        for forbidden in [
            "assume(",
            "admit(",
            "assume_specification",
            "external_body",
            "verifier::external",
            "uninterp spec",
            "axiom fn",
            "inline_air_stmt",
            "exec_allows_no_decreases_clause",
        ] {
            assert!(
                !source.contains(forbidden),
                "{name} contains forbidden proof shortcut {forbidden}"
            );
        }
    }
}

fn check(verus: &Path, root: &Path) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--no-cheating",
            "--num-threads",
            "1",
            "--triggers-mode",
            "silent",
            "--rlimit",
            "30",
        ])
        .current_dir(root)
        .output()
        .expect("run pinned Verus")
}

fn transcript(output: &std::process::Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_twenty_five_semantic_and_security_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let version = Command::new(&verus)
        .arg("--version")
        .output()
        .expect("read Verus version");
    assert!(version.status.success());
    assert!(String::from_utf8_lossy(&version.stdout).contains("0.2026.10.18.7d82994"));
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary =
        std::env::temp_dir().join(format!("proven-primitives-canaries-{}", std::process::id()));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    let sources = [
        "lib.rs",
        "base64.rs",
        "percent.rs",
        "lz4.rs",
        "brotli_input.rs",
        "brotli_block.rs",
        "brotli_prefix.rs",
        "composition_demo.rs",
    ];
    for name in sources {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    fs::create_dir_all(project.join("evidence")).unwrap();
    let baseline = check(&verus, &temporary);
    fs::write(
        project.join("evidence/canary-baseline.log"),
        transcript(&baseline),
    )
    .unwrap();
    assert!(
        baseline.status.success(),
        "unmodified positive control failed: {}",
        transcript(&baseline)
    );
    for (name, file, old, new) in [
        (
            "composition-passes-stale-scratch-suffix",
            "composition_demo.rs",
            "let middle = &scratch[..middle_n];",
            "let middle = &scratch[..];",
        ),
        (
            "composition-retains-length-on-base64-error",
            "composition_demo.rs",
            "self.published_len = None;\n        let ghost mut adapter_transitions: nat = 1;",
            "let ghost mut adapter_transitions: nat = 1;",
        ),
        (
            "composition-retains-length-on-percent-error",
            "composition_demo.rs",
            "Err(Error::InvalidInput) => {\n                proof { assert(adapter_transitions <= 8); }\n                return Err(ComposeError::PercentInvalid);\n            }",
            "Err(Error::InvalidInput) => {\n                proof { assert(adapter_transitions <= 8); }\n                self.published_len = Some(1);\n                return Err(ComposeError::PercentInvalid);\n            }",
        ),
        (
            "composition-publishes-whole-output",
            "composition_demo.rs",
            "self.published_len = Some(n);",
            "self.published_len = Some(output.len());",
        ),
        (
            "composition-collapses-base64-error",
            "composition_demo.rs",
            "return Err(ComposeError::Base64Invalid);",
            "return Err(ComposeError::ScratchTooSmall);",
        ),
        (
            "composition-omits-percent-work",
            "percent.rs",
            "let ghost mut decode_work: nat = 8 * input.len() as nat + 16;",
            "let ghost mut decode_work: nat = 16;",
        ),
        (
            "composition-rolls-back-scratch-after-downstream-error",
            "composition_demo.rs",
            "proof { assert(adapter_transitions <= 8); }\n                return Err(ComposeError::PercentInvalid);",
            "proof { assert(adapter_transitions <= 8); }\n                if scratch.len() > 0 { scratch[0] = 0; }\n                return Err(ComposeError::PercentInvalid);",
        ),
        (
            "brotli-block-switch-error-becomes-retryable",
            "brotli_block.rs",
            "return SwitchStep { consumed_fields: 0,\n                status: SwitchStatus::Failed(BlockSwitchError::InvalidBlockSwitch) };",
            "return SwitchStep { consumed_fields: 0,\n                status: SwitchStatus::NeedInput };",
        ),
        (
            "brotli-canonical-code-wrong-recurrence",
            "brotli_prefix.rs",
            "code = combined * 2;",
            "code = combined * 2 + 1;",
        ),
        (
            "brotli-pending-off-by-one-append",
            "brotli_input.rs",
            "self.pending[self.len] = byte;",
            "self.pending[self.len + 1] = byte;",
        ),
        (
            "brotli-reader-loses-retained-bit",
            "brotli_input.rs",
            "self.compact_after(width);",
            "self.compact_after(width + 1);",
        ),
        (
            "brotli-window-size-wrong-gap",
            "brotli_input.rs",
            "let window_size = (1u32 << window_bits) - 16;",
            "let window_size = (1u32 << window_bits) - 15;",
        ),
        (
            "brotli-invalid-header-becomes-retryable",
            "brotli_input.rs",
            "let status = HeaderStatus::Failed(HeaderError::InvalidHeader);",
            "let status = HeaderStatus::NeedInput;",
        ),
        (
            "brotli-appends-after-terminal-failure",
            "brotli_input.rs",
            "HeaderPhase::Failed(error) => {\n                return HeaderStep { consumed: 0, status: HeaderStatus::Failed(error) };\n            }",
            "HeaderPhase::Failed(error) => {\n                let _ = self.queue.read_bits(1, input, end_of_input);\n                return HeaderStep { consumed: 0, status: HeaderStatus::Failed(error) };\n            }",
        ),
        (
            "base64-validation-accepts-sentinel",
            "base64.rs",
            "    combined < 64\n}",
            "    (combined & 63) < 64\n}",
        ),
        (
            "base64-validation-small-before-invalid",
            "base64.rs",
            "if 6 > capacity - count { small = true; }",
            "if 6 > capacity - count { return Err(Error::OutputTooSmall); }",
        ),
        (
            "base64-batch-decode-wrong-shift",
            "base64.rs",
            "let x0 = ((packed >> 40) & 255) as u8;",
            "let x0 = ((packed >> 39) & 255) as u8;",
        ),
        (
            "base64-batch-encode-wrong-shift",
            "base64.rs",
            "let v0 = ((packed >> 42) & 63) as u8;",
            "let v0 = ((packed >> 41) & 63) as u8;",
        ),
        (
            "base64-decoder-accepts-null",
            "base64.rs",
            "const DECODE_TABLE: [u8; 256] = [\n    255,",
            "const DECODE_TABLE: [u8; 256] = [\n    0,",
        ),
        (
            "wrong-base64-alphabet",
            "base64.rs",
            "65, 66, 67, 68",
            "66, 66, 67, 68",
        ),
        (
            "plus-treated-as-space",
            "percent.rs",
            "if b != b'%' { return Some((b, i + 1)); }",
            "if b != b'%' { return Some((if b == b'+' { b' ' } else { b }, i + 1)); }",
        ),
        (
            "wrong-lz4-backreference",
            "lz4.rs",
            "let byte = output[j - step.offset];",
            "let byte = output[j - 1];",
        ),
        (
            "lz4-reads-stale-destination",
            "lz4.rs",
            "let byte = output[j - step.offset];",
            "let byte = output[j];",
        ),
        (
            "base64-undersized-output-guard",
            "base64.rs",
            "if groups > capacity / 4 {",
            "if groups > capacity / 4 + 1 {",
        ),
        (
            "lz4-fast-fill-reads-stale-destination",
            "lz4.rs",
            "let repeated = output[j - 1];",
            "let repeated = output[j];",
        ),
    ] {
        let path = temporary.join("src").join(file);
        let original = fs::read_to_string(project.join("src").join(file)).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check(&verus, &temporary);
        let log = transcript(&result);
        fs::write(
            project.join("evidence").join(format!("canary-{name}.log")),
            &log,
        )
        .unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied")
                || log.contains("precondition not satisfied")
                || log.contains("invariant not satisfied")
                || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}"
        );
        println!("REJECTED {name}: deliberately wrong implementation, unchanged specification");
        fs::write(&path, original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}
