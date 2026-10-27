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
            "60",
        ])
        .current_dir(root)
        .output()
        .expect("run pinned Verus")
}

fn check_brotli_prefix_function(verus: &Path, root: &Path, function: &str) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--verify-only-module",
            "brotli_prefix",
            "--verify-function",
            function,
            "--no-cheating",
            "--num-threads",
            "1",
            "--triggers-mode",
            "silent",
            "--rlimit",
            "60",
        ])
        .current_dir(root)
        .output()
        .expect("run selected pinned Verus root")
}

fn check_brotli_input_function(verus: &Path, root: &Path, function: &str) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--verify-only-module",
            "brotli_input",
            "--verify-function",
            function,
            "--no-cheating",
            "--num-threads",
            "1",
            "--triggers-mode",
            "silent",
            "--rlimit",
            "60",
        ])
        .current_dir(root)
        .output()
        .expect("run selected pinned Verus input root")
}

fn check_brotli_block_function(verus: &Path, root: &Path, function: &str) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--verify-only-module",
            "brotli_block",
            "--verify-function",
            function,
            "--no-cheating",
            "--num-threads",
            "1",
            "--triggers-mode",
            "silent",
            "--rlimit",
            "60",
        ])
        .current_dir(root)
        .output()
        .expect("run selected pinned Verus block root")
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
fn the_prover_rejects_twenty_eight_semantic_and_security_defects() {
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
            "brotli-workspace-record-offset-shifted",
            "brotli_prefix.rs",
            "let bytes = record * TREE_RECORD_BYTES;\n    let relative = region_offset + bytes;\n    let absolute = window_bytes + relative;",
            "let bytes = record * TREE_RECORD_BYTES;\n    let relative = region_offset + bytes;\n    let absolute = window_bytes + relative + 1;",
        ),
        (
            "brotli-workspace-reads-uninitialized-record",
            "brotli_prefix.rs",
            "if symbol >= initialized {",
            "if symbol > initialized {",
        ),
        (
            "brotli-workspace-total-off-by-one",
            "brotli_prefix.rs",
            "pub(crate) const STATE_BYTES: u32 = 16_384;",
            "pub(crate) const STATE_BYTES: u32 = 16_383;",
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_b3a_meta_header_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3a-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    let baseline = check(&verus, &temporary);
    fs::write(
        project.join("evidence/canary-b3a-baseline.log"),
        transcript(&baseline),
    )
    .unwrap();
    assert!(
        baseline.status.success(),
        "unmodified B3a positive control failed: {}",
        transcript(&baseline)
    );
    for (name, old, new) in [
        (
            "brotli-meta-reserved-bit-accepted",
            "MetaBlockPhase::Reserved { is_last } => {\n                if bits != 0 {",
            "MetaBlockPhase::Reserved { is_last } => {\n                if bits == 2 {",
        ),
        (
            "brotli-meta-exuberant-length-accepted",
            "if index + 1 == nibbles && nibbles > 4 && bits == 0 {",
            "if index + 1 == nibbles && nibbles > 4 && bits == 16 {",
        ),
        (
            "brotli-meta-exuberant-metadata-length-accepted",
            "if index + 1 == bytes && bytes > 1 && bits == 0 {",
            "if index + 1 == bytes && bytes > 1 && bits == 256 {",
        ),
        (
            "brotli-meta-truncation-becomes-retryable",
            "status: MetaBlockStatus::Failed(MetaBlockError::Truncated),",
            "status: MetaBlockStatus::NeedInput,",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_two_b3a_record_frame_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3a-frame-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in ["write_next_tree_record", "read_tree_record"] {
        let positive = check_brotli_prefix_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-workspace-write-swaps-code-bytes",
            "write_next_tree_record",
            "workspace[at + 1] = (record.code % 256) as u8;",
            "workspace[at + 1] = (record.code / 256) as u8;",
        ),
        (
            "brotli-workspace-read-uses-length-as-code-byte",
            "read_tree_record",
            "code: workspace[at + 1] as u16 | ((workspace[at + 2] as u16) << 8),",
            "code: workspace[at] as u16 | ((workspace[at + 2] as u16) << 8),",
        ),
    ] {
        let path = temporary.join("src/brotli_prefix.rs");
        let original = fs::read_to_string(project.join("src/brotli_prefix.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_prefix_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3a_builder_storage_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3a-builder-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "write_next_builder_code_length",
        "read_builder_code_length",
        "write_next_builder_count",
        "write_next_builder_next_code",
        "write_next_tree_record",
        "install_builder_canonical_tree",
    ] {
        let positive = check_brotli_prefix_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-builder-code-length-write-shifts-region",
            "write_next_builder_code_length",
            "BUILDER_CODE_LENGTHS_OFFSET,\n        BUILDER_CODE_LENGTHS,\n        1,\n        initialized,",
            "BUILDER_CODE_LENGTHS_OFFSET + 1,\n        BUILDER_CODE_LENGTHS,\n        1,\n        initialized,",
        ),
        (
            "brotli-builder-code-length-reads-uninitialized-entry",
            "read_builder_code_length",
            "if index >= initialized {\n        return Err(WorkspaceError::UninitializedRecord);\n    }\n    proof { fixed_layout_is_exact(); }\n    let at = match builder_entry_offset(\n        window_bytes,\n        BUILDER_CODE_LENGTHS_OFFSET,",
            "if index > initialized {\n        return Err(WorkspaceError::UninitializedRecord);\n    }\n    proof { fixed_layout_is_exact(); }\n    let at = match builder_entry_offset(\n        window_bytes,\n        BUILDER_CODE_LENGTHS_OFFSET,",
        ),
        (
            "brotli-builder-count-write-swaps-low-byte",
            "write_next_builder_count",
            "workspace[at] = (value % 256) as u8;\n    workspace[at + 1] = (value / 256) as u8;\n    Ok(initialized + 1)\n}\n\npub(crate) fn read_builder_count",
            "workspace[at] = (value / 256) as u8;\n    workspace[at + 1] = (value / 256) as u8;\n    Ok(initialized + 1)\n}\n\npub(crate) fn read_builder_count",
        ),
        (
            "brotli-builder-next-code-writes-wrong-third-byte",
            "write_next_builder_next_code",
            "workspace[at + 2] = ((value / 65_536) % 256) as u8;\n    workspace[at + 3] = (value / 16_777_216) as u8;\n    Ok(initialized + 1)\n}\n\npub(crate) fn read_builder_next_code",
            "workspace[at + 2] = ((value / 32_768) % 256) as u8;\n    workspace[at + 3] = (value / 16_777_216) as u8;\n    Ok(initialized + 1)\n}\n\npub(crate) fn read_builder_next_code",
        ),
        (
            "brotli-canonical-record-rejects-unused-zero-length",
            "write_next_tree_record",
            "if record.length > MAX_BITS {",
            "if record.length == 0 || record.length > MAX_BITS {",
        ),
        (
            "brotli-canonical-installation-assigns-next-code",
            "install_builder_canonical_tree",
            "record.code = combined as u16;",
            "record.code = (combined + 1) as u16;",
        ),
    ] {
        let path = temporary.join("src/brotli_prefix.rs");
        let original = fs::read_to_string(project.join("src/brotli_prefix.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_prefix_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_b3b_inverse_mtf_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-mtf-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in ["inverse_mtf_context_map", "mtf_move_rank"] {
        let positive = check_brotli_prefix_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-mtf-initializes-list-to-zero",
            "inverse_mtf_context_map",
            "workspace[list_base + init as usize] = init as u8;",
            "workspace[list_base + init as usize] = 0;",
        ),
        (
            "brotli-mtf-shifts-from-current-cell",
            "mtf_move_rank",
            "let source_index = (cursor - 1) as usize;",
            "let source_index = cursor as usize;",
        ),
        (
            "brotli-mtf-undercharges-each-rank",
            "inverse_mtf_context_map",
            "work = work + 2 * rank as u64 + 6;",
            "work = work + 2 * rank as u64 + 5;",
        ),
        (
            "brotli-mtf-reuses-too-little-list-prefix",
            "inverse_mtf_context_map",
            "let next_bound = rank_or >> 2;",
            "let next_bound = rank_or >> 3;",
        ),
    ] {
        let path = temporary.join("src/brotli_prefix.rs");
        let original = fs::read_to_string(project.join("src/brotli_prefix.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_prefix_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3b_metadata_map_and_coverage_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-map-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "write_tree_metadata",
        "fixed_layout_is_exact",
        "read_tree_metadata",
        "context_entry_offset",
        "read_context_entry",
        "check_context_tree_coverage",
    ] {
        let positive = check_brotli_prefix_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-metadata-single-uses-wrong-tag-bit",
            "write_tree_metadata",
            "proof { single_metadata_descriptor_is_exact(symbol); }\n            0x8000u16 | symbol",
            "proof { single_metadata_descriptor_is_exact(symbol); }\n            0x4000u16 | symbol",
        ),
        (
            "brotli-metadata-block-length-overlaps-block-type",
            "fixed_layout_is_exact",
            "pub(crate) const BLOCK_LENGTH_METADATA_OFFSET: u32 = 1_163_260;",
            "pub(crate) const BLOCK_LENGTH_METADATA_OFFSET: u32 = 1_163_248;",
        ),
        (
            "brotli-metadata-reads-first-inactive-record",
            "read_tree_metadata",
            "if tree >= initialized_prefix {",
            "if tree > initialized_prefix {",
        ),
        (
            "brotli-distance-context-map-uses-literal-region",
            "context_entry_offset",
            "ContextMapKind::Distance => (DISTANCE_CONTEXT_MAP_OFFSET, DISTANCE_CONTEXT_MAP_BYTES),",
            "ContextMapKind::Distance => (LITERAL_CONTEXT_MAP_OFFSET, DISTANCE_CONTEXT_MAP_BYTES),",
        ),
        (
            "brotli-context-map-reads-first-uninitialized-entry",
            "read_context_entry",
            "if num_htrees == 0 || num_htrees > 256 {\n        return Err(WorkspaceError::InvalidSymbol);\n    }\n    if index >= initialized {",
            "if num_htrees == 0 || num_htrees > 256 {\n        return Err(WorkspaceError::InvalidSymbol);\n    }\n    if index > initialized {",
        ),
        (
            "brotli-context-coverage-accepts-any-present-tree",
            "check_context_tree_coverage",
            "complete = complete && present;",
            "complete = complete || present;",
        ),
    ] {
        let path = temporary.join("src/brotli_prefix.rs");
        let original = fs::read_to_string(project.join("src/brotli_prefix.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_prefix_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_two_b3b_distance_and_exhaustion_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-input-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in ["decode_distance_parameters", "advance_var_uint8"] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-distance-postfix-uses-upper-four-bits",
            "decode_distance_parameters",
            "let postfix = bits % 4;\n    let upper = bits / 4;",
            "let postfix = bits / 4;\n    let upper = bits / 4;",
        ),
        (
            "brotli-varuint-final-exhaustion-needs-more-input",
            "advance_var_uint8",
            "BitReadStatus::Truncated => return VarUint8Step {\n            consumed: read.consumed,\n            status: VarUint8Status::Truncated,",
            "BitReadStatus::Truncated => return VarUint8Step {\n            consumed: read.consumed,\n            status: VarUint8Status::NeedInput,",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_b3b_adapter_failure_as_retryable() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-adapter-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    let function = "advance_b3b_switch";
    let positive = check_brotli_block_function(&verus, &temporary, function);
    assert!(
        positive.status.success(),
        "unmodified selected root failed: {}",
        transcript(&positive)
    );
    let name = "brotli-b3b-adapter-turns-failure-into-need-input";
    let old = "SwitchStatus::Failed(error) => {\n            B3bSwitchOutcome::Failed(b2_failure_to_b3b(error))\n        }";
    let new =
        "SwitchStatus::Failed(_error) => {\n            B3bSwitchOutcome::NeedInput\n        }";
    let path = temporary.join("src/brotli_block.rs");
    let original = fs::read_to_string(project.join("src/brotli_block.rs")).unwrap();
    assert_eq!(
        original.matches(old).count(),
        1,
        "unique mutation anchor for {name}"
    );
    fs::write(&path, original.replacen(old, new, 1)).unwrap();
    let result = check_brotli_block_function(&verus, &temporary, function);
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
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3a_code_description_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3a-code-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "*CodeDescriptionDecoder*",
        "process_complex_code_length",
        "code_length_order_is_rfc",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-code-selector-misclassifies-simple",
            "*CodeDescriptionDecoder*",
            "assert(field < 4);\n                if field == 1 {",
            "assert(field < 4);\n                if field == 0 {",
        ),
        (
            "brotli-simple-code-accepts-limit-value",
            "*CodeDescriptionDecoder*",
            "if field >= self.alphabet_limit as u64 {",
            "if field > self.alphabet_limit as u64 {",
        ),
        (
            "brotli-simple-code-accepts-duplicate-symbol",
            "*CodeDescriptionDecoder*",
            "if duplicate {",
            "if duplicate && symbol == u16::MAX {",
        ),
        (
            "brotli-complex-static-prefix-maps-four-to-five",
            "*CodeDescriptionDecoder*",
            "process_complex_code_length(progress, 4)",
            "process_complex_code_length(progress, 5)",
        ),
        (
            "brotli-complex-code-misclassifies-space-overflow",
            "process_complex_code_length",
            "if amount > progress.space {\n            return CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace);",
            "if amount > progress.space {\n            return CodeDescriptionPhase::Failed(CodeDescriptionError::InvalidAlphabet);",
        ),
        (
            "brotli-code-length-order-starts-at-zero",
            "code_length_order_is_rfc",
            "const CODE_LENGTH_ORDER: [u8; 18] = [\n    1, 2, 3, 4, 0, 5,",
            "const CODE_LENGTH_ORDER: [u8; 18] = [\n    0, 2, 3, 4, 0, 5,",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_b3a_auxiliary_code_without_bit_reversal() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3a-reversal-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }

    let function = "decode_auxiliary_symbol";
    let positive = check_brotli_input_function(&verus, &temporary, function);
    assert!(
        positive.status.success(),
        "unmodified selected root failed: {}",
        transcript(&positive)
    );

    let name = "brotli-auxiliary-code-compares-natural-instead-of-reversed";
    let old = "let reversed = reverse_auxiliary_code(candidate, width);\n                if reversed == bits {";
    let new = "let reversed = reverse_auxiliary_code(candidate, width);\n                if candidate == bits as u32 {";
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
    assert_eq!(
        original.matches(old).count(),
        1,
        "unique mutation anchor for {name}"
    );
    fs::write(&path, original.replacen(old, new, 1)).unwrap();
    let result = check_brotli_input_function(&verus, &temporary, function);
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
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_two_b3b_state_layout_and_bit_order_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-layout-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in ["b3b_scalar_layout_is_exact", "reverse_installed_code"] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-b3b-outer-phase-overlaps-terminal-tag",
            "b3b_scalar_layout_is_exact",
            "const B3B_OUTER_PHASE: u16 = 10;",
            "const B3B_OUTER_PHASE: u16 = 11;",
        ),
        (
            "brotli-installed-code-omits-reversed-head-bit",
            "reverse_installed_code",
            "installed_reverse_combine_fits(bit, width, rest);\n        }\n        bit * (1u16 << ((width - 1) as u8)) + rest",
            "installed_reverse_combine_fits(bit, width, rest);\n        }\n        rest",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_b3b_installed_symbol_without_bit_reversal() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-installed-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    let function = "advance_installed_tree_symbol";
    let positive = check_brotli_input_function(&verus, &temporary, function);
    assert!(
        positive.status.success(),
        "unmodified selected root failed: {}",
        transcript(&positive)
    );
    let name = "brotli-installed-symbol-compares-natural-code";
    let old = "if reversed == next_bits {";
    let new = "if record.code == next_bits {";
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
    assert_eq!(
        original.matches(old).count(),
        1,
        "unique mutation anchor for {name}"
    );
    fs::write(&path, original.replacen(old, new, 1)).unwrap();
    let result = check_brotli_input_function(&verus, &temporary, function);
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
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_b3b_block_count_and_category_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-block-count-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "*CompressedMetaBlockDecoder*",
        "CompressedMetaBlockDecoder::apply_block_count_value",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-b3b-one-type-initial-length-is-short",
            "CompressedMetaBlockDecoder::apply_block_count_value",
            "put_state_u32(\n                self.workspace,\n                self.window_bytes,\n                B3B_INITIAL_LENGTHS + 4 * kind as u16,\n                1u32 << 24,\n            )?;",
            "put_state_u32(\n                self.workspace,\n                self.window_bytes,\n                B3B_INITIAL_LENGTHS + 4 * kind as u16,\n                1u32 << 23,\n            )?;",
        ),
        (
            "brotli-b3b-block-count-omits-plus-one",
            "*CompressedMetaBlockDecoder*",
            "let count = raw + 1;",
            "let count = if raw == 0 { 1 } else { raw };",
        ),
        (
            "brotli-b3b-one-type-category-builds-trees",
            "*CompressedMetaBlockDecoder*",
            "if count == 1 {",
            "if count == 1 && kind == 255 {",
        ),
        (
            "brotli-b3b-category-order-skips-command",
            "*CompressedMetaBlockDecoder*",
            "B3B_CURRENT_KIND,\n                kind + 1,",
            "B3B_CURRENT_KIND,\n                if kind == 0 { 2 } else { kind + 1 },",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_thirteen_b3b_context_map_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-context-tree-count-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "advance_context_tree_count_phase",
        "advance_context_bits_phase",
        "advance_context_symbol_phase",
        "advance_context_coverage_phase",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-b3b-context-tree-count-omits-plus-one-for-zero",
            "advance_context_tree_count_phase",
            "let num_trees = raw + 1;",
            "let num_trees = if raw == 0 { 2 } else { raw + 1 };",
        ),
        (
            "brotli-b3b-context-phase-one-reads-two-bits",
            "advance_context_bits_phase",
            "if phase == 1 {\n                    (1usize, 0u8)",
            "if phase == 1 {\n                    (2usize, 0u8)",
        ),
        (
            "brotli-b3b-context-phase-two-reads-three-bits",
            "advance_context_bits_phase",
            "else if phase == 2 { (4usize, 0u8) }",
            "else if phase == 2 { (3usize, 0u8) }",
        ),
        (
            "brotli-b3b-context-rle-suffix-is-one-bit-short",
            "advance_context_bits_phase",
            "(pending as usize, pending)",
            "((pending - 1) as usize, pending)",
        ),
        (
            "brotli-b3b-context-phase-six-reads-two-bits",
            "advance_context_bits_phase",
            "else if phase == 6 { (1usize, 0u8) }",
            "else if phase == 6 { (2usize, 0u8) }",
        ),
        (
            "brotli-b3b-context-need-input-does-not-suspend",
            "advance_context_bits_phase",
            "BitReadStatus::NeedInput => {\n                        let result = (consumed, Some(ContextAdvanceStatus::NeedInput));",
            "BitReadStatus::NeedInput => {\n                        let result = (consumed, None);",
        ),
        (
            "brotli-b3b-context-exact-fill-is-overflow",
            "advance_context_bits_phase",
            "if index as u32 + repeat > active_len as u32 {",
            "if index as u32 + repeat >= active_len as u32 {",
        ),
        (
            "brotli-b3b-context-rle-writes-one",
            "advance_context_bits_phase",
            "initialized = match crate::brotli_prefix::write_next_context_entry(\n                                    workspace, window_bytes, kind, active_len,\n                                    initialized, 0, num_trees) {",
            "initialized = match crate::brotli_prefix::write_next_context_entry(\n                                    workspace, window_bytes, kind, active_len,\n                                    initialized, 1, num_trees) {",
        ),
        (
            "brotli-b3b-context-temporary-alphabet-adds-one",
            "advance_context_bits_phase",
            "let alphabet = num_trees + max_run as u16;",
            "let alphabet = num_trees + max_run as u16 + 1;",
        ),
        (
            "brotli-b3b-context-zero-mtf-flag-routes-to-mtf",
            "advance_context_bits_phase",
            "} else if value == 0 {\n                            if let Err(error) = store_context_phase(\n                                workspace, window_bytes, 8) {",
            "} else if value == 0 {\n                            if let Err(error) = store_context_phase(\n                                workspace, window_bytes, 7) {",
        ),
        (
            "brotli-b3b-context-direct-value-is-one-low",
            "store_context_direct_symbol",
            "let value = symbol - max_run as u16;\n    proof { bounded_u16_fits_u8(value); }",
            "let value = symbol - max_run as u16 - 1;\n    proof { bounded_u16_fits_u8(value); }",
        ),
        (
            "brotli-b3b-context-symbol-uses-literal-tree-region",
            "advance_context_symbol_phase",
            "let symbol_step = advance_installed_tree_symbol(\n                        workspace,\n                        window_bytes,\n                        crate::brotli_prefix::TreeRegion::TemporaryContext,",
            "let symbol_step = advance_installed_tree_symbol(\n                        workspace,\n                        window_bytes,\n                        crate::brotli_prefix::TreeRegion::Literal,",
        ),
        (
            "brotli-b3b-context-coverage-rejects-covered-map",
            "advance_context_coverage_phase",
            "if !covered {",
            "if covered {",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3b_tree_group_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-tree-group-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "CompressedMetaBlockDecoder::advance_tree_groups_phase",
        "CompressedMetaBlockDecoder::group_parameters",
        "CompressedMetaBlockDecoder::complete_tree_groups",
        "install_completed_simple_tree",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-b3b-completed-simple-tree-writes-unused-metadata",
            "install_completed_simple_tree",
            "    match crate::brotli_prefix::write_tree_metadata(\n        workspace,\n        window_bytes,\n        region,\n        tree,\n        meta,\n    ) {",
            "    match crate::brotli_prefix::write_tree_metadata(\n        workspace,\n        window_bytes,\n        region,\n        tree,\n        crate::brotli_prefix::TreeMetadata::unused(),\n    ) {",
        ),
        (
            "brotli-b3b-tree-group-order-skips-command",
            "CompressedMetaBlockDecoder::advance_tree_groups_phase",
            "if group < 2 {\n                                    let next_group = group + 1;\n                                    proof {\n                                        assert(next_group == group + 1);",
            "if group < 2 {\n                                    let next_group = if group == 0 { 2 } else { group + 1 };\n                                    proof {\n                                        assert(next_group == group + 1);",
        ),
        (
            "brotli-b3b-command-group-uses-distance-count",
            "CompressedMetaBlockDecoder::group_parameters",
            "let count = state_u16(\n                    self.workspace, self.window_bytes, B3B_BLOCK_COUNTS + 2)?;",
            "let count = state_u16(\n                    self.workspace, self.window_bytes, B3B_BLOCK_COUNTS + 4)?;",
        ),
        (
            "brotli-b3b-tree-group-index-advances-by-two",
            "CompressedMetaBlockDecoder::advance_tree_groups_phase",
            "let next = tree + 1;",
            "let next = tree + 2;",
        ),
        (
            "brotli-b3b-command-group-alphabet-is-703",
            "CompressedMetaBlockDecoder::group_parameters",
            "Ok((crate::brotli_prefix::TreeRegion::Command, count, 704))",
            "Ok((crate::brotli_prefix::TreeRegion::Command, count, 703))",
        ),
        (
            "brotli-b3b-active-command-tree-starts-at-one",
            "CompressedMetaBlockDecoder::complete_tree_groups",
            "put_state_u16(self.workspace, self.window_bytes, B3B_ACTIVE_COMMAND_TREE, 0)?;",
            "put_state_u16(self.workspace, self.window_bytes, B3B_ACTIVE_COMMAND_TREE, 1)?;",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3b_cross_call_state_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-cross-call-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "drain_serialized_pending_span",
        "CompressedMetaBlockDecoder::repeat_terminal_failure",
        "CompressedMetaBlockDecoder::step",
        "store_context_map_progress",
        "advance_context_mtf_phase",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-b3b-pending-span-is-not-drained",
            "drain_serialized_pending_span",
            "let acknowledged = acknowledge_serialized_pending_span(decoder);",
            "let acknowledged = CodeDescriptionStep { consumed: 0, status: CodeDescriptionStatus::Progress };",
        ),
        (
            "brotli-b3b-sticky-failure-consumes-one-byte",
            "CompressedMetaBlockDecoder::repeat_terminal_failure",
            "CompressedHeaderStep {\n            consumed: 0,\n            status: CompressedHeaderStatus::Failed(error),\n        }",
            "CompressedHeaderStep {\n            consumed: 1,\n            status: CompressedHeaderStatus::Failed(error),\n        }",
        ),
        (
            "brotli-b3b-sticky-failure-becomes-need-input",
            "CompressedMetaBlockDecoder::repeat_terminal_failure",
            "CompressedHeaderStep {\n            consumed: 0,\n            status: CompressedHeaderStatus::Failed(error),\n        }",
            "CompressedHeaderStep {\n            consumed: 0,\n            status: CompressedHeaderStatus::NeedInput,\n        }",
        ),
        (
            "brotli-b3b-step-bypasses-sticky-failure-helper",
            "CompressedMetaBlockDecoder::step",
            "return self.repeat_terminal_failure(error);",
            "return CompressedHeaderStep { consumed: input.len(), status: CompressedHeaderStatus::Failed(error) };",
        ),
        (
            "brotli-b3b-context-progress-leaves-stale-initialized-length",
            "store_context_map_progress",
            "put_state_u16(workspace, window_bytes, B3B_MAP_INITIALIZED, progress)",
            "put_state_u16(workspace, window_bytes, B3B_MAP_INDEX, progress)",
        ),
        (
            "brotli-b3b-context-mtf-leaves-stale-reuse-bound",
            "advance_context_mtf_phase",
            "put_state_byte(\n        workspace,\n        window_bytes,\n        B3B_MTF_UPPER_BOUND,\n        next_upper,\n    )",
            "put_state_byte(\n        workspace,\n        window_bytes,\n        B3B_MTF_UPPER_BOUND,\n        upper,\n    )",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_seven_b3b_stride_initialization_and_exhaustion_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-stride-init-exhaustion-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "CompressedMetaBlockDecoder::advance_context_modes_phase",
        "CompressedMetaBlockDecoder::advance_context_maps_phase",
        "start_serialized_tree",
        "advance_context_bits_phase",
        "handle_context_installed_symbol_status",
        "CodeDescriptionDecoder::advance_field",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-b3b-literal-context-row-stride-is-63",
            "CompressedMetaBlockDecoder::advance_context_modes_phase",
            "let active_len = literal_count * 64;",
            "let active_len = literal_count * 63;",
        ),
        (
            "brotli-b3b-distance-context-row-stride-is-three",
            "CompressedMetaBlockDecoder::advance_context_maps_phase",
            "if let Err(error) = start_context_map(\n                                    self.workspace,\n                                    self.window_bytes,\n                                    crate::brotli_prefix::ContextMapKind::Distance,\n                                    distance_types * 4,\n                                )",
            "if let Err(error) = start_context_map(\n                                    self.workspace,\n                                    self.window_bytes,\n                                    crate::brotli_prefix::ContextMapKind::Distance,\n                                    distance_types * 3,\n                                )",
        ),
        (
            "brotli-b3b-serialized-tree-skips-builder-reset",
            "start_serialized_tree",
            "put_state_u16(workspace, window_bytes, B3B_BUILDER_INITIALIZED, 0)",
            "Ok(())",
        ),
        (
            "brotli-b3b-context-tree-starts-in-literal-region",
            "advance_context_bits_phase",
            "if value == 0 {\n                                if let Err(error) = start_serialized_tree(\n                                    workspace,\n                                    window_bytes,\n                                    crate::brotli_prefix::TreeRegion::TemporaryContext,",
            "if value == 0 {\n                                if let Err(error) = start_serialized_tree(\n                                    workspace,\n                                    window_bytes,\n                                    crate::brotli_prefix::TreeRegion::Literal,",
        ),
        (
            "brotli-b3b-installed-symbol-truncation-needs-input",
            "handle_context_installed_symbol_status",
            "InstalledSymbolStatus::Truncated => Some(ContextAdvanceStatus::Failed(\n            CompressedHeaderError::Truncated,\n        )),",
            "InstalledSymbolStatus::Truncated => Some(ContextAdvanceStatus::NeedInput),",
        ),
        (
            "brotli-b3b-context-bit-truncation-needs-input",
            "advance_context_bits_phase",
            "BitReadStatus::Truncated => return (consumed, Some(ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated),)),",
            "BitReadStatus::Truncated => return (consumed, Some(ContextAdvanceStatus::NeedInput)),",
        ),
        (
            "brotli-b3b-tree-field-truncation-needs-input",
            "CodeDescriptionDecoder::advance_field",
            "self.phase = CodeDescriptionPhase::Failed(CodeDescriptionError::Truncated);\n                return CodeDescriptionStep {\n                    consumed: read.consumed,\n                    status: CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated),",
            "self.phase = CodeDescriptionPhase::Failed(CodeDescriptionError::Truncated);\n                return CodeDescriptionStep {\n                    consumed: read.consumed,\n                    status: CodeDescriptionStatus::NeedInput,",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3b_serialization_and_error_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3b-state-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "context_zero_repeat_exec",
        "b3b_state_address",
        "write_b3b_state_u16",
        "write_b3b_state_tag",
        "store_terminal_error",
        "load_terminal_error",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-context-repeat-uses-half-base",
            "context_zero_repeat_exec",
            "let base = 1u32 << symbol;",
            "let base = 1u32 << (symbol - 1);",
        ),
        (
            "brotli-b3b-state-address-shifts-scalar-block",
            "b3b_state_address",
            ".checked_add(B3B_SCALAR_OFFSET as usize) {",
            ".checked_add(B3B_SCALAR_OFFSET as usize + 1) {",
        ),
        (
            "brotli-b3b-u16-writes-low-byte-twice",
            "write_b3b_state_u16",
            "proof { encode_b3b_u16_le(value); }\n    workspace[at] = value as u8;\n    workspace[at + 1] = (value >> 8) as u8;",
            "proof { encode_b3b_u16_le(value); }\n    workspace[at] = value as u8;\n    workspace[at + 1] = value as u8;",
        ),
        (
            "brotli-b3b-tag-accepts-first-invalid-value",
            "write_b3b_state_tag",
            "if value >= variants {\n        return Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol);\n    }\n    write_b3b_state_byte",
            "if value > variants {\n        return Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol);\n    }\n    write_b3b_state_byte",
        ),
        (
            "brotli-terminal-store-marks-state-complete",
            "store_terminal_error",
            "write_b3b_state_tag(workspace, window_bytes, B3B_OUTER_PHASE, 13, 12)",
            "write_b3b_state_tag(workspace, window_bytes, B3B_OUTER_PHASE, 13, 11)",
        ),
        (
            "brotli-terminal-load-turns-truncation-unsupported",
            "load_terminal_error",
            "2 if detail == 0 => Ok(CompressedHeaderError::Truncated),",
            "2 if detail == 0 => Ok(CompressedHeaderError::UnsupportedMode),",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3a_repeat_stream_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3a-repeat-canaries-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
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
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    for function in [
        "start_complex_symbol_progress",
        "process_repeated_symbol_length",
    ] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive)
        );
    }
    for (name, function, old, new) in [
        (
            "brotli-repeat-initial-previous-length-is-not-eight",
            "start_complex_symbol_progress",
            "prev_code_len: 8,",
            "prev_code_len: 7,",
        ),
        (
            "brotli-repeat-does-not-reset-after-length-change",
            "process_repeated_symbol_length",
            "let old_repeat = if progress.repeat_code_len != length {\n        0",
            "let old_repeat = if progress.repeat_code_len == length {\n        0",
        ),
        (
            "brotli-repeat-chain-subtracts-one-instead-of-two",
            "process_repeated_symbol_length",
            "(old_repeat - 2) << extra_bits",
            "(old_repeat - 1) << extra_bits",
        ),
        (
            "brotli-repeat-chain-adds-four-instead-of-three",
            "process_repeated_symbol_length",
            "let next_repeat = base + suffix as u32 + 3;",
            "let next_repeat = base + suffix as u32 + 4;",
        ),
        (
            "brotli-repeat-rejects-an-exact-alphabet-fill",
            "process_repeated_symbol_length",
            "if delta > alphabet_limit as u32 - progress.symbol as u32 {",
            "if delta >= alphabet_limit as u32 - progress.symbol as u32 {",
        ),
        (
            "brotli-repeat-undercharges-final-code-space",
            "process_repeated_symbol_length",
            "let amount = weight * delta;",
            "let amount = weight * (delta - 1);",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
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
