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
