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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "1000",
            "--multiple-errors",
            "0",
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

fn check_brotli_function(verus: &Path, root: &Path, function: &str) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--verify-only-module",
            "brotli",
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
        .expect("run selected pinned Verus public Brotli root")
}

fn check_brotli_data_function(verus: &Path, root: &Path, function: &str) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--verify-only-module",
            "brotli_data",
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
        .expect("run selected pinned Verus Brotli data root")
}

fn check_brotli_data_function_high(
    verus: &Path,
    root: &Path,
    function: &str,
) -> std::process::Output {
    Command::new(verus)
        .arg(root.join("src/lib.rs"))
        .args([
            "--crate-type",
            "lib",
            "--verify-only-module",
            "brotli_data",
            "--verify-function",
            function,
            "--no-cheating",
            "--num-threads",
            "1",
            "--triggers-mode",
            "silent",
            "--rlimit",
            "300",
        ])
        .current_dir(root)
        .output()
        .expect("run selected high-limit Brotli data root")
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "    if initialized > BUILDER_CODE_LENGTHS || index >= BUILDER_CODE_LENGTHS {\n        return (Err(WorkspaceError::InvalidSymbol), Ghost(r_source_units));\n    }\n    if index >= initialized {\n        return (Err(WorkspaceError::UninitializedRecord), Ghost(r_source_units));\n    }\n    proof { fixed_layout_is_exact(); }",
            "    if initialized > BUILDER_CODE_LENGTHS || index >= BUILDER_CODE_LENGTHS {\n        return (Err(WorkspaceError::InvalidSymbol), Ghost(r_source_units));\n    }\n    if index > initialized {\n        return (Err(WorkspaceError::UninitializedRecord), Ghost(r_source_units));\n    }\n    proof { fixed_layout_is_exact(); }",
        ),
        (
            "brotli-builder-count-write-swaps-low-byte",
            "write_next_builder_count",
            "        BUILDER_COUNTS,\n        2,\n        initialized,\n    ) {\n        Ok(value) => value,\n        Err(error) => return (Err(error), Ghost(r_source_units)),\n    };\n    workspace[at] = (value % 256) as u8;\n    proof { r_source_units = r_source_units + 1; }\n    workspace[at + 1] = (value / 256) as u8;\n    proof { r_source_units = r_source_units + 1; }\n    let ordinary_result = {\n        Ok(initialized + 1)\n    };\n    (ordinary_result, Ghost(r_source_units))",
            "        BUILDER_COUNTS,\n        2,\n        initialized,\n    ) {\n        Ok(value) => value,\n        Err(error) => return (Err(error), Ghost(r_source_units)),\n    };\n    workspace[at] = (value / 256) as u8;\n    proof { r_source_units = r_source_units + 1; }\n    workspace[at + 1] = (value / 256) as u8;\n    proof { r_source_units = r_source_units + 1; }\n    let ordinary_result = {\n        Ok(initialized + 1)\n    };\n    (ordinary_result, Ghost(r_source_units))",
        ),
        (
            "brotli-builder-next-code-writes-wrong-third-byte",
            "write_next_builder_next_code",
            "    proof { r_source_units = r_source_units + 1; }\n    workspace[at + 2] = ((value / 65_536) % 256) as u8;\n    proof { r_source_units = r_source_units + 1; }",
            "    proof { r_source_units = r_source_units + 1; }\n    workspace[at + 2] = ((value / 32_768) % 256) as u8;\n    proof { r_source_units = r_source_units + 1; }",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "    if num_htrees == 0 || num_htrees > 256 {\n        return (Err(WorkspaceError::InvalidSymbol), Ghost(r_source_units));\n    }\n    if index >= initialized {\n        return (Err(WorkspaceError::UninitializedRecord), Ghost(r_source_units));\n    }\n    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {",
            "    if num_htrees == 0 || num_htrees > 256 {\n        return (Err(WorkspaceError::InvalidSymbol), Ghost(r_source_units));\n    }\n    if index > initialized {\n        return (Err(WorkspaceError::UninitializedRecord), Ghost(r_source_units));\n    }\n    let required = match (window_bytes as usize).checked_add(FIXED_SCRATCH_BYTES as usize) {",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "            status: VarUint8Status::Truncated,",
            "            status: VarUint8Status::NeedInput,",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "            return (CodeDescriptionPhase::Failed(CodeDescriptionError::CodeLengthSpace), Ghost(source_reads));",
            "            return (CodeDescriptionPhase::Failed(CodeDescriptionError::InvalidAlphabet), Ghost(source_reads));",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
    let start = original
        .find(&format!("fn {function}("))
        .expect("selected function exists");
    let end = start
        + original[start..]
            .find("\n}\n")
            .expect("selected function ends")
        + 3;
    let selected = &original[start..end];
    assert_eq!(
        selected.matches(old).count(),
        1,
        "unique mutation anchor for {name}"
    );
    fs::write(
        &path,
        format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        ),
    )
    .unwrap();
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "let next_reversed = 2 * reversed + bit;",
            "let next_reversed = 2 * reversed + if remaining == 1 { bit } else { 0 };",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "                B3B_INITIAL_LENGTHS + 4 * kind as u16,\n                1u32 << 24,\n            ); proof { r_source_units = r_source_units + r_child_units_1; } match r_child_1 { Ok(value) => value, Err(error) => return (Err(error), Ghost(r_source_units)) } };",
            "                B3B_INITIAL_LENGTHS + 4 * kind as u16,\n                1u32 << 23,\n            ); proof { r_source_units = r_source_units + r_child_units_1; } match r_child_1 { Ok(value) => value, Err(error) => return (Err(error), Ghost(r_source_units)) } };",
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
            "proof { source_units = source_units + 2; }\n        if count == 1 {",
            "proof { source_units = source_units + 2; }\n        if count == 1 && kind == 255 {",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "BitReadStatus::NeedInput => {\n                        proof { assert(source_units == context_bits_work_spec(source_read_work, phase, read.status, 0, 0)); }\n                        let result = (consumed, Some(ContextAdvanceStatus::NeedInput));",
            "BitReadStatus::NeedInput => {\n                        proof { assert(source_units == context_bits_work_spec(source_read_work, phase, read.status, 0, 0)); }\n                        let result = (consumed, None);",
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
            "crate::brotli_prefix::write_next_context_entry(\n                                    workspace, window_bytes, kind, active_len,\n                                    initialized, 0, num_trees)",
            "crate::brotli_prefix::write_next_context_entry(\n                                    workspace, window_bytes, kind, active_len,\n                                    initialized, 1, num_trees)",
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
            "                                workspace, window_bytes, 8); proof { r_source_units = r_source_units + r_child_units_13; } r_child_13 } {",
            "                                workspace, window_bytes, 7); proof { r_source_units = r_source_units + r_child_units_13; } r_child_13 } {",
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
            "                        window_bytes,\n                        crate::brotli_prefix::TreeRegion::TemporaryContext,\n                        0,",
            "                        window_bytes,\n                        crate::brotli_prefix::TreeRegion::Literal,\n                        0,",
        ),
        (
            "brotli-b3b-context-coverage-rejects-covered-map",
            "advance_context_coverage_phase",
            "if !covered {\n        return (Err(CompressedHeaderError::InvalidFormat(\n            CompressedFormatError::ContextMapCoverage,\n        )), Ghost(r_source_units));\n    }",
            "if covered {\n        return (Err(CompressedHeaderError::InvalidFormat(\n            CompressedFormatError::ContextMapCoverage,\n        )), Ghost(r_source_units));\n    }",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let checked_source = if name == "brotli-b3b-context-rle-suffix-is-one-bit-short" {
            // Retain every loop invariant, decreases clause and root guarantee
            // while checking this function's loops in their surrounding context.
            // The unchanged positive must pass with the same annotation first.
            let declaration = "fn advance_context_bits_phase(";
            assert_eq!(original.matches(declaration).count(), 1);
            let selected = original.replacen(declaration,
                "#[verifier::loop_isolation(false)]\nfn advance_context_bits_phase(", 1);
            fs::write(&path, &selected).unwrap();
            let positive = check_brotli_input_function(&verus, &temporary, function);
            let log = transcript(&positive);
            fs::write(project.join("evidence/positive-brotli-m1-context-rle-loop-context.log"), &log).unwrap();
            assert!(positive.status.success(), "unmodified same-setting root failed: {log}");
            selected
        } else {
            original.clone()
        };
        fs::write(&path, checked_source.replacen(old, new, 1)).unwrap();
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "        tree,\n        meta,\n    );",
            "        tree,\n        crate::brotli_prefix::TreeMetadata::unused(),\n    );",
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
            "        { let (r_child_3, Ghost(r_child_units_3)) = put_state_u16(self.workspace, self.window_bytes, B3B_ACTIVE_COMMAND_TREE, 0); proof { r_source_units = r_source_units + r_child_units_3; } match r_child_3 { Ok(value) => value, Err(error) => return (Err(error), Ghost(r_source_units)) } };",
            "        { let (r_child_3, Ghost(r_child_units_3)) = put_state_u16(self.workspace, self.window_bytes, B3B_ACTIVE_COMMAND_TREE, 1); proof { r_source_units = r_source_units + r_child_units_3; } match r_child_3 { Ok(value) => value, Err(error) => return (Err(error), Ghost(r_source_units)) } };",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        "CompressedMetaBlockDecoder::step_with_receipt",
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
            "CompressedMetaBlockDecoder::step_with_receipt",
            "                    return (self.repeat_terminal_failure(error), Ghost(r_w1_step_source_units));",
            "                    if input.len() == 1 {\n                        return (CompressedHeaderStep { consumed: input.len(), status: CompressedHeaderStatus::Failed(error) }, Ghost(r_w1_step_source_units));\n                    } else {\n                        return (CompressedHeaderStep { consumed: input.len(), status: CompressedHeaderStatus::Failed(error) }, Ghost(r_w1_step_source_units));\n                    }",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "                                    distance_types * 4,",
            "                                    distance_types * 3,",
        ),
        (
            "brotli-b3b-serialized-tree-skips-builder-reset",
            "start_serialized_tree",
            "put_state_u16(workspace, window_bytes, B3B_BUILDER_INITIALIZED, 0)",
            "(Ok(()), Ghost(0nat))",
        ),
        (
            "brotli-b3b-context-tree-starts-in-literal-region",
            "advance_context_bits_phase",
            "                                    crate::brotli_prefix::TreeRegion::TemporaryContext,",
            "                                    crate::brotli_prefix::TreeRegion::Literal,",
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
            "BitReadStatus::Truncated => {\n                        // The B3c owner performs its already-reserved terminal action.\n                        proof { assert(source_units + 4 + 1 == context_bits_work_spec(source_read_work, phase, read.status, 0, 0)); }\n                        let result = (consumed, Some(ContextAdvanceStatus::Failed(CompressedHeaderError::Truncated)));",
            "BitReadStatus::Truncated => {\n                        // The B3c owner performs its already-reserved terminal action.\n                        proof { assert(source_units + 4 + 1 == context_bits_work_spec(source_read_work, phase, read.status, 0, 0)); }\n                        let result = (consumed, Some(ContextAdvanceStatus::NeedInput));",
        ),
        (
            "brotli-b3b-tree-field-truncation-needs-input",
            "CodeDescriptionDecoder::advance_field",
            "return (CodeDescriptionStep {\n                    consumed: read.consumed,\n                    status: CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated),\n                }, Ghost(source_reads));",
            "return (CodeDescriptionStep {\n                    consumed: read.consumed,\n                    status: CodeDescriptionStatus::NeedInput,\n                }, Ghost(source_reads));",
        ),
    ] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = if name == "brotli-b3b-tree-field-truncation-needs-input" {
            // The instrumented positive and negative copies use the same checker effort.
            // Production advance_field retains its original allowance of 500.
            let declaration = "    #[verifier::rlimit(500)]\n    #[verifier::spinoff_prover]\n    fn advance_field(";
            let checked_declaration = "    #[verifier::rlimit(1000)]\n    #[verifier::spinoff_prover]\n    fn advance_field(";
            assert_eq!(original.matches(declaration).count(), 1, "unique selected field annotation");
            let checked_original = original.replacen(declaration, checked_declaration, 1);
            assert_eq!(old.matches("status: ").count(), 1, "unique healthy returned status");
            assert_eq!(new.matches("status: ").count(), 1, "unique faulty returned status");
            let healthy_status = old.split_once("status: ").unwrap().1.split_once(",\n").unwrap().0;
            let faulty_status = new.split_once("status: ").unwrap().1.split_once(",\n").unwrap().0;
            let expected_status = "CodeDescriptionStatus::Failed(CodeDescriptionError::Truncated)";
            assert_eq!(healthy_status, expected_status);
            assert_eq!(faulty_status, "CodeDescriptionStatus::NeedInput");
            let healthy_site = format!("proof {{\n                    assert(if matches!(\n                        {healthy_status},\n                        {expected_status}\n                    ) {{ true }} else {{ false }}) by (compute_only);\n                }}\n                {old}");
            let faulty_site = format!("proof {{\n                    assert(if matches!(\n                        {faulty_status},\n                        {expected_status}\n                    ) {{ true }} else {{ false }}) by (compute_only);\n                }}\n                {new}");
            fs::write(&path, checked_original.replacen(old, &healthy_site, 1)).unwrap();
            let positive = check_brotli_input_function(&verus, &temporary, function);
            assert!(positive.status.success(), "unmodified same-setting field root failed: {}", transcript(&positive));
            checked_original.replacen(old, &faulty_site, 1)
        } else {
            original.replacen(old, new, 1)
        };
        fs::write(&path, mutated).unwrap();
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
                || log.contains("assertion failed")
                || (name == "brotli-b3b-tree-field-truncation-needs-input"
                    && log.contains("error: expression simplifies to false")
                    && log.contains("by (compute_only)")),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
            "    workspace[at] = value as u8;\n    proof { source_units = source_units + 1; }\n    workspace[at + 1] = (value >> 8) as u8;\n    proof { source_units = source_units + 1; }\n    proof {",
            "    workspace[at] = value as u8;\n    proof { source_units = source_units + 1; }\n    workspace[at + 1] = value  as u8;\n    proof { source_units = source_units + 1; }\n    proof {",
        ),
        (
            "brotli-b3b-tag-accepts-first-invalid-value",
            "write_b3b_state_tag",
            "    let ghost source_units: nat = 0;\n    if value >= variants {\n        return (Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol), Ghost(source_units));",
            "    let ghost source_units: nat = 0;\n    if value > variants {\n        return (Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol), Ghost(source_units));",
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_twenty_eight_b3c_layout_state_resource_and_output_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-canaries-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    fs::create_dir_all(project.join("evidence")).unwrap();

    let check_core = |function: &str| {
        // Use the same allowance on each selected positive/negative pair.
        // Production source and its original allowances remain unchanged.
        let step_source = if function == "BrotliDecoder::step" {
            let path = temporary.join("src/brotli.rs");
            let source = fs::read_to_string(&path).unwrap();
            let declaration = "    #[verifier::rlimit(60)]\n    pub fn step(";
            let checked = "    #[verifier::rlimit(300)]\n    pub fn step(";
            assert_eq!(source.matches(declaration).count(), 1, "unique temporary step allowance");
            fs::write(&path, source.replacen(declaration, checked, 1)).unwrap();
            Some(source)
        } else {
            None
        };
        let output = Command::new(&verus)
            .arg(temporary.join("src/lib.rs"))
            .args([
                "--crate-type", "lib", "--verify-only-module", "brotli",
                "--verify-function", function, "--no-cheating", "--num-threads", "1",
                "--triggers-mode", "silent", "--no-auto-recommends-check", "--rlimit",
                if function == "BrotliDecoder::emit_byte" || function == "BrotliDecoder::step" {
                    "300"
                } else {
                    "60"
                },
            ])
            .current_dir(&temporary)
            .output()
            .expect("run selected pinned Verus core root");
        if let Some(source) = step_source {
            fs::write(temporary.join("src/brotli.rs"), source).unwrap();
        }
        output
    };

    for (module, function) in [
        ("input", "b3c_layout_is_exact"),
        ("input", "initialize_serialized_b3c"),
        ("input", "reject_permanent_single_type_switch"),
        ("input", "distance_lut_value"),
        ("input", "validate_zero_padding"),
        ("input", "validate_dictionary_staging_length"),
        ("input", "validate_initialized_dictionary_index"),
        ("input", "body_decrement_block_remaining"),
        ("brotli", "selected_literal_context"),
        ("brotli", "command_copy_length_context"),
        ("brotli", "BrotliDecoder::commit_eof_if_complete"),
        ("brotli", "phase_after_completed_insert"),
        ("brotli", "next_recent_cursor"),
        ("brotli", "copy_setup_phase"),
        ("brotli", "overlap_source_position"),
        ("brotli", "BrotliDecoder::consume_metadata_byte"),
        ("brotli", "BrotliDecoder::emit_uncompressed_byte"),
        ("brotli", "output_block_reason"),
        ("brotli", "BrotliDecoder::reset"),
        ("brotli", "BrotliDecoder::step"),
        ("data", "distance_index_delta"),
        ("data", "distance_value_delta"),
        ("data", "validate_dictionary_transform_shape"),
        ("data", "zero_length_dictionary_transform_plan"),
        ("brotli", "BrotliDecoder::fail"),
        ("brotli", "BrotliDecoder::emit_byte"),
    ] {
        let positive = match module {
            "input" => check_brotli_input_function(&verus, &temporary, function),
            "brotli" => check_core(function),
            "data" => check_brotli_data_function(&verus, &temporary, function),
            _ => unreachable!(),
        };
        assert!(
            positive.status.success(),
            "unmodified selected root failed: {}",
            transcript(&positive),
        );
    }

    for (name, module, file, function, old, new) in [
        (
            "brotli-b3c-region-boundary-shifts",
            "input",
            "brotli_input.rs",
            "b3c_layout_is_exact",
            "pub(crate) const B3C_DISTANCE_BITS_OFFSET: u32 = 1_163_660;",
            "pub(crate) const B3C_DISTANCE_BITS_OFFSET: u32 = 1_163_661;",
        ),
        (
            "brotli-b3c-initial-recent-distance-is-wrong",
            "input",
            "brotli_input.rs",
            "initialize_serialized_b3c",
            "if i == B3C_RECENT_DISTANCES as usize { 16 }",
            "if i == B3C_RECENT_DISTANCES as usize { 15 }",
        ),
        (
            "brotli-b3c-terminal-escrow-marker-is-wrong",
            "input",
            "brotli_input.rs",
            "initialize_serialized_b3c",
            "else if i == B3C_TERMINAL_ESCROW_MARKER as usize { 4 }",
            "else if i == B3C_TERMINAL_ESCROW_MARKER as usize { 3 }",
        ),
        (
            "brotli-b3c-distance-lut-offset-is-wrong",
            "input",
            "brotli_input.rs",
            "distance_lut_value",
            "let shifted_wide = shifted_grouped + direct as u64 + 1;",
            "let shifted_wide = shifted_grouped + direct as u64 + 2;",
        ),
        (
            "brotli-b3c-nonzero-padding-is-accepted",
            "input",
            "brotli_input.rs",
            "validate_zero_padding",
            "if value == 0 {\n        Ok(())",
            "if value != 0 {\n        Ok(())",
        ),
        (
            "brotli-b3c-dictionary-output-equal-to-meta-limit-is-rejected",
            "input",
            "brotli_input.rs",
            "validate_dictionary_staging_length",
            "    } else if output_length as u32 > meta_remaining {",
            "    } else if output_length as u32 >= meta_remaining {",
        ),
        (
            "brotli-b3c-dictionary-staging-reads-uninitialized-byte",
            "input",
            "brotli_input.rs",
            "validate_initialized_dictionary_index",
            "    if initialized > 37 || index >= initialized {",
            "    if initialized > 37 || index > initialized {",
        ),
        (
            "brotli-b3c-permanent-block-switch-failure-is-retryable",
            "input",
            "brotli_input.rs",
            "reject_permanent_single_type_switch",
            "        consumed: 0,\n        status: match result.outcome {\n            crate::brotli_block::B3bSwitchOutcome::Failed(error) => {\n                BodySwitchStatus::Failed(map_switch_failure(error))",
            "        consumed: 0,\n        status: match result.outcome {\n            crate::brotli_block::B3bSwitchOutcome::Failed(error) => {\n                BodySwitchStatus::NeedInput",
        ),
        (
            "brotli-b3c-command-remaining-does-not-decrement",
            "input",
            "brotli_input.rs",
            "body_decrement_block_remaining",
            "match put_state_u32(workspace, window_bytes, relative, remaining - 1).0 {",
            "match put_state_u32(workspace, window_bytes, relative, remaining).0 {",
        ),
        (
            "brotli-b3c-literal-context-previous-bytes-are-swapped",
            "brotli",
            "brotli.rs",
            "selected_literal_context",
            "crate::brotli_data::literal_context(mode, previous, second_previous)",
            "crate::brotli_data::literal_context(mode, second_previous, previous)",
        ),
        (
            "brotli-b3c-copy-length-context-is-wrong",
            "brotli",
            "brotli.rs",
            "command_copy_length_context",
            "    } else if copy_offset <= 4 {\n        (copy_offset - 2) as u8\n    } else {\n        3\n    }\n}",
            "    } else if copy_offset <= 4 {\n        (copy_offset - 1) as u8\n    } else {\n        3\n    }\n}",
        ),
        (
            "brotli-b3c-eof-is-committed-before-slice-consumption",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::commit_eof_if_complete",
            "    {\n        if end && consumed == input_len {",
            "    {\n        if end {",
        ),
        (
            "brotli-b3c-copy-runs-after-insert-reaches-meta-length",
            "brotli",
            "brotli.rs",
            "phase_after_completed_insert",
            "{\n    if meta_remaining == 0 { 15 } else { 8 }\n}",
            "{\n    if meta_remaining == 0 { 8 } else { 8 }\n}",
        ),
        (
            "brotli-b3c-recent-distance-ring-does-not-advance",
            "brotli",
            "brotli.rs",
            "next_recent_cursor",
            "    if cursor == 3 { 0 } else { cursor + 1 }",
            "    cursor",
        ),
        (
            "brotli-b3c-beyond-history-distance-is-treated-as-lz77",
            "brotli",
            "brotli.rs",
            "copy_setup_phase",
            "    if distance <= history { 12 } else { 13 }",
            "    12",
        ),
        (
            "brotli-b3c-overlap-copy-uses-wrong-source",
            "brotli",
            "brotli.rs",
            "overlap_source_position",
            "        position - distance",
            "        position - distance + 1",
        ),
        (
            "brotli-b3c-metadata-changes-history",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::consume_metadata_byte",
            "        let result = crate::brotli_input::write_b3c_state_u32(\n            self.workspace,\n            self.window_bytes(),\n            crate::brotli_input::B3C_META_REMAINING,\n            remaining - 1,",
            "        let result = crate::brotli_input::write_b3c_state_u32(\n            self.workspace,\n            self.window_bytes(),\n            crate::brotli_input::B3C_HISTORY_LENGTH,\n            remaining - 1,",
        ),
        (
            "brotli-b3c-uncompressed-byte-does-not-debit-input",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::emit_uncompressed_byte",
            "self.emit_byte(byte, output, produced, true)",
            "self.emit_byte(byte, output, produced, false)",
        ),
        (
            "brotli-b3c-need-output-masks-resource-limit",
            "brotli",
            "brotli.rs",
            "output_block_reason",
            "    if output_remaining == 0 || work_remaining < B3C_EMISSION_WRITE_WORK {\n        1\n    } else if !has_output_slot {\n        2",
            "    if !has_output_slot {\n        2\n    } else if output_remaining == 0 || work_remaining < B3C_EMISSION_WRITE_WORK {\n        1",
        ),
        (
            "brotli-b3c-reset-replenishes-work",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::reset",
            "        let window_bytes = 1u32 << self.budget.limits.max_window_bits;",
            "        self.budget.work_remaining = self.budget.limits.max_work;\n        let window_bytes = 1u32 << self.budget.limits.max_window_bits;",
        ),
        (
            "brotli-b3c-terminal-retry-debits-a-call",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::step",
            "        if let Some(step) = self.terminal_step(phase) {\n            proof {",
            "        if let Some(step) = self.terminal_step(phase) {\n            let _ = self.budget.charge_call();\n            proof {",
        ),
        (
            "brotli-b3c-recent-distance-index-is-wrong",
            "data",
            "brotli_data.rs",
            "distance_index_delta",
            "0 => 3, 1 => 2, 2 => 1, 3 => 0,",
            "0 => 2, 1 => 2, 2 => 1, 3 => 0,",
        ),
        (
            "brotli-b3c-recent-distance-signed-delta-is-wrong",
            "data",
            "brotli_data.rs",
            "distance_value_delta",
            "4 | 10 => -1,",
            "4 | 10 => 1,",
        ),
        (
            "brotli-b3c-dictionary-length-guard-is-weakened",
            "data",
            "brotli_data.rs",
            "validate_dictionary_transform_shape",
            "    if length < 4 || length > 24 {",
            "    if length < 3 || length > 24 {",
        ),
        (
            "brotli-b3c-valid-zero-length-transform-is-rejected",
            "data",
            "brotli_data.rs",
            "zero_length_dictionary_transform_plan",
            "    DictionaryTransformPlan {\n        prefix_at: 216,\n        prefix_len: 0,\n        body_start: 0,\n        body_len: 0,",
            "    DictionaryTransformPlan {\n        prefix_at: 216,\n        prefix_len: 0,\n        body_start: 0,\n        body_len: 1,",
        ),
        (
            "brotli-b3c-failure-is-stored-as-finished",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::fail",
            "crate::brotli_input::B3C_STREAM_PHASE,\n            9,",
            "crate::brotli_input::B3C_STREAM_PHASE,\n            8,",
        ),
        (
            "brotli-b3c-byte-emission-undercharges-work",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::emit_byte",
            "assert!(self.budget.charge_work(B3C_EMISSION_WRITE_WORK));",
            "assert!(self.budget.charge_work(B3C_EMISSION_WRITE_WORK - 1));",
        ),
        (
            "brotli-b3c-byte-emission-publishes-wrong-value",
            "brotli",
            "brotli.rs",
            "BrotliDecoder::emit_byte",
            "output[produced] = byte;",
            "output[produced] = byte.wrapping_add(1);",
        ),
    ] {
        let source_path = project.join("src").join(file);
        let temporary_path = temporary.join("src").join(file);
        let original = fs::read_to_string(&source_path).unwrap();
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}",
        );
        fs::write(&temporary_path, original.replacen(old, new, 1)).unwrap();
        let result = match module {
            "input" => check_brotli_input_function(&verus, &temporary, function),
            "brotli" => check_core(function),
            "data" => check_brotli_data_function(&verus, &temporary, function),
            _ => unreachable!(),
        };
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
            "expected a proof rejection, not a tooling error: {log}",
        );
        println!("REJECTED {name}: deliberately wrong implementation, unchanged specification");
        fs::write(&temporary_path, original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_b3c_exact_symbol_work_undercharge() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-symbol-work-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
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
        transcript(&positive),
    );

    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    let old = "        proof { exact_work = (exact_work + 1) as u64; }\n        let read = queue.read_bits";
    let new = "        proof { exact_work = exact_work; }\n        let read = queue.read_bits";
    assert_eq!(original.matches(old).count(), 1, "unique mutation anchor");
    fs::write(&path, original.replacen(old, new, 1)).unwrap();
    let result = check_brotli_input_function(&verus, &temporary, function);
    let log = transcript(&result);
    fs::create_dir_all(project.join("evidence")).unwrap();
    fs::write(
        project.join("evidence/canary-brotli-b3c-symbol-work-undercharge.log"),
        &log,
    )
    .unwrap();
    assert!(
        !result.status.success(),
        "prover accepted symbol-work undercharge"
    );
    assert!(
        log.contains("invariant not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("postcondition not satisfied")
            || log.contains("assertion failed"),
        "expected a proof rejection, not a tooling error: {log}",
    );
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_b3c_serialized_symbol_write_undercharge() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-symbol-write-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    let function = "completed_body_symbol_work";
    let positive = check_brotli_input_function(&verus, &temporary, function);
    assert!(
        positive.status.success(),
        "unmodified selected root failed: {}",
        transcript(&positive),
    );

    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    let old = "    const SERIALIZED_WRITE_WORK: u64 = 10 + 5;";
    let new = "    const SERIALIZED_WRITE_WORK: u64 = 10 + 4;";
    assert_eq!(original.matches(old).count(), 1, "unique mutation anchor");
    fs::write(&path, original.replacen(old, new, 1)).unwrap();
    let result = check_brotli_input_function(&verus, &temporary, function);
    let log = transcript(&result);
    fs::create_dir_all(project.join("evidence")).unwrap();
    fs::write(
        project.join("evidence/canary-brotli-b3c-symbol-write-undercharge.log"),
        &log,
    )
    .unwrap();
    assert!(
        !result.status.success(),
        "prover accepted serialized symbol-write undercharge",
    );
    assert!(
        log.contains("postcondition not satisfied") || log.contains("assertion failed"),
        "expected a proof rejection, not a tooling error: {log}",
    );
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_five_b3c_block_count_metering_undercharges() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-block-count-metering-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }

    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-b3c-block-count-planning-bit-undercharge",
            "plan_bit_read",
            "    let work = consumed as u64 + if complete { width as u64 } else { 0 };",
            "    let work = consumed as u64;",
        ),
        (
            "brotli-b3c-block-count-base-write-undercharge",
            "block_count_base_execution_work",
            "{\n    read_work + 10 + 2 + 1\n}",
            "{\n    read_work + 10 + 2\n}",
        ),
        (
            "brotli-b3c-block-count-terminal-write-undercharge",
            "block_count_truncated_execution_work",
            "{\n    block_count_base_execution_work(read_work) + 4 + 1\n}",
            "{\n    block_count_base_execution_work(read_work) + 4\n}",
        ),
        (
            "brotli-b3c-block-count-single-value-undercharge",
            "block_count_value_execution_work",
            "    if raw == 0 {\n        base + 7 + 1",
            "    if raw == 0 {\n        base + 7",
        ),
        (
            "brotli-b3c-block-count-tree-start-undercharge",
            "block_count_value_execution_work",
            "        base + 2 + 77 + 1 + 1",
            "        base + 2 + 75 + 1 + 1",
        ),
    ] {
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::create_dir_all(project.join("evidence")).unwrap();
        fs::write(
            project.join("evidence").join(format!("canary-{name}.log")),
            &log,
        )
        .unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}",
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_three_b3c_distance_metering_undercharges() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-distance-metering-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }

    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-b3c-distance-queue-write-undercharge",
            "distance_base_execution_work",
            "{\n    read_work + 10 + 1\n}",
            "{\n    read_work + 9 + 1\n}",
        ),
        (
            "brotli-b3c-distance-terminal-undercharge",
            "distance_truncated_execution_work",
            "{\n    distance_base_execution_work(read_work) + 4 + 1\n}",
            "{\n    distance_base_execution_work(read_work) + 4\n}",
        ),
        (
            "brotli-b3c-distance-value-undercharge",
            "distance_value_execution_work",
            "{\n    distance_base_execution_work(read_work) + 1 + 2 + 2 + 1 + 1\n}",
            "{\n    distance_base_execution_work(read_work) + 1 + 2 + 2 + 1\n}",
        ),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected mutation function exists");
        let end = start
            + original[start..]
                .find("\n}\n")
                .expect("selected mutation function ends")
            + 3;
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..],
        );
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::create_dir_all(project.join("evidence")).unwrap();
        fs::write(
            project.join("evidence").join(format!("canary-{name}.log")),
            &log,
        )
        .unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}",
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_b3c_context_mode_metering_undercharges() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-context-mode-metering-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }

    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-b3c-context-mode-complete-undercharge",
            "context_mode_complete_execution_work",
            "{\n    serialized_map_start_work() + 1 + 1\n}",
            "{\n    13 + 1 + 2\n}",
        ),
        (
            "brotli-b3c-context-mode-queue-undercharge",
            "context_mode_base_execution_work",
            "fn context_mode_base_execution_work(read_work: u64) -> (r: u64)\n    requires read_work <= 63,\n    ensures r == read_work + 10 + 1,\n{\n    read_work + 10 + 1\n}",
            "fn context_mode_base_execution_work(read_work: u64) -> (r: u64)\n    requires read_work <= 63,\n    ensures r == read_work + 10 + 1,\n{\n    read_work + 9 + 1\n}",
        ),
        (
            "brotli-b3c-context-mode-terminal-undercharge",
            "context_mode_truncated_execution_work",
            "{\n    context_mode_base_execution_work(read_work) + 4 + 1\n}",
            "{\n    context_mode_base_execution_work(read_work) + 4\n}",
        ),
        (
            "brotli-b3c-context-mode-value-undercharge",
            "context_mode_value_execution_work",
            "{\n    context_mode_base_execution_work(read_work) + 1 + 2 + 1\n}",
            "{\n    context_mode_base_execution_work(read_work) + 1 + 2\n}",
        ),
    ] {
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::create_dir_all(project.join("evidence")).unwrap();
        fs::write(
            project.join("evidence").join(format!("canary-{name}.log")),
            &log,
        )
        .unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}",
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_b3c_initial_suffix_metering_undercharges() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-initial-suffix-metering-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }

    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-b3c-initial-suffix-planning-undercharge",
            "initial_suffix_planning_total",
            "{\n    read_work + 1\n}",
            "{\n    read_work\n}",
        ),
        (
            "brotli-b3c-initial-suffix-queue-undercharge",
            "initial_suffix_base_execution_work",
            "{\n    read_work + 1 + 10 + 1\n}",
            "{\n    read_work + 1 + 9 + 1\n}",
        ),
        (
            "brotli-b3c-initial-suffix-terminal-undercharge",
            "initial_suffix_truncated_execution_work",
            "{\n    initial_suffix_base_execution_work(read_work) + 4 + 1\n}",
            "{\n    initial_suffix_base_execution_work(read_work) + 4\n}",
        ),
        (
            "brotli-b3c-initial-suffix-value-undercharge",
            "initial_suffix_value_execution_work",
            "{\n    initial_suffix_base_execution_work(read_work) + 2 + 4 + 1 + 1 + 1\n}",
            "{\n    initial_suffix_base_execution_work(read_work) + 4 + 1 + 1\n}",
        ),
    ] {
        assert_eq!(
            original.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::create_dir_all(project.join("evidence")).unwrap();
        fs::write(
            project.join("evidence").join(format!("canary-{name}.log")),
            &log,
        )
        .unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}",
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_five_b3c_tree_formula_undercharges() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-tree-metering-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.path().extension().is_some_and(|ext| ext == "rs") {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    // These controls bind the arithmetic contracts only. Full planner/action
    // refinement and source-action coverage remain separate M1 obligations.
    for (name, function, old, new) in [
        (
            "brotli-b3c-simple-install-formula-undercharge",
            "simple_tree_install_work",
            "if selector == 0 { 7 } else {",
            "if selector == 0 { 6 } else {",
        ),
        (
            "brotli-b3c-canonical-install-formula-undercharge",
            "canonical_tree_install_work",
            "    36 * symbols as u64 + 6 * nonzero as u64 + nonzero_index_sum + 1_564 + 4 + 1",
            "    36 * symbols as u64 + 6 * nonzero as u64 + nonzero_index_sum + 1_563 + 4 + 1",
        ),
        (
            "brotli-b3c-repeat-serialization-formula-undercharge",
            "code_description_payload_writes",
            "        CodeDescriptionPhase::ComplexRepeat { .. } => 35,",
            "        CodeDescriptionPhase::ComplexRepeat { .. } => 34,",
        ),
        (
            "brotli-b3c-initial-symbol-formula-undercharge",
            "initial_symbol_execution_work",
            "    let base = checked_planned_work_add(planning_work, 10 + 5 + 1)?;",
            "    let base = checked_planned_work_add(planning_work, 10 + 4 + 1)?;",
        ),
        (
            "brotli-b3c-serialization-base-formula-undercharge",
            "code_description_store_writes",
            "    4 + code_description_payload_writes(phase)",
            "    3 + code_description_payload_writes(phase)",
        ),
    ] {
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
            log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}",
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_thirteen_b3c_context_tree_count_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-context-count-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.path().extension().is_some_and(|ext| ext == "rs") {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-b3c-context-count-queue-write-undercharge","context_tree_count_execution_work","    let base = read_work + 10 + 2 + 1;","    let base = read_work + 9 + 2 + 1;"),
        ("brotli-b3c-context-count-var-write-undercharge","context_tree_count_execution_work","    let base = read_work + 10 + 2 + 1;","    let base = read_work + 10 + 1 + 1;"),
        ("brotli-b3c-context-count-map-cell-undercharge","context_tree_count_execution_work","            active_len as u64 + 4 + 1 + 1","            active_len as u64 / 2 + 4 + 1 + 1"),
        ("brotli-b3c-context-count-map-progress-undercharge","context_tree_count_execution_work","            active_len as u64 + 4 + 1 + 1","            active_len as u64 + 3 + 1 + 1"),
        ("brotli-b3c-context-count-tree-count-undercharge","context_tree_count_execution_work","        VarUint8Status::Value(raw) => base + 2 + if raw == 0 {","        VarUint8Status::Value(raw) => base + 1 + if raw == 0 {"),
        ("brotli-b3c-context-count-phase-transition-undercharge","context_tree_count_execution_work","            1 + 1\n        },","            1\n        },"),
        ("brotli-b3c-context-count-terminal-undercharge","context_tree_count_execution_work","        VarUint8Status::Truncated => base + 4 + 1,","        VarUint8Status::Truncated => base + 4,"),
        ("brotli-b3c-context-count-planning-debit-omitted","plan_context_tree_count_action","    if !budget.charge_work(read.work) {","    if !budget.charge_work(0) {"),
        ("brotli-b3c-context-count-execution-debit-undercharge","execute_planned_context_tree_count","    if !budget.charge_work(plan.execution_work) {","    if !budget.charge_work(plan.execution_work - 1) {"),
        ("brotli-b3c-context-count-execution-reserved-after-writes","execute_planned_context_tree_count","    if !budget.charge_work(plan.execution_work) {\n        return (Err(CompressedStep {\n            consumed: 0, status: CompressedStatus::Failed(CoreFailure::ResourceLimit),\n        }), Ghost(r_context_owner_source_units));\n    }","    "),
        ("brotli-b3c-context-count-wrong-decoded-count","advance_context_tree_count_phase","                        let num_trees = raw + 1;","                        let num_trees = raw + 2;"),
        ("brotli-b3c-context-count-wrong-zero-map-value","advance_context_tree_count_phase","                                    kind,\n                                    active_len,\n                                    initialized,\n                                    0,\n                                    1,","                                    kind,\n                                    active_len,\n                                    initialized,\n                                    1,\n                                    1,"),
        ("brotli-b3c-context-count-progress-writes-map-size","store_context_map_progress","    let (receipt_child_0, Ghost(receipt_child_units_0)) = put_state_u16(workspace, window_bytes, B3B_MAP_INDEX, progress);","    let (receipt_child_0, Ghost(receipt_child_units_0)) = put_state_u16(workspace, window_bytes, B3B_MAP_SIZE, progress);"),
    ] {
        let start = original.find(&format!("fn {function}("))
            .expect("selected function exists");
        let end = start + original[start..].find("\n}\n")
            .expect("selected function ends") + 3;
        let selected = &original[start..end];
        assert_eq!(selected.matches(old).count(), 1, "unique mutation anchor for {name}");
        let mut changed = selected.replacen(old, new, 1);
        if name == "brotli-b3c-context-count-execution-reserved-after-writes" {
            let call = "    let (used, status) = { let (r_child_result, Ghost(r_child_units)) = advance_context_tree_count_phase(\n        workspace, window_bytes, kind_tag, kind, active_len, input, end_of_input,\n    ); proof { r_context_owner_source_units = r_context_owner_source_units + r_child_units; } r_child_result };";
            assert_eq!(changed.matches(call).count(), 1, "unique execution site");
            changed = changed.replacen(call, &format!("{call}\n{old}"), 1);
        }
        let mutated = format!("{}{}{}", &original[..start], changed, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_seventeen_b3c_context_bits_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-context-bits-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.path().extension().is_some_and(|ext| ext == "rs") {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-b3c-context-bits-queue-undercharge", "context_bits_execution_work", "    let base = read_work + 10 + 1;", "    let base = read_work + 9 + 1;"),
        ("brotli-b3c-context-bits-start-undercharge", "context_bits_execution_work", "{ 76 + 1 + 1 + 1 + 1 }", "{ 75 + 1 + 1 + 1 + 1 }"),
        ("brotli-b3c-context-bits-prefix-undercharge", "context_bits_execution_work", "{ 76 + 1 + 1 + 1 + 1 }", "{ 76 + 1 + 0 + 1 + 1 }"),
        ("brotli-b3c-context-bits-map-undercharge", "context_bits_execution_work", "repeat as u64 + 4 + 1 + 1 + 1", "repeat as u64 / 2 + 4 + 1 + 1 + 1"),
        ("brotli-b3c-context-bits-progress-undercharge", "context_bits_execution_work", "repeat as u64 + 4 + 1 + 1 + 1", "repeat as u64 + 3 + 1 + 1 + 1"),
        ("brotli-b3c-context-bits-reset-undercharge", "context_bits_execution_work", "repeat as u64 + 4 + 1 + 1 + 1", "repeat as u64 + 4 + 0 + 1 + 1"),
        ("brotli-b3c-context-bits-phase-undercharge", "context_bits_execution_work", "} else { 1 + 1 }", "} else { 1 }"),
        ("brotli-b3c-context-bits-terminal-undercharge", "context_bits_execution_work", "BitReadStatus::Truncated => 4 + 1,", "BitReadStatus::Truncated => 4,"),
        ("brotli-b3c-context-bits-planning-debit-omitted", "plan_context_bits_action", "if !budget.charge_work(read.work)", "if !budget.charge_work(0)"),
        ("brotli-b3c-context-bits-execution-debit-undercharge", "execute_planned_context_bits", "if !budget.charge_work(plan.execution_work)", "if !budget.charge_work(plan.execution_work - 1)"),
        ("brotli-b3c-context-bits-execution-reserved-after-writes", "execute_planned_context_bits", "    if !budget.charge_work(plan.execution_work) {\n        return (Err(CompressedStep { consumed: 0, status: CompressedStatus::Failed(CoreFailure::ResourceLimit) }), Ghost(r_context_owner_source_units));\n    }", "    "),
        ("brotli-b3c-context-bits-wrong-prefix", "advance_context_bits_phase", "let max_run = value as u8 + 1;", "let max_run = value as u8 + 2;"),
        ("brotli-b3c-context-bits-wrong-zero", "advance_context_bits_phase", "initialized, 0, num_trees);", "initialized, 1, num_trees);"),
        ("brotli-b3c-context-bits-start-writes-unrelated-byte", "initialize_code_description_state", "B3B_PENDING_SPAN_LENGTH, 0)", "B3B_GROUP_KIND, 0)"),
        ("brotli-b3c-context-bits-overshoot-terminal-undercharge", "context_bits_execution_work", "if repeat > remaining as u32 { 4 + 1 }", "if repeat > remaining as u32 { 4 }"),
        ("brotli-b3c-context-bits-skips-overshoot-check", "advance_context_bits_phase", "if index as u32 + repeat > active_len as u32 {", "if false {"),
        ("brotli-b3c-context-bits-reads-wrong-width", "advance_context_bits_phase", "                let read = { let (r_child_0, Ghost(r_child_units_0)) = queue.read_bits(width, remaining, end_of_input); proof { r_source_units = r_source_units + r_child_units_0; } r_child_0 };", "                let read = { let (r_child_0, Ghost(r_child_units_0)) = queue.read_bits(width - 1 , remaining, end_of_input); proof { r_source_units = r_source_units + r_child_units_0; } r_child_0 };"),
    ] {
        let start = original.find(&format!("fn {function}("))
            .expect("selected function exists");
        let end = start + original[start..].find("\n}\n")
            .expect("selected function ends") + 3;
        let selected = &original[start..end];
        assert_eq!(selected.matches(old).count(), 1, "unique mutation anchor for {name}");
        let mut changed = selected.replacen(old, new, 1);
        if name == "brotli-b3c-context-bits-execution-reserved-after-writes" {
            let call = "    let (used, status) = { let (r_child_result, Ghost(r_child_units)) = advance_context_bits_phase(workspace, window_bytes, plan.phase,\n        kind_tag, kind, active_len, input, end_of_input); proof { r_context_owner_source_units = r_context_owner_source_units + r_child_units; } r_child_result };";
            assert_eq!(changed.matches(call).count(), 1, "unique execution site");
            changed = changed.replacen(call, &format!("{call}\n{old}"), 1);
        }
        if name == "brotli-b3c-context-bits-skips-overshoot-check" {
            // Restate the existing post-guard loop/write bound explicitly.
            // Check the hint with the original guard first; neither run changes
            // the function's admitted inputs or requires/ensures contracts.
            let add_bound = |source: &str, guard: &str| {
                let at = source.find(guard).expect("unique repeat guard");
                let begin = at + source[at..].find('{').unwrap();
                let mut depth = 0usize;
                let mut finish = None;
                for (offset, byte) in source.as_bytes()[begin..].iter().enumerate() {
                    if *byte == b'{' { depth += 1; }
                    else if *byte == b'}' {
                        depth -= 1;
                        if depth == 0 { finish = Some(begin + offset + 1); break; }
                    }
                }
                let finish = finish.expect("balanced repeat guard");
                let bound = "\n                            proof {\n                                assert(index as u32 + repeat <= active_len as u32) by (nonlinear_arith)\n                                    requires index as u32 + repeat <= active_len as u32;\n                            }\n";
                format!("{}{}{}", &source[..finish], bound, &source[finish..])
            };
            let positive = add_bound(selected, old);
            fs::write(&path, format!("{}{}{}", &original[..start], positive, &original[end..])).unwrap();
            let positive = check_brotli_input_function(&verus, &temporary, function);
            let positive_log = transcript(&positive);
            fs::write(project.join("evidence/positive-brotli-b3c-repeat-bound-obligation.log"), &positive_log).unwrap();
            assert!(positive.status.success(), "original guard with explicit existing bound failed: {positive_log}");
            changed = add_bound(&changed, new);
        }
        let mutated = format!("{}{}{}", &original[..start], changed, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_nested_reset_transition_undercharges() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-nested-reset-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-tree-reset-transition-undercharge",
            "serialized_tree_start_work",
            "{ 76 + 1 }",
            "{ 76 }",
        ),
        (
            "brotli-m1-var-reset-transition-undercharge",
            "serialized_map_start_work",
            "{ 14 + 1 + 1 }",
            "{ 14 + 1 }",
        ),
        (
            "brotli-m1-prefix-reset-transition-undercharge",
            "installed_prefix_reset_work",
            "{ 5 + 1 }",
            "{ 5 }",
        ),
        (
            "brotli-m1-group-tree-transition-undercharge",
            "group_tree_start_work",
            "{ serialized_tree_start_work() + 2 + 1 + 1 }",
            "{ serialized_tree_start_work() + 2 + 1 }",
        ),
        (
            "brotli-m1-group-reset-transition-undercharge",
            "tree_group_start_work",
            "{ 4 + 1 + group_tree_start_work() + 1 + 1 }",
            "{ 4 + group_tree_start_work() + 1 + 1 }",
        ),
        (
            "brotli-m1-ready-reset-transition-undercharge",
            "ready_switch_start_work",
            "{ 28 + 1 }",
            "{ 28 }",
        ),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected function exists");
        let end = start
            + original[start..]
                .find("\n\n")
                .expect("selected function ends");
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(
            project.join("evidence").join(format!("canary-{name}.log")),
            &log,
        )
        .unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_nine_m1_source_refinement_and_debit_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-source-refinement-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-code-field-wrong-width",
            "CodeDescriptionDecoder::advance_field",
            "self.queue.read_bits(width, input, end_of_input)",
            "self.queue.read_bits(width / 2, input, end_of_input)",
        ),
        (
            "brotli-m1-auxiliary-wrong-symbol",
            "decode_auxiliary_symbol",
            "                    return (Some(i as u8), Ghost(source_reads));",
            "                    return (Some(i as u8 + 1 ), Ghost(source_reads));",
        ),
        (
            "brotli-m1-complex-start-wrong-previous-length",
            "start_complex_symbol_progress",
            "prev_code_len: 8,",
            "prev_code_len: 7,",
        ),
        (
            "brotli-m1-var-integer-wrong-value",
            "advance_var_uint8",
            "let value = (1u16 << width) + field as u16;",
            "let value = (1u16 << width) + field as u16 + 1;",
        ),
        (
            "brotli-m1-body-metadata-read-not-charged",
            "advance_planned_body_symbol",
            "budget.charge_work(TREE_METADATA_WORK)",
            "budget.charge_work(0)",
        ),
        (
            "brotli-m1-body-execution-undercharge",
            "advance_planned_body_symbol",
            "budget.charge_work(completed_action_work)",
            "budget.charge_work(completed_action_work - 1)",
        ),
        (
            "brotli-m1-context-direct-wrong-value",
            "store_context_direct_symbol",
            "let value = symbol - max_run as u16;",
            "let value = symbol - max_run as u16 + 1;",
        ),
        (
            "brotli-m1-initial-symbol-execution-undercharge",
            "execute_planned_initial_symbol",
            "budget.charge_work(plan.execution_work)",
            "budget.charge_work(plan.execution_work - 1)",
        ),
        (
            "brotli-m1-context-symbol-execution-undercharge",
            "execute_planned_context_symbol",
            "budget.charge_work(plan.execution_work)",
            "budget.charge_work(plan.execution_work - 1)",
        ),
    ] {
        let scope = if function.starts_with("CodeDescriptionDecoder::") {
            original
                .find("impl CodeDescriptionDecoder {")
                .expect("decoder implementation exists")
        } else {
            0
        };
        let function_name = function.rsplit("::").next().unwrap();
        let start = scope
            + original[scope..]
                .find(&format!("fn {function_name}("))
                .expect("selected function exists");
        let end = start
            + original[start..]
                .find("\n}\n")
                .expect("selected function ends")
            + 3;
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        fs::write(&path, mutated).unwrap();
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
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_b3c_wrong_dictionary_source() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-dictionary-source-canary-{}",
        std::process::id(),
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
        "brotli.rs",
        "brotli_data.rs",
        "brotli_dictionary.rs",
        "composition_demo.rs",
    ] {
        fs::copy(
            project.join("src").join(name),
            temporary.join("src").join(name),
        )
        .unwrap();
    }
    let function = "copy_dictionary_slice";
    let positive = check_brotli_data_function_high(&verus, &temporary, function);
    assert!(
        positive.status.success(),
        "unmodified selected root failed: {}",
        transcript(&positive),
    );

    let path = temporary.join("src/brotli_data.rs");
    let original = fs::read_to_string(&path).unwrap();
    let old = "        output[output_start + i] = crate::brotli_dictionary::dictionary_byte(\n            source + body_start + i,\n        );";
    let new = "        output[output_start + i] = crate::brotli_dictionary::dictionary_byte(\n            source + body_start + i + 1,\n        );";
    assert_eq!(original.matches(old).count(), 1, "unique mutation anchor");
    fs::write(&path, original.replacen(old, new, 1)).unwrap();
    let result = check_brotli_data_function_high(&verus, &temporary, function);
    let log = transcript(&result);
    fs::create_dir_all(project.join("evidence")).unwrap();
    fs::write(
        project.join("evidence/canary-brotli-b3c-wrong-dictionary-source.log"),
        &log,
    )
    .unwrap();
    assert!(
        !result.status.success(),
        "prover accepted wrong dictionary source"
    );
    assert!(
        log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
        "expected a proof rejection, not a tooling error: {log}",
    );
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_fifteen_m1_saved_table_and_lookup_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-saved-table-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-aux-count-read-not-charged", "auxiliary_count_metered",
            "budget.charge_work(1)", "budget.charge_work(0)"),
        ("brotli-m1-aux-first-code-skips-last-length", "auxiliary_first_code_metered",
            "auxiliary_count_metered(lengths, width, 18, budget)",
            "auxiliary_count_metered(lengths, width, 17, budget)"),
        ("brotli-m1-aux-canonical-length-read-not-charged", "auxiliary_canonical_code_metered",
            "budget.charge_work(1)", "budget.charge_work(0)"),
        ("brotli-m1-aux-candidate-read-not-charged", "decode_auxiliary_symbol_metered",
            "budget.charge_work(1)", "budget.charge_work(0)"),
        ("brotli-m1-aux-singleton-skips-last-length", "auxiliary_singleton_metered",
            "while i < 18", "while i < 17"),
        ("brotli-m1-simple-pair-second-read-not-charged", "simple_symbol_pair_metered",
            "    proof { r_metered_source_reads = r_metered_source_reads + 1; }\n    if !budget.charge_work(1) { return (Err(CoreFailure::ResourceLimit), Ghost(r_metered_source_reads)); }\n    let b = symbols[right];",
            "    proof { r_metered_source_reads = r_metered_source_reads + 1; }\n    if !budget.charge_work(0) { return (Err(CoreFailure::ResourceLimit), Ghost(r_metered_source_reads)); }\n    let b = symbols[right];"),
        ("brotli-m1-simple-validation-skips-last-pair", "simple_distinct_validation_metered",
            "        let equal = { let (r_child_result, Ghost(r_child_units)) = simple_symbol_pair_metered(symbols, 2, 3, budget); proof { r_metered_source_reads = r_metered_source_reads + r_child_units; } match r_child_result { Ok(value) => value, Err(error) => return (Err(error), Ghost(r_metered_source_reads)) } };\n        assert(!equal);",
            ""),
        ("brotli-m1-field-planning-replay-not-charged", "plan_code_description_field",
            "budget.charge_work(replay_work)", "budget.charge_work(0)"),
        ("brotli-m1-saved-aux-load-not-charged", "plan_saved_aux_load",
            "budget.charge_work(1)", "budget.charge_work(0)"),
        ("brotli-m1-saved-aux-wrong-partial-count", "plan_saved_aux_load",
            "            return (Ok((i as u64 + 1, false)), Ghost(r_saved_forecast_source_reads));", "            return (Ok((18, false)), Ghost(r_saved_forecast_source_reads));"),
        ("brotli-m1-saved-aux-skips-last-copy", "read_aux_lengths",
            "while i < 18", "while i < 17"),
        ("brotli-m1-saved-aux-accepts-invalid-length", "read_aux_lengths",
            "if value > 5 {", "if false {"),
        ("brotli-m1-canonical-validation-read-not-charged", "plan_canonical_tree_install",
            "budget.charge_work(1)", "budget.charge_work(0)"),
        ("brotli-m1-canonical-accepts-invalid-length", "plan_canonical_tree_install",
            "            proof { k1_canonical_classification_agrees(lengths@, symbols as nat, planning_work as nat, false); }\n            return (Ok((planning_work, planning_work, false)), Ghost(source_visits));\n        }",
            "            proof { k1_canonical_classification_agrees(lengths@, symbols as nat, planning_work as nat, false); }\n            return (Ok((planning_work, planning_work, true)), Ghost(source_visits));\n        }"),
        ("brotli-m1-canonical-accepts-incomplete-space", "plan_canonical_tree_install",
            "if nonzero < 2 || space != 0 {", "if nonzero < 2 {"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        assert_eq!(selected.matches(old).count(), 1, "unique mutation anchor for {name}");
        let mutated = format!("{}{}{}", &original[..start], selected.replacen(old, new, 1), &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_m1_tree_action_bound_and_drain_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-tree-bound-canary-{}",
        std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-parser-restores-too-small-cap",
            "advance_serialized_tree",
            "while work < 5_696",
            "while work < 2_000",
        ),
        (
            "brotli-m1-planner-restores-too-small-cap",
            "plan_serialized_tree",
            "while iterations < 5_696",
            "while iterations < 2_000",
        ),
        (
            "brotli-m1-parser-skips-pending-span-drain",
            "advance_serialized_tree",
            "let step = if matches!(decoder.phase, CodeDescriptionPhase::ComplexPendingSpan { .. }) {",
            "let step = if false {",
        ),
        (
            "brotli-m1-planner-skips-pending-span-drain",
            "plan_serialized_tree",
            "if matches!(decoder.phase, CodeDescriptionPhase::ComplexPendingSpan { .. }) {",
            "if false {",
        ),
    ] {
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let mut selected = original[start..end].to_string();
        let (old, new) = if name == "brotli-m1-planner-restores-too-small-cap" {
            // Check the existing rank's adequacy for the executable cap before
            // mutation, including its concrete consequence at the admitted
            // Selector/704 startup witness. This is a certificate control;
            // it does not claim an actual 2000-action execution.
            let receipt = "    proof { assert(initial_rank < 5_696nat); }\n    proof { assert(if code_phase_rank(CodeDescriptionPhase::Selector, 704) < 5_696nat { true } else { false }) by (compute_only); }\n    while iterations < 5_696";
            assert_eq!(selected.matches("    while iterations < 5_696").count(), 1);
            selected = selected.replacen("    while iterations < 5_696", receipt, 1);
            fs::write(
                &path,
                format!("{}{}{}", &original[..start], selected, &original[end..]),
            )
            .unwrap();
            let positive = check_brotli_input_function(&verus, &temporary, function);
            fs::write(
                project.join("evidence/positive-brotli-m1-planner-cap-rank.log"),
                transcript(&positive),
            )
            .unwrap();
            assert!(
                positive.status.success(),
                "unmodified cap/rank obligation failed: {}",
                transcript(&positive)
            );
            let rank_receipt = "proof { assert(initial_rank < 5_696nat); }";
            let bad_rank_receipt = "proof { assert(initial_rank < 2_000nat); }";
            let concrete_receipt = "proof { assert(if code_phase_rank(CodeDescriptionPhase::Selector, 704) < 5_696nat { true } else { false }) by (compute_only); }";
            let bad_concrete_receipt = "proof { assert(if code_phase_rank(CodeDescriptionPhase::Selector, 704) < 2_000nat { true } else { false }) by (compute_only); }";
            assert_eq!(selected.matches(rank_receipt).count(), 1);
            assert_eq!(selected.matches(concrete_receipt).count(), 1);
            selected = selected.replacen(rank_receipt, bad_rank_receipt, 1);
            selected = selected.replacen(concrete_receipt, bad_concrete_receipt, 1);
            let preview = selected.replacen(old, new, 1);
            assert_eq!(preview.matches(bad_rank_receipt).count(), 1);
            assert_eq!(preview.matches(bad_concrete_receipt).count(), 1);
            assert_eq!(preview.matches("while iterations < 2_000").count(), 1);
            assert_eq!(preview.matches("            initial_rank <= 5_695,\n").count(), 1);
            (old, new)
        } else {
            (old, new)
        };
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        fs::write(
            &path,
            format!(
                "{}{}{}",
                &original[..start],
                selected.replacen(old, new, 1),
                &original[end..]
            ),
        )
        .unwrap();
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
                || log.contains("requires not satisfied")
                || log.contains("assertion failed")
                || log.contains("invariant not satisfied")
                || (name == "brotli-m1-planner-restores-too-small-cap"
                    && log.contains("error: expression simplifies to false")
                    && log.contains("by (compute_only)")),
            "expected semantic proof rejection: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_tree_plan_debit_and_frame_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-tree-refinement-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-tree-plan-omits-saved-load-planning", "plan_serialized_tree",
            "let mut planning_work = initial_planning_work + copy_len as u64;",
            "let mut planning_work = copy_len as u64;"),
        (
            "brotli-m1-block-tree-plan-omits-planning-debit",
            "plan_block_tree_action",
            "Ok(CompressedActionPlan {\n        planning_work: tree.planning_work,",
            "Ok(CompressedActionPlan {\n        planning_work: 0,",
        ),
        ("brotli-m1-group-tree-plan-omits-planning-debit", "plan_tree_group_action",
            "    Ok(CompressedActionPlan {\n        planning_work,\n        execution_work,\n        consumed: tree.consumed,\n        status,\n    })", "    Ok(CompressedActionPlan {\n        planning_work: 0,\n        execution_work,\n        consumed: tree.consumed,\n        status,\n    })"),
        ("brotli-m1-pending-span-writes-wrong-length", "drain_serialized_pending_span",
            "next_initialized,\n            length,\n        )",
            "next_initialized,\n            0,\n        )"),
        ("brotli-m1-descriptor-store-writes-unrelated-byte", "store_code_description_decoder",
            "B3B_PENDING_SPAN_LENGTH, 0)", "B3B_PENDING_SPAN_LENGTH + 1, 0)"),
        ("brotli-m1-inconsistent-span-mutates-decoder", "drain_serialized_pending_span",
            "        proof { assert(workspace@ == original); }\n        return (Err(CompressedHeaderError::InternalState), Ghost(source_span_writes));\n    }",
            "        proof { assert(workspace@ == original); }\n         decoder.phase = CodeDescriptionPhase::Failed(CodeDescriptionError::InvalidAlphabet); return (Err(CompressedHeaderError::InternalState), Ghost(source_span_writes));\n    }"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        assert_eq!(selected.matches(old).count(), 1, "unique mutation anchor for {name}");
        let mutated = format!("{}{}{}", &original[..start], selected.replacen(old, new, 1), &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_block_count_relation_and_debit_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-block-relation-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-block-count-prepass-omits-read-work", "block_count_planning_work",
            "Ok(read.work)", "Ok(0)"),
        ("brotli-m1-block-count-plan-loses-need-input", "plan_block_count_action",
            "VarUint8Status::NeedInput => Some(CompressedHeaderStatus::NeedInput),",
            "VarUint8Status::NeedInput => None,"),
        ("brotli-m1-block-count-plan-loses-consumption", "plan_block_count_action",
            "consumed: step.consumed,", "consumed: 0,"),
        ("brotli-m1-block-count-executor-omits-input-debit", "execute_fixed_compressed_plan",
            "budget.charge_input(used as u64)", "budget.charge_input(0)"),
        ("brotli-m1-block-count-limited-input-is-retryable", "execute_fixed_compressed_plan",
            "if input_was_limited { CompressedStatus::Failed(CoreFailure::ResourceLimit) }",
            "if input_was_limited && !matches!(phase, CompressedOuterPhase::BlockCount) { CompressedStatus::Failed(CoreFailure::ResourceLimit) }"),
        ("brotli-m1-block-count-value-writes-padding", "apply_block_count_value",
            "        let count = raw + 1;",
            "        match put_state_byte(self.workspace, self.window_bytes, 175, 255).0 { Ok(value) => value, Err(error) => return (Err(error), Ghost(r_source_units)), };\n    let count = raw + 1;"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start + original[start..].find(&closing).expect("selected function ends") + closing.len();
        let selected = &original[start..end];
        assert_eq!(selected.matches(old).count(), 1, "unique mutation anchor for {name}");
        let mutated = format!("{}{}{}", &original[..start], selected.replacen(old, new, 1), &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_distance_relation_and_frame_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-distance-relation-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-distance-prepass-omits-read-work",
            "distance_planning_work",
            "Ok(read.work)",
            "Ok(0)",
        ),
        (
            "brotli-m1-distance-plan-loses-need-input",
            "plan_distance_action",
            "Some(CompressedHeaderStatus::NeedInput),",
            "None,",
        ),
        (
            "brotli-m1-distance-plan-loses-consumption",
            "plan_distance_action",
            "consumed: read.consumed,",
            "consumed: 0,",
        ),
        (
            "brotli-m1-distance-plan-omits-value-writes",
            "plan_distance_action",
            "distance_value_execution_work(read_plan.work)",
            "distance_base_execution_work(read_plan.work)",
        ),
        (
            "brotli-m1-distance-action-writes-wrong-direct-field",
            "advance_distance_parameters_phase",
            "B3B_DIRECT_DISTANCE, direct)",
            "B3B_ALPHABET_LIMIT, direct)",
        ),
        (
            "brotli-m1-distance-action-flips-postfix",
            "advance_distance_parameters_phase",
            "B3B_DISTANCE_POSTFIX, postfix)",
            "B3B_DISTANCE_POSTFIX, postfix ^ 1)",
        ),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start
            + original[start..]
                .find(&closing)
                .expect("selected function ends")
            + closing.len();
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        fs::write(&path, mutated).unwrap();
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
                || log.contains("requires not satisfied")
                || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_bad_context_count_failure_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-context-count-failure-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    let positive = check_brotli_input_function(&verus, &temporary, "advance_planned_compressed_action");
    assert!(positive.status.success(), "unmodified selected root failed: {}", transcript(&positive));
    for (name, function, old, new) in [
        ("brotli-m1-context-bad-count-prepass-skips-terminal-plan", "context_mode_planning_work", "if literal_count == 0 || literal_count > 256 || initialized > literal_count {\n        return Ok(0);", "if literal_count == 0 || literal_count > 256 || initialized > literal_count {\n        return Err(CompressedHeaderError::InternalState);"),
        ("brotli-m1-context-bad-count-plan-omits-terminal-work", "plan_context_mode_action", "execution_work: 4 + 1,", "execution_work: 0,"),
        ("brotli-m1-context-bad-count-plan-loses-failure", "plan_context_mode_action", "status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState))", "status: None"),
        ("brotli-m1-context-bad-count-plan-consumes-input", "plan_context_mode_action", "consumed: 0, status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState))", "consumed: 1, status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState))"),
        ("brotli-m1-context-bad-count-executor-wrong-error", "execute_fixed_compressed_plan", "CompressedStatus::Failed(map_compressed_error(error))", "CompressedStatus::Failed(CoreFailure::Truncated)"),
        ("brotli-m1-context-bad-count-owner-skips-action", "advance_planned_compressed_action", "        match { let (r_child_result, Ghost(r_child_units)) = execute_fixed_compressed_plan(\n            workspace,\n            window_bytes,\n            budget,\n            CompressedOuterPhase::ContextModes,\n            &input[..initial_allowed],\n            end_of_input && initial_allowed == input.len(),\n            initial_allowed < input.len(),\n            plan,\n        ); proof { r_header_action_source_units = r_header_action_source_units + r_child_units; } r_child_result } {\n            Ok(used) => already_consumed = used,\n            Err(step) => return (Err(step), Ghost(r_header_action_source_units)),\n        }", "        if window_bytes == 1024 && budget.work_remaining == 5 {\n            return (Err::<usize, CompressedStep>(CompressedStep { consumed: 0,\n                status: CompressedStatus::Failed(core_state_failure()) }), Ghost(r_header_action_source_units));\n        } else {\n            return (Err::<usize, CompressedStep>(CompressedStep { consumed: 0,\n                status: CompressedStatus::Failed(core_state_failure()) }), Ghost(r_header_action_source_units));\n        }"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start + original[start..].find(&closing).expect("selected function ends") + closing.len();
        let selected = &original[start..end];
        assert_eq!(selected.matches(old).count(), 1, "unique mutation anchor for {name}");
        let mutated = format!("{}{}{}", &original[..start], selected.replacen(old, new, 1), &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_eight_m1_context_mode_relation_and_frame_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-context-mode-relation-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-context-mode-prepass-omits-read-work",
            "context_mode_planning_work",
            "Ok(read.work)",
            "Ok(0)",
        ),
        (
            "brotli-m1-context-mode-plan-loses-need-input",
            "plan_context_mode_action",
            "Some(CompressedHeaderStatus::NeedInput),",
            "None,",
        ),
        (
            "brotli-m1-context-mode-plan-loses-consumption",
            "plan_context_mode_action",
            "consumed: read.consumed,",
            "consumed: 0,",
        ),
        (
            "brotli-m1-context-mode-plan-omits-value-writes",
            "plan_context_mode_action",
            "context_mode_value_execution_work(read_plan.work)",
            "context_mode_base_execution_work(read_plan.work)",
        ),
        (
            "brotli-m1-context-mode-action-writes-wrong-value",
            "advance_context_modes_phase",
            "                                    value as u8,
                                )",
            "                                    (value as u8) ^ 1,
                                )",
        ),
        (
            "brotli-m1-context-mode-action-loses-initialized-count",
            "advance_context_modes_phase",
            "B3B_MODES_INITIALIZED, next)",
            "B3B_MODES_INITIALIZED, initialized)",
        ),
        ("brotli-m1-context-mode-executor-omits-input-debit", "execute_fixed_compressed_plan", "budget.charge_input(used as u64)", "budget.charge_input(if phase == CompressedOuterPhase::ContextModes { 0 } else { used as u64 })"),
        ("brotli-m1-context-mode-limited-input-is-retryable", "execute_fixed_compressed_plan", "if input_was_limited { CompressedStatus::Failed(CoreFailure::ResourceLimit) }", "if input_was_limited && phase != CompressedOuterPhase::ContextModes { CompressedStatus::Failed(CoreFailure::ResourceLimit) }"),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start
            + original[start..]
                .find(&closing)
                .expect("selected function ends")
            + closing.len();
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        fs::write(&path, mutated).unwrap();
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
                || log.contains("requires not satisfied")
                || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_two_k2_context_mode_success_guarantee_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k2-writer-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_prefix.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-k2-writer-rejects-last-valid-index",
            "write_next_context_mode",
            "initialized >= LITERAL_CONTEXT_MODES_BYTES as u16",
            "initialized >= LITERAL_CONTEXT_MODES_BYTES as u16 - 1",
        ),
        (
            "brotli-k2-writer-rejects-valid-window",
            "write_next_context_mode",
            "if window_bytes > 16_777_216",
            "if window_bytes >= 16_777_216",
        ),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected function exists");
        let indent = original[..start]
            .rsplit('\n')
            .next()
            .unwrap()
            .chars()
            .take_while(|c| c.is_whitespace())
            .count();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start
            + original[start..]
                .find(&closing)
                .expect("selected function ends")
            + closing.len();
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        fs::write(&path, mutated).unwrap();
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
                || log.contains("requires not satisfied")
                || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_five_k1_k3_success_and_preservation_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k1-k3-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_prefix.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-k1-installer-rejects-valid-two-symbol-tree",
            "install_builder_canonical_tree",
            "    let mut symbol: u16 = 0;\n    let mut space: u32 = CODE_SPACE;",
            "    if symbols == 2 { return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_validation_reads + source_count_reads + source_count_writes + source_chain_initialization_writes + source_chain_reads + source_chain_writes + source_next_reads + source_next_writes + source_record_reads + source_record_writes)); }\n    let mut symbol: u16 = 0;\n    let mut space: u32 = CODE_SPACE;",
        ),
        (
            "brotli-k1-invalid-length-changes-metadata",
            "install_builder_canonical_tree",
            "            proof { assert(source_validation_reads == symbol as nat + 1); reveal(valid_builder_lengths); assert(!valid_builder_lengths(lengths)); }\n            return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_validation_reads + source_count_reads + source_count_writes + source_chain_initialization_writes + source_chain_reads + source_chain_writes + source_next_reads + source_next_writes + source_record_reads + source_record_writes));\n        }",
            "            proof { assert(source_validation_reads == symbol as nat + 1); reveal(valid_builder_lengths); assert(!valid_builder_lengths(lengths)); }\n             meta.symbols = 0; return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_validation_reads + source_count_reads + source_count_writes + source_chain_initialization_writes + source_chain_reads + source_chain_writes + source_next_reads + source_next_writes + source_record_reads + source_record_writes));\n        }",
        ),
        (
            "brotli-k1-invalid-length-changes-builder",
            "install_builder_canonical_tree",
            "            proof { assert(source_validation_reads == symbol as nat + 1); reveal(valid_builder_lengths); assert(!valid_builder_lengths(lengths)); }\n            return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_validation_reads + source_count_reads + source_count_writes + source_chain_initialization_writes + source_chain_reads + source_chain_writes + source_next_reads + source_next_writes + source_record_reads + source_record_writes));\n        }",
            "            proof { assert(source_validation_reads == symbol as nat + 1); reveal(valid_builder_lengths); assert(!valid_builder_lengths(lengths)); }\n             workspace[window_bytes as usize + BUILDER_CODE_LENGTHS_OFFSET as usize] = 0; return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_validation_reads + source_count_reads + source_count_writes + source_chain_initialization_writes + source_chain_reads + source_chain_writes + source_next_reads + source_next_writes + source_record_reads + source_record_writes));\n        }",
        ),
        (
            "brotli-k3-rejects-valid-symbol-and-suffix",
            "decode_block_length",
            "        match offset.checked_add(suffix) {",
            "        if symbol == 0 && suffix == 0 { return (Err(PrefixError::InvalidBlockLengthSuffix), Ghost(source_units)); }\n    match offset.checked_add(suffix) {",
        ),
        (
            "brotli-k3-decodes-wrong-block-length",
            "decode_block_length",
            "Some(value) => Ok(value)",
            "Some(value) => Ok(value + 1)",
        ),
    ] {
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("executable body");
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = check_brotli_prefix_function(&verus, &temporary, function);
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(
            log.contains("postcondition not satisfied") || log.contains("precondition not satisfied")
                || log.contains("invariant not satisfied") || log.contains("assertion failed"),
            "expected a semantic proof rejection: {log}"
        );
        assert!(
            !lower.contains("resource limit") && !lower.contains("panicked")
                && !lower.contains("expected rlimit-count"),
            "tool/resource failure is not a semantic rejection: {log}"
        );
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_three_k3_suffix_plan_relation_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k3-suffix-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    let function = "plan_initial_suffix_action";
    let start = original.find(&format!("fn {function}(")).unwrap();
    let end = start + original[start..].find("\n}\n").unwrap() + 3;
    let selected = &original[start..end];
    let body = selected.find("\n{\n").unwrap();
    for (name, old, new) in [
        (
            "brotli-k3-suffix-plan-loses-consumption",
            "let result = CompressedActionPlan { planning_work, execution_work, consumed: read.consumed, status };",
            "let result = CompressedActionPlan { planning_work, execution_work, consumed: 0, status };",
        ),
        (
            "brotli-k3-suffix-plan-loses-success",
            "Ok(_) => None,",
            "Ok(_) => Some(CompressedHeaderStatus::NeedInput),",
        ),
        (
            "brotli-k3-suffix-plan-undercharges-value-tables",
            "if !budget.charge_work(2)",
            "if !budget.charge_work(1)",
        ),
    ] {
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied") || log.contains("assertion failed"),
            "expected a semantic proof rejection: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_context_mode_handoff_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-context-mode-handoff-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-handoff-reset-writes-wrong-var-phase",
            "start_context_map",
            "store_var_uint8_phase(workspace, window_bytes, VarUint8Phase::First)",
            "store_var_uint8_phase(workspace, window_bytes, VarUint8Phase::Short)",
        ),
        (
            "brotli-m1-handoff-reset-writes-wrong-pending-run",
            "start_context_map",
            "        let (receipt_child_3, Ghost(receipt_child_units_3)) = put_state_byte(workspace, window_bytes, B3B_PENDING_RUN, 255);",
            "        let (receipt_child_3, Ghost(receipt_child_units_3)) = put_state_byte(workspace, window_bytes, B3B_PENDING_RUN, 0);",
        ),
        (
            "brotli-m1-handoff-plan-undercharges-one",
            "plan_context_mode_action",
            "execution_work: context_mode_complete_execution_work(),",
            "execution_work: context_mode_complete_execution_work() - 1,",
        ),
        (
            "brotli-m1-handoff-plan-consumes-input",
            "plan_context_mode_action",
            "execution_work: context_mode_complete_execution_work(),\n            consumed: 0,",
            "execution_work: context_mode_complete_execution_work(),\n            consumed: 1,",
        ),
        (
            "brotli-m1-handoff-action-skips-literal-map",
            "advance_context_modes_phase",
            "                            CompressedOuterPhase::LiteralContextMap); proof { r_source_units = r_source_units + r_child_units_5; } r_child_5 } {",
            "                            CompressedOuterPhase::DistanceContextMap); proof { r_source_units = r_source_units + r_child_units_5; } r_child_5 } {",
        ),
        (
            "brotli-m1-handoff-reset-writes-padding",
            "start_context_map",
            "    let kind_tag = match kind {",
            "    match put_state_byte(workspace, window_bytes, 175, 255).0 { Ok(value) => value, Err(error) => return (Err(error), Ghost(receipt_units)), };\n    let kind_tag = match kind {",
        ),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start
            + original[start..]
                .find(&closing)
                .expect("selected function ends")
            + closing.len();
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        fs::write(&path, mutated).unwrap();
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
                || log.contains("requires not satisfied")
                || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_bad_fixed_cursor_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-bad-fixed-cursor-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-cursor-tag-rejects-with-wrong-error", "read_b3b_state_tag", "return Err(crate::brotli_prefix::WorkspaceError::InvalidSymbol);", "return Err(crate::brotli_prefix::WorkspaceError::InvalidTree);"),
        ("brotli-m1-cursor-distance-prepass-forgets-rejection", "distance_planning_work", "let queue = load_b3b_queue(workspace, window_bytes)?;", "let queue = match load_b3b_queue(workspace, window_bytes) { Ok(value) => value, Err(_) => return Ok(0) };"),
        ("brotli-m1-cursor-block-prepass-forgets-var-rejection", "block_count_planning_work", "let phase = load_var_uint8_phase(workspace, window_bytes)?;", "let phase = match load_var_uint8_phase(workspace, window_bytes) { Ok(value) => value, Err(_) => return Ok(0) };"),
        ("brotli-m1-cursor-block-forecast-omits-terminal-work", "advance_planned_compressed_action", "            Ok(value) => value,\n            Err(_) => {\n                let failure_plan = CompressedActionPlan { planning_work: 0, execution_work: 4 + 1,\n                    consumed: 0, status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState)) };\n                proof {", "            Ok(value) => value,\n            Err(_) => {\n                let mut failure_plan = CompressedActionPlan { planning_work: 0, execution_work: 4 + 1,\n                    consumed: 0, status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState)) };\n                failure_plan.execution_work = 0;\n                proof {"),
        ("brotli-m1-cursor-context-owner-skips-terminal-action", "advance_planned_compressed_action", "                return ({ let (r_child_result, Ghost(r_child_units)) = execute_fixed_compressed_plan(workspace, window_bytes, budget,\n                    CompressedOuterPhase::ContextModes, &input[..initial_allowed],\n                    end_of_input && initial_allowed == input.len(), initial_allowed < input.len(), failure_plan); proof { r_header_action_source_units = r_header_action_source_units + r_child_units; } r_child_result }, Ghost(r_header_action_source_units));", "                return ({ let (r_child_result, Ghost(r_child_units)) = (Err::<usize, CompressedStep>(CompressedStep { consumed: 0, status: CompressedStatus::Failed(CoreFailure::InvalidFormat(CoreFormatDetail::StateEncoding)) }), Ghost(0nat)); proof { r_header_action_source_units = r_header_action_source_units + r_child_units; } r_child_result }, Ghost(r_header_action_source_units));"),
        ("brotli-m1-cursor-executor-forgets-terminal-work-debit", "execute_fixed_compressed_plan", "if !budget.charge_work(plan.execution_work) {", "if !budget.charge_work(if plan.execution_work == 5 { 0 } else { plan.execution_work }) {"),
    ] {
        let start = original
            .find(&format!("fn {function}("))
            .expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start
            + original[start..]
                .find(&closing)
                .expect("selected function ends")
            + closing.len();
        let selected = &original[start..end];
        assert_eq!(
            selected.matches(old).count(),
            1,
            "unique mutation anchor for {name}"
        );
        let mutated = format!(
            "{}{}{}",
            &original[..start],
            selected.replacen(old, new, 1),
            &original[end..]
        );
        let mutated = if name == "brotli-m1-cursor-context-owner-skips-terminal-action" {
            // The checked witnessed call supplies5; the skipped child's literal is authoritative.
            let skipped_receipts: Vec<_> = new.split("Ghost(").skip(1)
                .filter_map(|tail| tail.split_once(')').map(|(value, _)| value))
                .filter(|value| value.chars().next().is_some_and(|first| first.is_ascii_digit()))
                .collect();
            assert_eq!(skipped_receipts, vec!["0nat"], "unique skipped-child receipt for {name}");
            let insertion_at = start + selected.find(old).unwrap();
            let healthy_receipt = "                proof { assert(if 5nat == 5nat { true } else { false }) by (compute_only); }\n";
            let mut healthy_source = original.clone();
            healthy_source.insert_str(insertion_at, healthy_receipt);
            fs::write(&path, &healthy_source).unwrap();
            let healthy = check_brotli_input_function(&verus, &temporary, function);
            assert!(healthy.status.success(), "healthy cursor receipt root failed: {}", transcript(&healthy));
            let negative_receipt = format!("                proof {{ assert(if {} == 5nat {{ true }} else {{ false }}) by (compute_only); }}\n", skipped_receipts[0]);
            assert_eq!(&mutated[insertion_at..insertion_at + new.len()], new, "qualified skipped-child stub");
            let mut coupled_negative = mutated;
            coupled_negative.insert_str(insertion_at, &negative_receipt);
            coupled_negative
        } else {
            mutated
        };
        fs::write(&path, mutated).unwrap();
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
                || log.contains("requires not satisfied")
                || log.contains("assertion failed")
                || (name == "brotli-m1-cursor-context-owner-skips-terminal-action"
                    && log.to_lowercase().contains("error: expression simplifies to false")
                    && log.contains("by (compute_only)")),
            "expected a proof rejection, not a tooling error: {log}"
        );
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_k4_repeat_codec_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k4-repeat-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-k4-repeat-store-overwrites-history",
            "store_complex_code_description_payload",
            "            proof { }\n            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_PENDING_SPAN_LENGTH, length); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };\n            proof { }",
            "            proof { }\n            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_REPEATED_LENGTH, length); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };\n            proof { }",
        ),
        (
            "brotli-k4-repeat-load-current-from-history",
            "load_code_description_decoder",
            "let repeat_length = match state_byte(\n                        workspace, window_bytes, B3B_PENDING_SPAN_LENGTH) {",
            "let repeat_length = match state_byte(\n                        workspace, window_bytes, B3B_REPEATED_LENGTH) {",
        ),
        (
            "brotli-k4-progress-stores-previous-code-in-history",
            "store_complex_progress",
            "(B3B_REPEATED_LENGTH, progress.repeat_code_len)",
            "(B3B_REPEATED_LENGTH, progress.prev_code_len)",
        ),
        (
            "brotli-k4-repeat-load-history-from-current",
            "load_code_description_decoder",
            "let repeated = match state_byte(workspace, window_bytes, B3B_REPEATED_LENGTH) {",
            "let repeated = match state_byte(workspace, window_bytes, if tag == 6 { B3B_PENDING_SPAN_LENGTH } else { B3B_REPEATED_LENGTH }) {",
        ),
        (
            "brotli-k4-repeat-width-uses-old-class",
            "load_code_description_decoder",
            "let extra_bits = if repeat_length == 0 { 3 } else { 2 };",
            "let extra_bits = if repeated == 0 { 3 } else { 2 };",
        ),
        (
            "brotli-k4-repeat-rejects-valid-length-fifteen",
            "load_code_description_decoder",
            "if repeat_length > 15 {",
            "if repeat_length >= 15 {",
        ),
    ] {
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(lower.contains("postcondition not satisfied") || lower.contains("precondition not satisfied")
            || lower.contains("invariant not satisfied") || lower.contains("assertion failed"),
            "expected a semantic proof rejection: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_fourteen_k5_loader_accounting_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k5-loader-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-k5-loader-omits-four-simple-copies", "plan_saved_loader_read_units", "let base = 4 + aux_reads;", "let base = aux_reads;"),
        ("brotli-k5-prefix-validation-scan-undercharge", "plan_saved_loader_read_units", "        return (Ok(base + if 1 <= auxiliary_phase && auxiliary_phase <= 3 { 18u64 } else { 0u64 }), Ghost(r_saved_forecast_source_reads));", "        return (Ok(base + if 1 <= auxiliary_phase && auxiliary_phase <= 3 { 17u64 } else { 0u64 }), Ghost(r_saved_forecast_source_reads));"),
        ("brotli-k5-singleton-guard-reordered-before-scan", "plan_saved_loader_read_units", "|| prefix_bits >= (1u8 << prefix_width) || singleton >= 18 {", "|| prefix_bits >= (1u8 << prefix_width) || prefix_width != 0 || singleton >= 18 {"),
        ("brotli-k5-selected-singleton-read-unpaid", "plan_saved_singleton_validation_reads", "    proof { singleton_other_read_bounds(values, singleton as nat, 0); assert(total <= 18); }\n    if !budget.charge_work(1) { return (Err(CoreFailure::ResourceLimit), Ghost(r_saved_forecast_source_reads)); }\n    let selected = match state_byte(workspace, window_bytes, B3B_AUX_LENGTHS + singleton as u16)", "    proof { singleton_other_read_bounds(values, singleton as nat, 0); assert(total <= 18); }\n    if !budget.charge_work(0) { return (Err(CoreFailure::ResourceLimit), Ghost(r_saved_forecast_source_reads)); }\n    let selected = match state_byte(workspace, window_bytes, B3B_AUX_LENGTHS + singleton as u16)"),
        ("brotli-k5-singleton-skips-last-validation-cell", "plan_saved_singleton_validation_reads", "while i < 18", "while i < 17"),
        ("brotli-k5-simple-right-comparison-operand-unpaid", "plan_saved_simple_validation_reads", "        inspected += 1;\n            if !budget.charge_work(1) { return (Err(CoreFailure::ResourceLimit), Ghost(r_saved_forecast_source_reads)); }\n            let right = match state_u16(workspace, window_bytes, B3B_SIMPLE_SYMBOLS + 2 * j as u16)", "        inspected += 1;\n            if !budget.charge_work(0) { return (Err(CoreFailure::ResourceLimit), Ghost(r_saved_forecast_source_reads)); }\n            let right = match state_u16(workspace, window_bytes, B3B_SIMPLE_SYMBOLS + 2 * j as u16)"),
        ("brotli-k5-simple-omits-right-operand-receipt", "plan_saved_simple_validation_reads", "            proof { r_saved_forecast_source_reads = r_saved_forecast_source_reads + 1; }\n        inspected += 1;\n            if left == right {", "            proof { r_saved_forecast_source_reads = r_saved_forecast_source_reads + 1; }\n        inspected += 0;\n            if left == right {"),
        ("brotli-k5-selector-reload-keeps-old-eighteen", "valid_code_loader_read_units", "_ => 22,", "_ => 18,"),
        ("brotli-k5-prefix-reload-omits-validation-cell", "valid_code_loader_read_units", "valid_complex_code_scan_is_18(ComplexCodeLengthAlphabet { skip: progress.skip, lengths: progress.lengths }); }\n            40", "valid_complex_code_scan_is_18(ComplexCodeLengthAlphabet { skip: progress.skip, lengths: progress.lengths }); }\n            39"),
        ("brotli-k5-singleton-reload-omits-selected-cell", "valid_code_loader_read_units", "CodeDescriptionPhase::ComplexSymbol(progress)\n        | CodeDescriptionPhase::ComplexRepeat { progress, .. } => {\n            proof { valid_complex_symbol_validation_count(progress, decoder.alphabet_limit); }\n            40 + if progress.singleton < 18 { 18u64 } else { 0u64 }", "CodeDescriptionPhase::ComplexSymbol(progress)\n        | CodeDescriptionPhase::ComplexRepeat { progress, .. } => {\n            proof { valid_complex_symbol_validation_count(progress, decoder.alphabet_limit); }\n            40 + if progress.singleton < 18 { 17u64 } else { 0u64 }"),
        ("brotli-k5-initial-loader-replay-unpaid", "plan_serialized_tree", "budget.charge_work(loader_reads)", "budget.charge_work(0)"),
        ("brotli-k5-each-reload-restores-old-eighteen", "plan_serialized_tree", "checked_planned_work_add(execution_work, reload_reads)", "checked_planned_work_add(execution_work, 18)"),
        ("brotli-k5-invalid-last-auxiliary-misclassified-valid", "plan_saved_aux_load", "            return (Ok((i as u64 + 1, false)), Ghost(r_saved_forecast_source_reads));", "            return (Ok((i as u64 + 1, true)), Ghost(r_saved_forecast_source_reads));"),
        ("brotli-k5-invalid-alphabet-misclassified-valid", "plan_saved_aux_load", "    if maximum == 0 || maximum > 704 || limit == 0 || limit > maximum { return (Ok((0, false)), Ghost(r_saved_forecast_source_reads)); }", "    if maximum == 0 || maximum > 704 || limit == 0 || limit > maximum { return (Ok((0, true)), Ghost(r_saved_forecast_source_reads)); }"),
    ] {
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(lower.contains("postcondition not satisfied") || lower.contains("precondition not satisfied")
            || lower.contains("invariant not satisfied") || lower.contains("assertion failed"),
            "expected a semantic proof rejection: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_twelve_m1_general_codec_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-general-codec-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        (
            "brotli-m1-codec-simple-index-erased",
            "store_simple_code_description_payload",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_CODE_INDEX, index); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_CODE_INDEX, 0); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
        ),
        (
            "brotli-m1-codec-shape-selector-lost",
            "store_simple_code_description_payload",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_SIMPLE_SELECTOR, 3); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_SIMPLE_SELECTOR, 2); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
        ),
        (
            "brotli-m1-codec-symbol-array-alias",
            "write_simple_symbols",
            "            symbols[i],",
            "            symbols[0],",
        ),
        (
            "brotli-m1-codec-aux-array-erased",
            "write_aux_lengths",
            "            lengths[i],",
            "            0,",
        ),
        (
            "brotli-m1-codec-prefix-phase-alias",
            "store_complex_code_description_payload",
            "CodeDescriptionPhase::ComplexPrefix3(_) => 2,",
            "CodeDescriptionPhase::ComplexPrefix3(_) => 3,",
        ),
        (
            "brotli-m1-codec-prefix-nonzero-erased",
            "store_complex_code_description_payload",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_AUX_NONZERO, progress.nonzero); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_AUX_NONZERO, 0); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
        ),
        (
            "brotli-m1-codec-aux-skip-erased",
            "store_complex_code",
            "put_state_byte(workspace, window_bytes, B3B_AUX_SKIP, code.skip)",
            "put_state_byte(workspace, window_bytes, B3B_AUX_SKIP, 0)",
        ),
        (
            "brotli-m1-codec-chained-history-erased",
            "store_complex_progress",
            "put_state_u32(workspace, window_bytes, B3B_CHAINED_REPEAT, progress.repeat)",
            "put_state_u32(workspace, window_bytes, B3B_CHAINED_REPEAT, 0)",
        ),
        (
            "brotli-m1-codec-parent-tag-erased",
            "store_code_description_decoder",
            "put_state_byte(workspace, window_bytes, B3B_CODE_PHASE, tag)",
            "put_state_byte(workspace, window_bytes, B3B_CODE_PHASE, 0)",
        ),
        (
            "brotli-m1-codec-failed-error-tag-alias",
            "code_description_error_tag",
            "CodeDescriptionError::InvalidAlphabet => 2,",
            "CodeDescriptionError::InvalidAlphabet => 3,",
        ),
        (
            "brotli-m1-codec-simple-write-undercharge",
            "store_simple_code_description_payload",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_CODE_INDEX, index); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
            "            { let (r_write, Ghost(r_write_units)) = put_state_byte(workspace, window_bytes, B3B_CODE_INDEX, index); proof { source_writes = source_writes + 0; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };",
        ),
        (
            "brotli-m1-codec-complex-write-undercharge",
            "store_complex_code_description_payload",
            "        CodeDescriptionPhase::ComplexSymbol(progress) => {\n            { let (r_write, Ghost(r_write_units)) = store_complex_progress(workspace, window_bytes, progress); proof { source_writes = source_writes + r_write_units; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };\n            proof { }",
            "        CodeDescriptionPhase::ComplexSymbol(progress) => {\n            { let (r_write, Ghost(r_write_units)) = store_complex_progress(workspace, window_bytes, progress); proof { source_writes = source_writes + if r_write.is_ok() { (r_write_units - 1) as nat } else { r_write_units }; } match r_write { Ok(value) => value, Err(error) => return (Err(error), Ghost(source_writes)), } };\n            proof { }",
        ),
    ] {
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(lower.contains("postcondition not satisfied") || lower.contains("precondition not satisfied")
            || lower.contains("invariant not satisfied") || lower.contains("assertion failed"),
            "expected a semantic proof rejection: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_twelve_k6_simple_install_metering_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k6-install-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    for (name, module, function, old, new) in [
        (
            "brotli-k6-singleton-reservation-restores-five",
            "input",
            "simple_tree_install_work",
            "if selector == 0 { 7 } else {",
            "if selector == 0 { 5 } else {",
        ),
        (
            "brotli-k6-selector-four-uses-three-symbols",
            "input",
            "simple_tree_install_work",
            "let count: u64 = if selector <= 2 { selector as u64 + 1 } else { 4 };",
            "let count: u64 = if selector <= 2 { selector as u64 + 1 } else { 3 };",
        ),
        (
            "brotli-k6-install-omits-validation-reads",
            "input",
            "simple_tree_install_work",
            "        work\n",
            "        if selector == 1 && alphabet == 2 { 14 } else { work }\n",
        ),
        (
            "brotli-k6-install-omits-record-probes",
            "input",
            "simple_tree_install_work",
            "        work\n",
            "        if selector == 1 && alphabet == 2 { 15 } else { work }\n",
        ),
        (
            "brotli-k6-triangular-correction-undercharged",
            "input",
            "simple_tree_install_work",
            "let work = (3 + count) * alphabet as u64 + 5 + count * (count + 1) / 2;",
            "let work = (3 + count) * alphabet as u64 + 5 + count * (count + 1) / 3;",
        ),
        (
            "brotli-k6-first-record-probe-unpaid",
            "prefix",
            "simple_record_exec",
            "if { proof { source_reads = source_reads + 1; } symbol == symbols[0] }",
            "if { proof { source_reads = source_reads + 0; } symbol == symbols[0] }",
        ),
        (
            "brotli-k6-fourth-record-probe-unpaid",
            "prefix",
            "simple_record_exec",
            "count > 3 && { proof { source_reads = source_reads + 1; } symbol == symbols[3] }",
            "count > 3 && { proof { source_reads = source_reads + 0; } symbol == symbols[3] }",
        ),
        (
            "brotli-k6-range-validation-read-unpaid",
            "prefix",
            "install_simple_tree",
            "proof { reveal(k6_simple_symbol_prefix); source_reads = source_reads + 1; }\n        if symbols[i as usize]",
            "proof { reveal(k6_simple_symbol_prefix); source_reads = source_reads + 0; }\n        if symbols[i as usize]",
        ),
        (
            "brotli-k6-distinctness-right-read-unpaid",
            "prefix",
            "install_simple_tree",
            "proof { reveal(k6_simple_symbol_prefix); source_reads = source_reads + 2; }",
            "proof { reveal(k6_simple_symbol_prefix); source_reads = source_reads + 1; }",
        ),
        (
            "brotli-k6-singleton-final-read-unpaid",
            "prefix",
            "install_simple_tree",
            "source_reads = source_reads + 1;\n            assert(source_reads == 2);",
            "source_reads = source_reads + 0;\n            assert(source_reads == 2);",
        ),
        (
            "brotli-k6-adapter-omits-installation-reservation",
            "input",
            "plan_serialized_tree",
            "simple_tree_install_work(decoder.alphabet_limit, code.selector),",
            "0,",
        ),
        (
            "brotli-k6-installer-reads-before-destination-guard",
            "prefix",
            "install_simple_tree",
            "let ghost mut source_reads: nat = 0;",
            "let ghost mut source_reads: nat = 0;\n    let _observed_symbol = symbols[0];\n    proof { source_reads = source_reads + 1; }",
        ),
    ] {
        let source_name = if module == "prefix" { "src/brotli_prefix.rs" } else { "src/brotli_input.rs" };
        let path = temporary.join(source_name);
        let original = fs::read_to_string(&path).unwrap();
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = if module == "prefix" { check_brotli_prefix_function(&verus, &temporary, function) }
            else { check_brotli_input_function(&verus, &temporary, function) };
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(lower.contains("postcondition not satisfied") || lower.contains("precondition not satisfied")
            || lower.contains("invariant not satisfied") || lower.contains("assertion failed"),
            "expected a semantic proof rejection: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_m1_executor_normal_trace_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-executor-normal-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-executor-simple-loses-consumption", "advance_serialized_tree",
            "let simple_result = SerializedTreeStep { consumed, status };",
            "let simple_result = SerializedTreeStep { consumed: 0, status };"),
        ("brotli-m1-executor-canonical-loses-consumption", "advance_serialized_tree",
            "                return (SerializedTreeStep { consumed, status }, Ghost(source_execution_units));",
            "                return (SerializedTreeStep { consumed : 0 , status }, Ghost(source_execution_units));"),
        ("brotli-m1-executor-simple-false-need-input", "advance_serialized_tree",
            "let simple_result = SerializedTreeStep { consumed, status };",
            "let simple_result = SerializedTreeStep { consumed, status: if !end_of_input && consumed == input.len() { SerializedTreeStatus::NeedInput } else { status } };"),
        ("brotli-m1-executor-canonical-false-need-input", "advance_serialized_tree",
            "                return (SerializedTreeStep { consumed, status }, Ghost(source_execution_units));",
            "                return (SerializedTreeStep { consumed, status  : if status == SerializedTreeStatus::Complete && !end_of_input && consumed == input.len() { SerializedTreeStatus::NeedInput } else { status } }, Ghost(source_execution_units));"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_eight_m1_parser_failure_relation_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-executor-parser-failure-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-executor-parser-error-replaced", "advance_serialized_tree",
            "map_code_description_error(error)", "CompressedHeaderError::InternalState"),
        ("brotli-m1-executor-bad-span-error-replaced", "advance_serialized_tree",
            "                                actions, action, before_consumed as nat, SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) }, source_execution_units, actual_parts.push(actual_part));\n                        }\n                        return (SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) }, Ghost(source_execution_units));\n                    },\n                }",
            "                                actions, action, before_consumed as nat, SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(error) }, source_execution_units, actual_parts.push(actual_part));\n                        }\n                        return (SerializedTreeStep { consumed, status: SerializedTreeStatus::Failed(CompressedHeaderError::Truncated) }, Ghost(source_execution_units));\n                    },\n                }"),
        ("brotli-m1-executor-canonical-error-replaced", "m1_tree_complete_canonical_status",
            "Err(error) => SerializedTreeStatus::Failed(error),",
            "Err(_error) => SerializedTreeStatus::Failed(CompressedHeaderError::Truncated),"),
        ("brotli-m1-executor-empty-input-fabricates-error", "advance_serialized_tree",
            "    let ghost loop_limit = b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_LIMIT) as u16;\n    let mut consumed: usize = 0;\n    let mut work: u16 = 0;",
            "    let ghost loop_limit = b3b_scalar_u16_at(original, window_bytes, B3B_ALPHABET_LIMIT) as u16;\n    if input.is_empty() { return (SerializedTreeStep { consumed: 0, status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState) }, Ghost(source_execution_units)); }\n    let mut consumed: usize = 0;\n    let mut work: u16 = 0;"),
        ("brotli-m1-pending-span-wrong-failure-reason", "drain_serialized_pending_span",
            "        proof { assert(workspace@ == original); }\n        return (Err(CompressedHeaderError::InternalState), Ghost(source_span_writes));\n    }",
            "        proof { assert(workspace@ == original); }\n        return (Err(CompressedHeaderError::Truncated), Ghost(source_span_writes));\n    }"),
        ("brotli-m1-planner-parser-error-replaced", "plan_serialized_tree",
            "map_code_description_error(error)", "CompressedHeaderError::InternalState"),
        ("brotli-m1-planner-bad-span-error-replaced", "plan_serialized_tree",
            "if builder_initialized != start\n                    || start as u32 + span_count as u32 > decoder.alphabet_limit as u32\n                {\n                    let failed_result = SerializedTreePlan { planning_work, execution_work, consumed,\n                        status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState) };",
            "if builder_initialized != start\n                    || start as u32 + span_count as u32 > decoder.alphabet_limit as u32\n                {\n                    let failed_result = SerializedTreePlan { planning_work, execution_work, consumed,\n                        status: SerializedTreeStatus::Failed(CompressedHeaderError::Truncated) };"),
        ("brotli-m1-planner-bad-builder-error-replaced", "plan_serialized_tree",
            "if builder_initialized != decoded_symbols\n                    || decoded_symbols != decoder.alphabet_limit\n                {\n                    let failed_result = SerializedTreePlan { planning_work, execution_work, consumed,\n                        status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState) };",
            "if builder_initialized != decoded_symbols\n                    || decoded_symbols != decoder.alphabet_limit\n                {\n                    let failed_result = SerializedTreePlan { planning_work, execution_work, consumed,\n                        status: SerializedTreeStatus::Failed(CompressedHeaderError::Truncated) };"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        let (scope_start, scope_end) = if name == "brotli-m1-executor-bad-span-error-replaced" {
            let begin = selected.find("drain_and_store_serialized_pending_span(").unwrap();
            let end = begin + selected[begin..].find("CodeDescriptionPhase::CompleteSimple(").unwrap();
            (begin, end)
        } else { (body, selected.len()) };
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_k7_k8_result_contract_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-k7-k8-result-canary-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    for (name, module, function, old, new) in [
        ("brotli-k7-canonical-constructor-spurious-error", "prefix", "canonical",
            "Ok(Self { symbols, storage: TreeStorageState::Canonical { initialized: 0 } })",
            "Err(WorkspaceError::InvalidSymbol)"),
        ("brotli-k8-single-constructor-spurious-error", "prefix", "single",
            "Ok(Self { symbols, storage: TreeStorageState::Single { symbol } })",
            "Err(WorkspaceError::InvalidSymbol)"),
        (
            "brotli-k7-singleton-install-spurious-error",
            "prefix",
            "install_simple_tree",
            "return (TreeMetadata::single(region, alphabet_limit, symbols[0]), Ghost(source_reads + source_writes));",
            "return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_reads + source_writes));",
        ),
        ("brotli-k7-multi-install-spurious-error", "prefix", "install_simple_tree",
            "let mut meta = match TreeMetadata::canonical(region, alphabet_limit) {",
            "if selector == 1 && alphabet_limit == 2 { return (Err(WorkspaceError::InvalidCodeLength), Ghost(source_reads + source_writes)); }\n    let mut meta = match TreeMetadata::canonical(region, alphabet_limit) {"),
        (
            "brotli-k8-invalid-tree-error-replaced",
            "prefix",
            "install_builder_canonical_tree",
            "if tree >= tree_region_count_exec(region) {\n        proof { assert(source_validation_reads == 0); }\n        return (Err(WorkspaceError::InvalidTree), Ghost(",
            "if tree >= tree_region_count_exec(region) {\n        proof { assert(source_validation_reads == 0); }\n        return (Err(WorkspaceError::InvalidSymbol), Ghost(",
        ),
        (
            "brotli-k8-invalid-tree-mutates-metadata",
            "prefix",
            "install_builder_canonical_tree",
            "if tree >= tree_region_count_exec(region) {\n        proof { assert(source_validation_reads == 0); }\n        return (Err(WorkspaceError::InvalidTree), Ghost(",
            "if tree >= tree_region_count_exec(region) {\n        proof { assert(source_validation_reads == 0); }\n        meta.storage = TreeStorageState::Unused;\n        return (Err(WorkspaceError::InvalidTree), Ghost(",
        ),
    ] {
        let source_name = if module == "prefix" { "src/brotli_prefix.rs" } else { "src/brotli_input.rs" };
        let path = temporary.join(source_name);
        let original = fs::read_to_string(&path).unwrap();
        let start = original.find(&format!("fn {function}(")).unwrap();
        let line = original[..start].rsplit('\n').next().unwrap();
        let indent = line.chars().take_while(|ch| ch.is_whitespace()).count();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start + original[start..].find(&closing).unwrap() + closing.len();
        let selected = &original[start..end];
        let opening = format!("\n{}{{\n", " ".repeat(indent));
        let body = selected.find(&opening).unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let selector = if function == "canonical" || function == "single" { format!("TreeMetadata::{function}") } else { function.to_string() };
        let result = if module == "prefix" { check_brotli_prefix_function(&verus, &temporary, &selector) }
            else { check_brotli_input_function(&verus, &temporary, function) };
        let log = transcript(&result);
        let lower = log.to_ascii_lowercase();
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(lower.contains("postcondition not satisfied") || lower.contains("precondition not satisfied")
            || lower.contains("invariant not satisfied") || lower.contains("assertion failed"),
            "expected a semantic proof rejection: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_m1_tree_install_outcome_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-tree-install-outcome-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-tree-simple-rejection-is-truncated", "m1_tree_complete_simple_status",
            "Err(error) => SerializedTreeStatus::Failed(error),",
            "Err(_error) => SerializedTreeStatus::Failed(CompressedHeaderError::Truncated),"),
        ("brotli-m1-tree-canonical-rejection-is-internal", "m1_tree_complete_canonical_status",
            "Err(error) => SerializedTreeStatus::Failed(error),",
            "Err(_error) => SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),"),
        ("brotli-m1-tree-simple-plan-reports-invalid-tree", "plan_serialized_tree",
            "const SIMPLE_DESTINATION_ERROR: crate::brotli_prefix::WorkspaceError = crate::brotli_prefix::WorkspaceError::InvalidSymbol;",
            "const SIMPLE_DESTINATION_ERROR: crate::brotli_prefix::WorkspaceError = crate::brotli_prefix::WorkspaceError::InvalidTree;"),
        ("brotli-m1-tree-canonical-plan-loses-tree-priority", "plan_serialized_tree",
            "const CANONICAL_TREE_ERROR: crate::brotli_prefix::WorkspaceError = crate::brotli_prefix::WorkspaceError::InvalidTree;",
            "const CANONICAL_TREE_ERROR: crate::brotli_prefix::WorkspaceError = crate::brotli_prefix::WorkspaceError::InvalidSymbol;"),
        ("brotli-m1-tree-canonical-plan-loses-length-error", "plan_serialized_tree",
            "const CANONICAL_LENGTH_ERROR: crate::brotli_prefix::WorkspaceError = crate::brotli_prefix::WorkspaceError::InvalidCodeLength;",
            "const CANONICAL_LENGTH_ERROR: crate::brotli_prefix::WorkspaceError = crate::brotli_prefix::WorkspaceError::InvalidSymbol;"),
        ("brotli-m1-tree-owner-flags-matching-workspace-error", "advance_planned_context_tree",
            "(SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(crate::brotli_prefix::WorkspaceError::InvalidTree)), SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(crate::brotli_prefix::WorkspaceError::InvalidTree))) => false,",
            "(SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(crate::brotli_prefix::WorkspaceError::InvalidTree)), SerializedTreeStatus::Failed(CompressedHeaderError::Workspace(crate::brotli_prefix::WorkspaceError::InvalidTree))) => true,"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        let (scope_start, scope_end) = (body, selected.len());
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        let computed_contradiction = matches!(name,
            "brotli-m1-tree-simple-plan-reports-invalid-tree"
            | "brotli-m1-tree-canonical-plan-loses-tree-priority"
            | "brotli-m1-tree-canonical-plan-loses-length-error")
            && log.contains("error: expression simplifies to false")
            && log.contains("assert(matches!(") && log.contains("by (compute_only)");
        assert!(computed_contradiction || log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_m1_invalid_start_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-invalid-start-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-invalid-region-consumes-input", "advance_serialized_tree",
            "        None => return (SerializedTreeStep {\n            consumed: 0,\n            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),",
            "        None => return (SerializedTreeStep {\n            consumed:  if input.is_empty() { 0 } else { 1 } ,\n            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),"),
        ("brotli-m1-invalid-region-mutates-descriptor", "advance_serialized_tree",
            "        None => return (SerializedTreeStep {\n            consumed: 0,\n            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),\n        }, Ghost(source_execution_units)),",
            "        None =>  { let _ = put_state_byte(workspace, window_bytes, B3B_CODE_PHASE, 0); return (SerializedTreeStep {\n            consumed: 0,\n            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),\n        }, Ghost(source_execution_units)) ; } ,"),
        ("brotli-m1-invalid-region-plan-consumes-input", "plan_serialized_tree",
            "        None => return (Ok(SerializedTreePlan { planning_work: 0, execution_work: 0, consumed: 0,",
            "        None => return (Ok(SerializedTreePlan { planning_work: 0, execution_work: 0, consumed:  if input.is_empty() { 0 } else { 1 } ,"),
        ("brotli-m1-invalid-descriptor-plan-consumes-input", "plan_serialized_tree",
            "execution_work: loader_reads, consumed: 0,",
            "execution_work: loader_reads, consumed: if input.is_empty() { 0 } else { 1 },"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        let (scope_start, scope_end) = (body, selected.len());
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_five_m1_tree_error_identity_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-tree-error-identity-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-saved-loader-spurious-unsupported-mode", "load_code_description_decoder", "        || alphabet_limit == 0 || alphabet_limit > alphabet_max {\n        return ({ proof { assert(source_reads == loader_table_read_units(workspace@, window_bytes)); } Err(CompressedHeaderError::InternalState) }, Ghost(source_reads));\n    }", "        || alphabet_limit == 0 || alphabet_limit > alphabet_max {\n        return ({ proof { assert(source_reads == loader_table_read_units(workspace@, window_bytes)); } Err(CompressedHeaderError::UnsupportedMode) }, Ghost(source_reads));\n    }"),
        ("brotli-m1-malformed-region-executor-wrong-error", "advance_serialized_tree", "            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState),", "            status: SerializedTreeStatus::Failed(CompressedHeaderError::UnsupportedMode),"),
        ("brotli-m1-malformed-region-planner-wrong-error", "plan_serialized_tree", "            status: SerializedTreeStatus::Failed(CompressedHeaderError::InternalState) }), Ghost(r_tree_planning_source_units)),", "            status: SerializedTreeStatus::Failed(CompressedHeaderError::UnsupportedMode) }), Ghost(r_tree_planning_source_units)),"),
        ("brotli-m1-malformed-descriptor-plan-wrong-error", "plan_serialized_tree", "            execution_work: loader_reads, consumed: 0,\n            status: SerializedTreeStatus::Failed(error) }), Ghost(r_tree_planning_source_units)),\n    };", "            execution_work: loader_reads, consumed: 0,\n            status: SerializedTreeStatus::Failed(CompressedHeaderError::UnsupportedMode) }), Ghost(r_tree_planning_source_units)),\n    };"),
        ("brotli-m1-tree-caller-flags-equal-internal-errors", "advance_planned_context_tree", "(SerializedTreeStatus::Failed(CompressedHeaderError::InternalState), SerializedTreeStatus::Failed(CompressedHeaderError::InternalState)) => false,", "(SerializedTreeStatus::Failed(CompressedHeaderError::InternalState), SerializedTreeStatus::Failed(CompressedHeaderError::InternalState)) => true,"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        let (scope_start, scope_end) = (body, selected.len());
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_five_m1_literal_handoff_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-literal-handoff-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-literal-handoff-accepts-zero-command-count", "plan_tree_group_handoff", "if next_count == 0 || next_count > 256 {", "if next_count > 256 {"),
        ("brotli-m1-literal-handoff-accepts-large-command-count", "plan_tree_group_handoff", "if next_count == 0 || next_count > 256 {", "if next_count == 0 {"),
        ("brotli-m1-literal-handoff-terminal-work-undercharge", "plan_tree_group_handoff", "            if next_count == 0 || next_count > 256 {\n                return (Ok(CompressedActionPlan { planning_work: 0, execution_work: 5, consumed: 0, status: failed }), Ghost(r_tree_wrapper_plan_source_reads));\n            }", "            if next_count == 0 || next_count > 256 {\n                return (Ok(CompressedActionPlan { planning_work: 0, execution_work: 4, consumed: 0, status: failed }), Ghost(r_tree_wrapper_plan_source_reads));\n            }"),
        ("brotli-m1-literal-handoff-loses-error", "plan_tree_group_handoff", "            if next_count == 0 || next_count > 256 {\n                return (Ok(CompressedActionPlan { planning_work: 0, execution_work: 5, consumed: 0, status: failed }), Ghost(r_tree_wrapper_plan_source_reads));\n            }", "            if next_count == 0 || next_count > 256 {\n                return (Ok(CompressedActionPlan { planning_work: 0, execution_work: 5, consumed: 0, status: None }), Ghost(r_tree_wrapper_plan_source_reads));\n            }"),
        ("brotli-m1-literal-handoff-loses-planning-debit", "plan_tree_group_action", "    Ok(CompressedActionPlan {\n        planning_work,\n        execution_work,\n        consumed: tree.consumed,\n        status,\n    })", "    Ok(CompressedActionPlan {\n        planning_work: 0,\n        execution_work,\n        consumed: tree.consumed,\n        status,\n    })"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        let (scope_start, scope_end) = (body, selected.len());
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_sixteen_m1_final_handoff_and_debit_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-final-handoff-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-handoff-loses-distance-parameter-rejection", "plan_tree_group_handoff", "if postfix > 3 || direct > 120 {", "if false {"),
        ("brotli-m1-handoff-loses-final-count-validation", "plan_tree_group_handoff", "if literal_types == 0 || literal_types > 256\n        || command_types == 0 || command_types > 256\n        || distance_types == 0 || distance_types > 256\n        || literal_trees == 0 || literal_trees > 256\n        || distance_trees == 0 || distance_trees > 256 {", "if false {"),
        ("brotli-m1-handoff-accepts-out-of-range-literal-context", "plan_tree_group_handoff", "if literal as u16 >= literal_trees {", "if literal as u16 > literal_trees {"),
        ("brotli-m1-handoff-accepts-out-of-range-distance-context", "plan_tree_group_handoff", "if distance as u16 >= distance_trees {", "if distance as u16 > distance_trees {"),
        ("brotli-m1-handoff-accepts-zero-initial-length", "plan_tree_group_handoff", "if literal_length == 0 || command_length == 0 || distance_length == 0 {", "if false {"),
        ("brotli-m1-handoff-first-map-read-not-prepaid", "plan_tree_group_handoff", "    // Each forecast context-cell access is prepaid before its actual read.\n    if !budget.charge_work(1) { return (Err(CoreFailure::ResourceLimit), Ghost(r_tree_wrapper_plan_source_reads)); }\n    let literal = workspace[literal_at];", "    // Each forecast context-cell access is prepaid before its actual read.\n    if !budget.charge_work(0) { return (Err(CoreFailure::ResourceLimit), Ghost(r_tree_wrapper_plan_source_reads)); }\n    let literal = workspace[literal_at];"),
        ("brotli-m1-handoff-second-map-read-not-prepaid", "plan_tree_group_handoff", "    }\n    if !budget.charge_work(1) { return (Err(CoreFailure::ResourceLimit), Ghost(r_tree_wrapper_plan_source_reads)); }\n    let distance = workspace[distance_at];", "    }\n    if !budget.charge_work(0) { return (Err(CoreFailure::ResourceLimit), Ghost(r_tree_wrapper_plan_source_reads)); }\n    let distance = workspace[distance_at];"),
        ("brotli-m1-handoff-ready-start-undercharge", "plan_tree_group_handoff", "ready_switch_start_work() + 1 + 1 + 1", "ready_switch_start_work() + 1 + 1"),
        ("brotli-m1-block-tree-execution-reservation-undercharge", "advance_planned_block_tree", "budget.charge_work(plan.execution_work)", "budget.charge_work(plan.execution_work.saturating_sub(1))"),
        ("brotli-m1-tree-group-execution-reservation-undercharge", "advance_planned_tree_group", "budget.charge_work(plan.execution_work)", "budget.charge_work(plan.execution_work.saturating_sub(1))"),
        ("brotli-m1-map-tail-execution-reservation-undercharge", "advance_planned_context_map_tail", "budget.charge_work(plan.execution_work)", "budget.charge_work(plan.execution_work.saturating_sub(1))"),
        ("brotli-m1-terminal-execution-reservation-undercharge", "advance_planned_terminal_header", "budget.charge_work(work)", "budget.charge_work(work.saturating_sub(1))"),
        ("brotli-m1-terminal-plan-accepts-zero-length", "plan_terminal_header_work", "if count == 0 || count > 256 || length == 0 { failed = true; }", "if count == 0 || count > 256 { failed = true; }"),
        ("brotli-m1-map-handoff-rejection-undercharge", "plan_context_map_tail", "execution_work = 2 + 4 + 1;", "execution_work = 2 + 4;"),
        ("brotli-m1-map-tail-replay-consumption-corrupted", "advance_planned_context_map_tail", "    let ordinary_result = {\n        Ok(0)\n    };", "    let ordinary_result = {\n        Ok(1)\n    };"),
        ("brotli-m1-map-tail-replay-coverage-error-corrupted", "advance_planned_context_map_tail", "        return (Err(CompressedStep { consumed: 0, status: CompressedStatus::Failed(map_compressed_error(error)) }), Ghost(r_tail_owner_source_units));", "        return (Err(CompressedStep { consumed: 0, status: CompressedStatus::Failed(core_state_failure()) }), Ghost(r_tail_owner_source_units));"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let end = start + original[start..].find("\n}\n").expect("selected function ends") + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").expect("function body");
        let (scope_start, scope_end) = (body, selected.len());
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires an unchanged whole-crate positive and VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_m1_context_cursor_terminal_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-context-cursor-terminal-canary-{}", std::process::id()));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-context-count-cursor-terminal-undercharged", "advance_planned_context_tree_count",
            "planning_work: 0, execution_work: 5,", "planning_work: 0, execution_work: 4,"),
        ("brotli-m1-context-bits-cursor-terminal-undercharged", "advance_planned_context_bits",
            "planning_work: 0, execution_work: 5,", "planning_work: 0, execution_work: 4,"),
        ("brotli-m1-context-count-cursor-skips-terminal-action", "advance_planned_context_tree_count",
            "            let failed_plan = CompressedActionPlan { planning_work: 0, execution_work: 5,\n                consumed: 0, status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState)) };\n            proof { assert(m1_context_cursor_failure_plan(workspace@, window_bytes, failed_plan)); }\n            return ({ let (r_child_result, Ghost(r_child_units)) = execute_fixed_compressed_plan(workspace, window_bytes, budget, phase,\n                &input[..allowed], end_of_input && allowed == input.len(), allowed < input.len(), failed_plan); proof { r_context_wrapper_source_units = r_context_wrapper_source_units + r_child_units; } r_child_result }, Ghost(r_context_wrapper_source_units));\n        },\n        Err(error) => return (Err(CompressedStep { consumed: 0,\n            status: CompressedStatus::Failed(error) }), Ghost(r_context_wrapper_source_units)),",
            "            let failed_plan = CompressedActionPlan { planning_work: 0, execution_work: 5,\n                consumed: 0, status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState)) };\n            proof { assert(m1_context_cursor_failure_plan(workspace@, window_bytes, failed_plan)); }\n            return ({ let (r_child_result, Ghost(r_child_units)) = (Err::<usize, CompressedStep>(CompressedStep { consumed: 0, status: CompressedStatus::Failed(CoreFailure::InvalidFormat(CoreFormatDetail::StateEncoding)) }), Ghost(0nat)); proof { r_context_wrapper_source_units = r_context_wrapper_source_units + r_child_units; } r_child_result }, Ghost(r_context_wrapper_source_units));\n        },\n        Err(error) => return (Err(CompressedStep { consumed: 0,\n            status: CompressedStatus::Failed(error) }), Ghost(r_context_wrapper_source_units)),"),
        ("brotli-m1-context-bits-cursor-plan-wrong-error", "advance_planned_context_bits",
            "status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::InternalState)) };",
            "status: Some(CompressedHeaderStatus::Failed(CompressedHeaderError::Truncated)) };"),
    ] {
        let start = original.find(&format!("fn {function}(")).unwrap();
        let end = start + original[start..].find("\n}\n").unwrap() + 3;
        let selected = &original[start..end];
        let body = selected.find("\n{\n").unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let output = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&output);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        let lower = log.to_ascii_lowercase();
        assert!(!output.status.success(), "prover accepted {name}");
        assert!(lower.contains("postcondition not satisfied") || lower.contains("precondition not satisfied")
            || lower.contains("invariant not satisfied") || lower.contains("assertion failed"),
            "expected semantic rejection for {name}: {log}");
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count"), "tool/resource failure for {name}: {log}");
        println!("REJECTED {name}: deliberate source defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_five_m1_malformed_suffix_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-malformed-suffix-canary-{}",
        std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    fs::create_dir_all(project.join("evidence")).unwrap();
    let path = temporary.join("src/brotli_input.rs");
    let original = fs::read_to_string(&path).unwrap();
    for (name, function, old, new) in [
        ("brotli-m1-malformed-suffix-invalid-fields-undercharge", "plan_initial_suffix_action", "        return (Ok(CompressedActionPlan { planning_work: 0, execution_work: 4 + 1, consumed: 0,", "        return (Ok(CompressedActionPlan { planning_work: 0, execution_work: 4 , consumed: 0,"),
        ("brotli-m1-malformed-suffix-wrong-width-undercharge", "plan_initial_suffix_action", "        return (Ok(CompressedActionPlan { planning_work: 1, execution_work: 1 + 4 + 1, consumed: 0,", "        return (Ok(CompressedActionPlan { planning_work: 1, execution_work: 1 + 4 , consumed: 0,"),
        ("brotli-m1-malformed-suffix-bad-kind-is-truncated", "advance_initial_block_length_phase", "                        return ({ let (r_child_1, Ghost(r_child_units_1)) = self.fail_phase(consumed, CompressedHeaderError::InternalState); proof { r_source_units = r_source_units + r_child_units_1; } r_child_1 }, Ghost(r_source_units));", "                        match state_byte(self.workspace, self.window_bytes, B3B_BLOCK_LENGTH_PHASE) {\n                            Ok(1) => {\n                                return ({ let (r_child_1, Ghost(r_child_units_1)) = self.fail_phase(consumed, CompressedHeaderError::Truncated); proof { r_source_units = r_source_units + r_child_units_1; } r_child_1 }, Ghost(r_source_units));\n                            },\n                            _ => {\n                                return ({ let (r_child_1, Ghost(r_child_units_1)) = self.fail_phase(consumed, CompressedHeaderError::InternalState); proof { r_source_units = r_source_units + r_child_units_1; } r_child_1 }, Ghost(r_source_units));\n                            },\n                        }"),
        ("brotli-m1-malformed-suffix-fallback-undercharge", "advance_planned_compressed_action", "        if !budget.charge_work(4 + 1) {", "        if !budget.charge_work( if initial_outer == 3 { 4 } else { 4 + 1 } ) {"),
        ("brotli-m1-malformed-suffix-fallback-writes-byte175", "advance_planned_compressed_action", "        if { let (r_child_result, Ghost(r_child_units)) = store_terminal_error(workspace, window_bytes, CompressedHeaderError::InternalState); proof { r_header_action_source_units = r_header_action_source_units + r_child_units; } r_child_result }.is_err() {\n            return (Err(CompressedStep { consumed: 0,\n                status: CompressedStatus::Failed(core_state_failure()) }), Ghost(r_header_action_source_units));\n        }", "        if { let (r_child_result, Ghost(r_child_units)) = store_terminal_error(workspace, window_bytes, CompressedHeaderError::InternalState); proof { r_header_action_source_units = r_header_action_source_units + r_child_units; } r_child_result }.is_err() {\n            return (Err(CompressedStep { consumed: 0,\n                status: CompressedStatus::Failed(core_state_failure()) }), Ghost(r_header_action_source_units));\n        }\n        if initial_outer == 3 {\n            let _ = put_state_byte(workspace, window_bytes, 175, 1);\n        }"),
    ] {
        let start = original.find(&format!("fn {function}(")).expect("selected function exists");
        let indent = original[..start].rsplit('\n').next().unwrap().len();
        let closing = format!("\n{}}}\n", " ".repeat(indent));
        let end = start + original[start..].find(&closing).expect("selected function ends") + closing.len();
        let mut selected = original[start..end].to_string();
        let opening = format!("\n{}{{\n", " ".repeat(indent));
        let body = selected.find(&opening).expect("function body");
        if name == "brotli-m1-malformed-suffix-fallback-undercharge" {
            // The admitted outer=3/subphase=2 witness reaches this reservation
            // with five units. The unchanged owner debit requires zero left.
            assert_eq!(old, "        if !budget.charge_work(4 + 1) {");
            assert_eq!(new, "        if !budget.charge_work( if initial_outer == 3 { 4 } else { 4 + 1 } ) {");
            let receipt = "        proof { assert(if (4 + 1) == 5u64 { true } else { false }) by (compute_only); }\n";
            let bad_receipt = "        proof { assert(if (if 3u8 == 3 { 4 } else { 4 + 1 }) == 5u64 { true } else { false }) by (compute_only); }\n";
            assert_eq!(selected[body..].matches(old).count(), 1);
            selected = selected.replacen(old, &format!("{receipt}{old}"), 1);
            fs::write(&path, format!("{}{}{}", &original[..start], selected, &original[end..])).unwrap();
            let positive = check_brotli_input_function(&verus, &temporary, function);
            fs::write(project.join("evidence/positive-brotli-m1-malformed-suffix-fallback-debit.log"), transcript(&positive)).unwrap();
            assert!(positive.status.success(), "unchanged fallback debit positive failed: {}", transcript(&positive));
            assert_eq!(selected[body..].matches(receipt).count(), 1);
            selected = selected.replacen(receipt, bad_receipt, 1);
            let preview = selected.replacen(old, new, 1);
            assert_eq!(preview[body..].matches(bad_receipt).count(), 1);
            assert_eq!(preview[body..].matches(new).count(), 1);
        } else if name == "brotli-m1-malformed-suffix-fallback-writes-byte175" {
            // The checked original frame carries the model byte zero to this
            // reached point. Keep the healthy body free of an extra write.
            let actual_put_value: u8 = new.strip_prefix(old)
                .and_then(|tail| tail.strip_prefix("\n        if initial_outer == 3 {\n            let _ = put_state_byte(workspace, window_bytes, 175, "))
                .and_then(|tail| tail.strip_suffix(");\n        }"))
                .expect("unchanged extra-write guard and target")
                .parse().expect("literal extra-write value");
            assert_eq!(actual_put_value, 1);
            let receipt = "\n        proof { assert(if 0u8 == 0u8 { true } else { false }) by (compute_only); }";
            let bad_receipt = format!("\n        proof {{ assert(if {actual_put_value}u8 == 0u8 {{ true }} else {{ false }}) by (compute_only); }}");
            assert_eq!(selected[body..].matches(old).count(), 1);
            selected = selected.replacen(old, &format!("{old}{receipt}"), 1);
            fs::write(&path, format!("{}{}{}", &original[..start], selected, &original[end..])).unwrap();
            let positive = check_brotli_input_function(&verus, &temporary, function);
            fs::write(project.join("evidence/positive-brotli-m1-malformed-suffix-fallback-byte175.log"), transcript(&positive)).unwrap();
            assert!(positive.status.success(), "unchanged fallback byte positive failed: {}", transcript(&positive));
            assert_eq!(selected[body..].matches(receipt).count(), 1);
            selected = selected.replacen(receipt, bad_receipt.as_str(), 1);
            let preview = selected.replacen(old, new, 1);
            assert_eq!(preview[body..].matches(bad_receipt.as_str()).count(), 1);
            assert_eq!(preview[body..].matches(new).count(), 1);
        }
        let (scope_start, scope_end) = (body, selected.len());
        assert_eq!(selected[scope_start..scope_end].matches(old).count(), 1, "unique body mutation for {name}");
        let replacement = format!("{}{}{}", &selected[..scope_start],
            selected[scope_start..scope_end].replacen(old, new, 1), &selected[scope_end..]);
        assert_eq!(&replacement[..body], &selected[..body], "unchanged root contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed")
            || ((name == "brotli-m1-malformed-suffix-fallback-undercharge"
                || name == "brotli-m1-malformed-suffix-fallback-writes-byte175")
                && log.contains("error: expression simplifies to false")
                && log.contains("by (compute_only)")),
            "expected a proof rejection, not a tooling error: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output") && !lower.contains("internal compiler error"),
            "tool/resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate executable defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}


// Source receipt controls use the unchanged checked source contracts.
// The unchanged whole positive gate below must pass before any mutation is made.
#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_four_m1_actual_source_receipt_omissions() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-m1-source-receipt-canaries-{}", std::process::id()
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for name in [
        "lib.rs", "base64.rs", "percent.rs", "lz4.rs", "brotli_input.rs",
        "brotli_block.rs", "brotli_prefix.rs", "brotli.rs", "brotli_data.rs",
        "brotli_dictionary.rs", "composition_demo.rs",
    ] {
        fs::copy(project.join("src").join(name), temporary.join("src").join(name)).unwrap();
    }
    let whole_positive = Command::new(&verus)
        .arg(temporary.join("src/lib.rs"))
        .args(["--crate-type", "lib", "--no-cheating", "--num-threads", "8",
               "--triggers-mode", "silent", "--rlimit", "300"])
        .current_dir(&temporary)
        .output().expect("run unchanged whole source before receipt mutants");
    assert!(whole_positive.status.success(),
        "unmodified whole source must pass before receipt controls: {}", transcript(&whole_positive));
    for function in ["BitQueue::bit_at", "store_b3b_queue", "execute_fixed_compressed_plan",
                     "advance_serialized_compressed_header"] {
        let positive = check_brotli_input_function(&verus, &temporary, function);
        assert!(positive.status.success(), "unmodified selected root failed: {}", transcript(&positive));
    }
    for (name, function, old, new) in [
    (
        "brotli-m1-r-bit-selection-receipt-omitted",
        "BitQueue::bit_at",
        "proof { source_bit_selections = source_bit_selections + 1; }",
        "proof { source_bit_selections = source_bit_selections + 0; }",
    ),
    (
        "brotli-m1-r-queue-child-receipt-omitted",
        "store_b3b_queue",
        "let (receipt_child_0, Ghost(receipt_child_units_0)) = write_b3b_state_byte(\n            workspace,\n            window_bytes,\n            relative,\n            value,\n        );\n    proof { receipt_units = receipt_units + receipt_child_units_0; }",
        "let (receipt_child_0, Ghost(receipt_child_units_0)) = write_b3b_state_byte(\n            workspace,\n            window_bytes,\n            relative,\n            value,\n        );\n    proof { receipt_units = receipt_units + 0; }",
    ),
    (
        "brotli-m1-r-fixed-owner-child-receipt-omitted",
        "execute_fixed_compressed_plan",
        "proof { r_fixed_owner_source_units = r_fixed_owner_source_units + actual_outer_units; }",
        "proof { r_fixed_owner_source_units = r_fixed_owner_source_units + 0; }",
    ),
    (
        "brotli-m1-r-public-driver-child-receipt-omitted",
        "advance_serialized_compressed_header",
        "proof { r_header_driver_source_units = r_header_driver_source_units + r_child_units; }",
        "proof { r_header_driver_source_units = r_header_driver_source_units + 0; }",
    ),
] {
        let path = temporary.join("src/brotli_input.rs");
        let original = fs::read_to_string(project.join("src/brotli_input.rs")).unwrap();
        assert_eq!(original.matches(old).count(), 1, "unique mutation anchor for {name}");
        fs::write(&path, original.replacen(old, new, 1)).unwrap();
        let result = check_brotli_input_function(&verus, &temporary, function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        fs::write(&path, &original).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("panicked")
            && !lower.contains("internal compiler error")
            && !lower.contains("expected rlimit-count")
            && !lower.contains("unexpected smt output")
            && !lower.contains("resource limit exceeded")
            && !lower.contains("resource limit (rlimit)")
            && !lower.contains("timed out")
            && !lower.contains("timeout"), "proof resources are unresolved, not semantic rejection: {log}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("requires not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"), "expected semantic proof rejection, not tooling failure: {log}");
        println!("REJECTED {name}: omitted actual source receipt, unchanged specification");
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_six_b3c_constructor_binding_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-constructor-canaries-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli.rs");
    let original = fs::read_to_string(&path).unwrap();
    let positive = check_brotli_function(&verus, &temporary, "BrotliDecoder::new");
    assert!(positive.status.success(), "unchanged constructor failed: {}", transcript(&positive));
    let start = original.find("    pub fn new(\n        workspace: &'w mut [u8],").unwrap();
    let end = start + original[start..].find("    pub fn reset(").unwrap();
    let selected = &original[start..end];
    let body = selected.find("\n    {\n").unwrap();
    for (name, old, new) in [
        (
            "brotli-b3c-constructor-skips-initialization-reservation",
            "if !budget.reserve_initialization() {",
            "if false {",
        ),
        (
            "brotli-b3c-constructor-spurious-resource-failure",
            "if !budget.reserve_initialization() {",
            "if true {",
        ),
        (
            "brotli-b3c-constructor-small-workspace-consumes-credit",
            "        if workspace.len() < required {\n            return Err(InitError::WorkspaceTooSmall);\n        }",
            "        if workspace.len() < required {\n            let _ = budget.reserve_initialization();\n            return Err(InitError::WorkspaceTooSmall);\n        }",
        ),
        (
            "brotli-b3c-constructor-replenishes-work",
            "            Ok(()) => Ok(Self { workspace, budget }),",
            "            Ok(()) => {\n                budget.work_remaining = budget.limits.max_work;\n                Ok(Self { workspace, budget })\n            },",
        ),
        (
            "brotli-b3c-constructor-returns-finished-state",
            "            Ok(()) => Ok(Self { workspace, budget }),",
            "            Ok(()) => {\n                let _ = crate::brotli_input::write_b3c_state_byte(\n                    workspace, window_bytes, crate::brotli_input::B3C_STREAM_PHASE, 8);\n                Ok(Self { workspace, budget })\n            },",
        ),
        (
            "brotli-b3c-constructor-small-workspace-is-resource-error",
            "        if workspace.len() < required {\n            return Err(InitError::WorkspaceTooSmall);\n        }",
            "        if workspace.len() < required {\n            return Err(InitError::ResourceLimit);\n        }",
        ),
    ] {
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body anchor for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged constructor contract");
        let mutated = format!("{}{}{}", &original[..start], replacement, &original[end..]);
        fs::write(&path, mutated).unwrap();
        let output = check_brotli_function(&verus, &temporary, "BrotliDecoder::new");
        let log = transcript(&output);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!output.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"), "expected semantic rejection: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output")
            && !lower.contains("internal compiler error") && !lower.contains("error[e"),
            "tool or resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate constructor defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_ten_b3c_atomic_emission_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!(
        "proven-primitives-b3c-emission-canaries-{}", std::process::id(),
    ));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let path = temporary.join("src/brotli.rs");
    let original = fs::read_to_string(&path).unwrap();
    let check = |function: &str| {
        Command::new(&verus).arg(temporary.join("src/lib.rs"))
            .args(["--crate-type", "lib", "--verify-only-module", "brotli",
                "--verify-function", function, "--no-cheating", "--num-threads", "1",
                "--triggers-mode", "silent", "--no-auto-recommends-check", "--rlimit", "300"])
            .current_dir(&temporary).output().expect("run selected pinned Verus emission root")
    };
    for function in ["BrotliDecoder::emit_byte", "BrotliDecoder::emit_uncompressed_byte"] {
        let positive = check(function);
        assert!(positive.status.success(), "unchanged emission root failed: {}", transcript(&positive));
    }
    for (name, function, old, new) in [
        (
            "brotli-b3c-emission-window-byte-disagrees-with-output",
            "BrotliDecoder::emit_byte",
            "        self.workspace[position as usize] = byte;",
            "        self.workspace[position as usize] = byte.wrapping_add(1);",
        ),
        (
            "brotli-b3c-emission-window-position-does-not-advance",
            "BrotliDecoder::emit_byte",
            "            crate::brotli_input::B3C_WINDOW_POSITION,\n                next_position,",
            "            crate::brotli_input::B3C_WINDOW_POSITION,\n                position,",
        ),
        (
            "brotli-b3c-emission-first-history-increment-is-skipped",
            "BrotliDecoder::emit_byte",
            "let next_history = if history < history_limit { history + 1 } else { history };",
            "let next_history = if history == 0 { 0 } else if history < history_limit { history + 1 } else { history };",
        ),
        (
            "brotli-b3c-emission-first-total-increment-is-skipped",
            "BrotliDecoder::emit_byte",
            "total.checked_add(1)",
            "total.checked_add(if total == 0 { 0 } else { 1 })",
        ),
        (
            "brotli-b3c-emission-second-previous-uses-current-byte",
            "BrotliDecoder::emit_byte",
            "            crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE,\n                previous,",
            "            crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE,\n                byte,",
        ),
        (
            "brotli-b3c-emission-meta-remaining-does-not-decrement",
            "BrotliDecoder::emit_byte",
            "            crate::brotli_input::B3C_META_REMAINING,\n                remaining - 1,",
            "            crate::brotli_input::B3C_META_REMAINING,\n                remaining,",
        ),
        (
            "brotli-b3c-emission-writes-unrelated-scratch",
            "BrotliDecoder::emit_byte",
            "        self.workspace[position as usize] = byte;",
            "        self.workspace[position as usize] = byte;\n        self.workspace[window_bytes as usize] = byte;",
        ),
        (
            "brotli-b3c-emission-resource-error-consumes-work",
            "BrotliDecoder::emit_byte",
            "        {\n            return (Err(StreamError::ResourceLimit), Ghost(e3_source_writes));\n        }\n        let window_bytes = self.window_bytes();",
            "        {\n            let _ = self.budget.charge_work(1);\n            return (Err(StreamError::ResourceLimit), Ghost(e3_source_writes));\n        }\n        let window_bytes = self.window_bytes();",
        ),
        (
            "brotli-b3c-emission-resource-error-writes-window",
            "BrotliDecoder::emit_byte",
            "        {\n            return (Err(StreamError::ResourceLimit), Ghost(e3_source_writes));\n        }\n        let window_bytes = self.window_bytes();",
            "        {\n            self.workspace[0] = self.workspace[0].wrapping_add(1);\n            return (Err(StreamError::ResourceLimit), Ghost(e3_source_writes));\n        }\n        let window_bytes = self.window_bytes();",
        ),
        (
            "brotli-b3c-emission-uncompressed-error-writes-window",
            "BrotliDecoder::emit_uncompressed_byte",
            "        (result, Ghost(e3_source_writes))",
            "        if result.is_err() { self.workspace[0] = byte; }\n        (result, Ghost(e3_source_writes))",
        ),
    ] {
        let (begin, following) = if function == "BrotliDecoder::emit_byte" {
            ("    fn emit_byte(", "    fn emit_uncompressed_byte(")
        } else {
            ("    fn emit_uncompressed_byte(", "    fn fail_transition(")
        };
        let start = original.find(begin).unwrap();
        let end = start + original[start..].find(following).unwrap();
        let selected = &original[start..end];
        let body = selected.find("\n    {\n").unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique body anchor for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged emission contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let result = check(function);
        let log = transcript(&result);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!result.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied")
            || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied")
            || log.contains("assertion failed"), "expected semantic rejection: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output")
            && !lower.contains("internal compiler error") && !lower.contains("error[e"),
            "tool or resource failure is not a semantic rejection: {log}");
        println!("REJECTED {name}: deliberate emission defect, unchanged specification");
        fs::write(&path, &original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}

#[test]
#[ignore = "requires VERUS_ROOT pointing at the pinned Verus distribution"]
fn the_prover_rejects_twelve_e3_store_receipt_and_billing_defects() {
    let verus_root = PathBuf::from(std::env::var_os("VERUS_ROOT").expect("set VERUS_ROOT"));
    let verus = verus_root.join(if cfg!(windows) { "verus.exe" } else { "verus" });
    let project = Path::new(env!("CARGO_MANIFEST_DIR"));
    let temporary = std::env::temp_dir().join(format!("proven-primitives-e3-canaries-{}", std::process::id()));
    fs::create_dir(&temporary).expect("fresh private temporary directory");
    fs::create_dir(temporary.join("src")).unwrap();
    for entry in fs::read_dir(project.join("src")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), temporary.join("src").join(entry.file_name())).unwrap();
        }
    }
    let check = |module: &str, function: &str| {
        if module == "input" {
            check_brotli_input_function(&verus, &temporary, function)
        } else {
            Command::new(&verus).arg(temporary.join("src/lib.rs"))
                .args(["--crate-type", "lib", "--verify-only-module", "brotli",
                    "--verify-function", function, "--no-cheating", "--num-threads", "1",
                    "--triggers-mode", "silent", "--rlimit", "300"])
                .current_dir(&temporary).output().expect("run selected pinned Verus emission root")
        }
    };
    for (module, function) in [
        ("input", "write_b3c_state_byte"), ("input", "write_b3c_state_u32"),
        ("input", "write_b3c_state_u64"), ("brotli", "BrotliDecoder::emit_byte"),
        ("brotli", "BrotliDecoder::emit_uncompressed_byte"), ("brotli", "output_block_reason"),
    ] {
        let positive = check(module, function);
        assert!(positive.status.success(), "unchanged E3 root failed: {}", transcript(&positive));
    }
    for (name, module, function, old, new) in [
        ("brotli-e3-write-b3c-state-byte-omits-store-receipt", "input", "write_b3c_state_byte", "workspace[at] = value;\n    proof { e3_source_writes = e3_source_writes + 1; }", "workspace[at] = value;"),
        ("brotli-e3-write-b3c-state-u32-omits-store-receipt", "input", "write_b3c_state_u32", "workspace[at + 3] = (value >> 24) as u8;\n    proof { e3_source_writes = e3_source_writes + 1; }", "workspace[at + 3] = (value >> 24) as u8;"),
        ("brotli-e3-write-b3c-state-u64-omits-store-receipt", "input", "write_b3c_state_u64", "workspace[at + 7] = (value >> 56) as u8;\n    proof { e3_source_writes = e3_source_writes + 1; }", "workspace[at + 7] = (value >> 56) as u8;"),
        ("brotli-e3-output-store-receipt-omitted", "brotli", "BrotliDecoder::emit_byte", "output[produced] = byte;\n        proof { e3_source_writes = e3_source_writes + 1; }", "output[produced] = byte;"),
        ("brotli-e3-window-store-receipt-omitted", "brotli", "BrotliDecoder::emit_byte", "self.workspace[position as usize] = byte;\n        proof { e3_source_writes = e3_source_writes + 1; }", "self.workspace[position as usize] = byte;"),
        ("brotli-e3-byte-child-store-receipt-omitted", "brotli", "BrotliDecoder::emit_byte", "crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE,\n                previous,\n            );\n            proof { e3_source_writes = e3_source_writes + e3_child_writes; }", "crate::brotli_input::B3C_SECOND_PREVIOUS_BYTE,\n                previous,\n            );\n            proof { }"),
        ("brotli-e3-u32-child-store-receipt-omitted", "brotli", "BrotliDecoder::emit_byte", "crate::brotli_input::B3C_WINDOW_POSITION,\n                next_position,\n            );\n            proof { e3_source_writes = e3_source_writes + e3_child_writes; }", "crate::brotli_input::B3C_WINDOW_POSITION,\n                next_position,\n            );\n            proof { }"),
        ("brotli-e3-u64-child-store-receipt-omitted", "brotli", "BrotliDecoder::emit_byte", "crate::brotli_input::B3C_TOTAL_PRODUCED,\n                next_total,\n            );\n            proof { e3_source_writes = e3_source_writes + e3_child_writes; }", "crate::brotli_input::B3C_TOTAL_PRODUCED,\n                next_total,\n            );\n            proof { }"),
        ("brotli-e3-uncompressed-discards-child-receipt", "brotli", "BrotliDecoder::emit_uncompressed_byte", "proof { e3_source_writes = e3_source_writes + e3_child_writes; }", "proof { }"),
        ("brotli-e3-emission-restores-eight-work-debit", "brotli", "BrotliDecoder::emit_byte", "assert!(self.budget.charge_work(B3C_EMISSION_WRITE_WORK));", "assert!(self.budget.charge_work(8));"),
        ("brotli-e3-output-block-check-restores-eight-unit-minimum", "brotli", "output_block_reason", "if output_remaining == 0 || work_remaining < B3C_EMISSION_WRITE_WORK {", "if output_remaining == 0 || work_remaining < 8 {"),
        ("brotli-e3-debit-moved-after-first-output-write", "brotli", "BrotliDecoder::emit_byte", "assert!(self.budget.charge_work(B3C_EMISSION_WRITE_WORK));\n        proof {\n            assert(e3_source_writes == 0);\n            assert(self.budget.work_remaining as nat + B3C_EMISSION_WRITE_WORK as nat\n                == old(self).budget.work_remaining as nat);\n        }\n        output[produced] = byte;", "proof {\n            assert(e3_source_writes == 0);\n            assert(self.budget.work_remaining as nat + B3C_EMISSION_WRITE_WORK as nat\n                == old(self).budget.work_remaining as nat);\n        }\n        output[produced] = byte;\n        assert!(self.budget.charge_work(B3C_EMISSION_WRITE_WORK));"),
    ] {
        let (file, begin, following, marker) = if module == "input" {
            match function {
                "write_b3c_state_byte" => ("brotli_input.rs", "pub(crate) fn write_b3c_state_byte(", "pub(crate) open spec fn b3c_scalar_u16_at", "\n{\n"),
                "write_b3c_state_u32" => ("brotli_input.rs", "pub(crate) fn write_b3c_state_u32(", "proof fn decode_b3c_u64_le", "\n{\n"),
                "write_b3c_state_u64" => ("brotli_input.rs", "pub(crate) fn write_b3c_state_u64(", "pub(crate) fn initialize_serialized_b3c(", "\n{\n"),
                _ => unreachable!(),
            }
        } else {
            match function {
                "BrotliDecoder::emit_byte" => ("brotli.rs", "    fn emit_byte(", "    fn emit_uncompressed_byte(", "\n    {\n"),
                "BrotliDecoder::emit_uncompressed_byte" => ("brotli.rs", "    fn emit_uncompressed_byte(", "    fn fail_transition(", "\n    {\n"),
                "output_block_reason" => ("brotli.rs", "fn output_block_reason(", "pub struct RequestLimits", "\n{\n"),
                _ => unreachable!(),
            }
        };
        let path = temporary.join("src").join(file);
        let original = fs::read_to_string(project.join("src").join(file)).unwrap();
        let start = original.find(begin).unwrap();
        let end = start + original[start..].find(following).unwrap();
        let selected = &original[start..end];
        let body = selected.find(marker).unwrap();
        assert_eq!(selected[body..].matches(old).count(), 1, "unique E3 body anchor for {name}");
        let replacement = format!("{}{}", &selected[..body], selected[body..].replacen(old, new, 1));
        assert_eq!(&replacement[..body], &selected[..body], "unchanged E3 contract");
        fs::write(&path, format!("{}{}{}", &original[..start], replacement, &original[end..])).unwrap();
        let output = check(module, function);
        let log = transcript(&output);
        fs::write(project.join("evidence").join(format!("canary-{name}.log")), &log).unwrap();
        assert!(!output.status.success(), "prover accepted {name}");
        assert!(log.contains("postcondition not satisfied") || log.contains("precondition not satisfied")
            || log.contains("invariant not satisfied") || log.contains("assertion failed"),
            "expected semantic rejection: {log}");
        let lower = log.to_ascii_lowercase();
        assert!(!lower.contains("resource limit") && !lower.contains("panicked")
            && !lower.contains("expected rlimit-count") && !lower.contains("unexpected smt output")
            && !lower.contains("internal compiler error") && !lower.contains("error[e"),
            "tool or resource failure is not semantic rejection: {log}");
        println!("REJECTED {name}: actual reached-store receipt or debit defect, unchanged specification");
        fs::write(&path, original).unwrap();
    }
    fs::remove_dir_all(temporary).unwrap();
}
