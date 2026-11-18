import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "tools" / "pipeline.py"
SPEC = importlib.util.spec_from_file_location("proven_pipeline", SCRIPT)
pipeline = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(pipeline)


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


class GateFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "src").mkdir()
        (self.root / "normative").mkdir()
        (self.root / "evidence" / "runs" / "run-1").mkdir(parents=True)
        (self.root / "src" / "lib.rs").write_text("verified source\n")
        (self.root / "normative" / "contract.txt").write_text("all bytes admitted\n")
        (self.root / "Cargo.lock").write_text("locked\n")
        (self.root / "artifact.bin").write_bytes(b"compiled")
        (self.root / "review.txt").write_text("independent review\n")

        closure = pipeline.freeze_paths(self.root, ["normative/contract.txt"])
        self.profile = {
            "schema_version": 1,
            "profile_id": "Profile",
            "version": "1.0.0",
            "parent": None,
            "obligations": [{
                "id": "BOUNDS",
                "revision": "1",
                "applicability": "all",
                "bindings": ["proof::root"],
                "required_evidence": ["checked-proof"],
            }],
            "admitted_domains": ["all byte slices and capacities"],
            "models": ["rust-slice-model-v1"],
            "assumptions": ["valid Rust references"],
            "trusted_components": ["Verus", "Z3", "Rust/LLVM"],
            "capability_predicates": ["stateless-byte-transform"],
            "required_evidence": ["checked-proof", "raw-receipt"],
            "supported_families": ["primitive"],
            "approval_refs": ["human-approval"],
            "review_refs": ["review.txt"],
            "closure": closure,
        }
        self.profile_path = self.root / "profile.json"
        write_json(self.profile_path, self.profile)

        self.approval = {
            "schema_version": 1,
            "approval_id": "approval-1",
            "human": "human@example.com",
            "approved_at": "2026-10-24T00:00:00Z",
            "scope": "Profile 1.0.0",
            "proposal_commit": "0123456789abcdef",
        }
        self.approval_path = self.root / "approval.json"
        write_json(self.approval_path, self.approval)

        self.source_closure = pipeline.freeze_paths(self.root, ["src/lib.rs"])
        artifact_digest = pipeline.sha256_file(self.root / "artifact.bin")
        self.inventory = {
            "schema_version": 1,
            "source_revision": "revision-1",
            "objects": [{
                "id": "primitive-1",
                "kind": "primitive",
                "source_digest": self.source_closure["digest"],
                "artifact_digest": artifact_digest,
                "capabilities": ["stateless-byte-transform"],
                "advertised_supported": True,
                "profile_id": "Profile",
                "profile_version": "1.0.0",
            }],
        }
        self.inventory_path = self.root / "inventory.json"
        write_json(self.inventory_path, self.inventory)

        self.raw_path = self.root / "evidence" / "runs" / "run-1" / "verification.json"
        write_json(self.raw_path, {
            "verification-results": {
                "success": True,
                "verified": 1,
                "errors": 0,
                "is-verifying-entire-crate": True,
            },
            "times-ms": {"smt": {"smt-run-module-times": [{
                "function-breakdown": [{"function": "proof::root", "success": True}]
            }]}},
        })
        (self.raw_path.parent / "stderr.txt").write_text("")
        self.receipt = {
            "schema_version": 1,
            "run_id": "run-1",
            "subject_id": "primitive-1",
            "profile_digest": closure["digest"],
            "approval_digest": pipeline.sha256_file(self.approval_path),
            "source_digest": self.source_closure["digest"],
            "artifact_digest": artifact_digest,
            "dependencies_digest": pipeline.sha256_file(self.root / "Cargo.lock"),
            "verifier": {
                "name": "Verus",
                "version": "pinned",
                "binary_sha256": "0" * 64,
            },
            "options": list(pipeline.VERUS_OPTIONS),
            "entire_crate": True,
            "outcome": "checked",
            "theorem_bindings": ["proof::root"],
            "raw_receipts": [
                "evidence/runs/run-1/verification.json",
                "evidence/runs/run-1/stderr.txt",
            ],
            "target": "aarch64-apple-darwin",
            "trusted_components": ["Verus", "Z3", "Rust/LLVM"],
            "controls": {"positive": "passed"},
        }
        self.receipt_path = self.raw_path.parent / "receipt.json"
        write_json(self.receipt_path, self.receipt)
        self.coverage = pipeline.derive_coverage(self.profile, self.inventory, [self.receipt])
        self.coverage_path = self.root / "coverage.json"
        write_json(self.coverage_path, self.coverage)
        self.manifest = {
            "schema_version": 1,
            "release_id": "release-1",
            "source_revision": "revision-1",
            "source_closure": self.source_closure,
            "artifact": self.entry("artifact.bin"),
            "inventory": self.entry("inventory.json"),
            "profile": self.entry("profile.json"),
            "approval": self.entry("approval.json"),
            "coverage": self.entry("coverage.json"),
            "receipts": [self.entry("evidence/runs/run-1/receipt.json")],
            "dependencies": self.entry("Cargo.lock"),
            "build": {"target": "aarch64-apple-darwin", "recipe": "cargo --locked --release"},
            "verifier_expectation": {
                "name": "Verus",
                "version": "pinned",
                "binary_sha256": "0" * 64,
                "options": list(pipeline.VERUS_OPTIONS),
                "target": "aarch64-apple-darwin",
            },
            "trusted_components": ["Verus", "Z3", "Rust/LLVM"],
            "independent_review": {
                "status": "approved",
                "reviewer": "independent human",
                "report_sha256": pipeline.sha256_file(self.root / "review.txt"),
                "scope": "contract and applicability",
            },
        }
        self.profile_expected = pipeline.sha256_file(self.profile_path)
        self.approval_expected = pipeline.sha256_file(self.approval_path)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def entry(self, relative: str) -> dict:
        return {"path": relative, "sha256": pipeline.sha256_file(self.root / relative)}

    def gate(self, profile_digest: str | None = None, approval_digest: str | None = None) -> None:
        pipeline.gate_release(
            self.root,
            self.manifest,
            profile_digest or self.profile_expected,
            approval_digest or self.approval_expected,
        )

    def refresh_receipt(self) -> None:
        write_json(self.receipt_path, self.receipt)
        self.manifest["receipts"] = [self.entry("evidence/runs/run-1/receipt.json")]

    def test_valid_exact_evidence_passes(self) -> None:
        self.gate()

    def test_omitted_new_obligation_denies(self) -> None:
        self.coverage["rows"] = []
        write_json(self.coverage_path, self.coverage)
        self.manifest["coverage"] = self.entry("coverage.json")
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_invented_not_applicable_denies(self) -> None:
        self.coverage["rows"][0]["applicable"] = False
        self.coverage["rows"][0]["status"] = "not_applicable"
        write_json(self.coverage_path, self.coverage)
        self.manifest["coverage"] = self.entry("coverage.json")
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_stale_source_after_pass_denies(self) -> None:
        (self.root / "src" / "lib.rs").write_text("changed after proof\n")
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_retargeted_profile_denies(self) -> None:
        with self.assertRaises(pipeline.PipelineError):
            self.gate(profile_digest="f" * 64)

    def test_absent_no_cheating_denies(self) -> None:
        self.receipt["options"].remove("--no-cheating")
        self.refresh_receipt()
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_partial_verification_denies(self) -> None:
        self.receipt["entire_crate"] = False
        self.refresh_receipt()
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_forged_checked_outcome_denies(self) -> None:
        write_json(self.raw_path, {
            "verification-results": {
                "success": False,
                "verified": 0,
                "errors": 1,
                "is-verifying-entire-crate": True,
            }
        })
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_changed_lockfile_denies(self) -> None:
        (self.root / "Cargo.lock").write_text("changed dependency\n")
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_narrowed_domain_denies(self) -> None:
        original_expected = self.profile_expected
        self.profile["admitted_domains"] = ["inputs shorter than four bytes"]
        write_json(self.profile_path, self.profile)
        self.manifest["profile"] = self.entry("profile.json")
        with self.assertRaises(pipeline.PipelineError):
            self.gate(profile_digest=original_expected)

    def test_deleting_failing_supported_object_denies(self) -> None:
        self.inventory["objects"][0]["advertised_supported"] = False
        write_json(self.inventory_path, self.inventory)
        self.manifest["inventory"] = self.entry("inventory.json")
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_test_only_evidence_denies(self) -> None:
        self.receipt["theorem_bindings"] = []
        self.refresh_receipt()
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_forged_theorem_binding_denies(self) -> None:
        self.receipt["theorem_bindings"] = ["proof::different"]
        self.refresh_receipt()
        with self.assertRaises(pipeline.PipelineError):
            self.gate()

    def test_unknown_schema_field_denies(self) -> None:
        bad = copy.deepcopy(self.inventory)
        bad["untrusted_success_claim"] = True
        with self.assertRaises(pipeline.PipelineError):
            pipeline.validate_inventory(bad)

    def test_manifest_path_escape_denies(self) -> None:
        self.manifest["artifact"]["path"] = "../outside.bin"
        with self.assertRaises(pipeline.PipelineError):
            self.gate()


if __name__ == "__main__":
    unittest.main()
