#!/usr/bin/env python3
"""Fail-closed local evidence pipeline for Proven Primitives.

This is bookkeeping and evidence collection. It never grants human approval,
changes security contracts, or converts tests into proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


SCHEMA_VERSION = 1
CAPABILITIES = {
    "stateless-byte-transform",
    "complete-buffer-decoder",
    "retained-input-parser",
    "output-producing-streaming-decoder",
    "caller-adapter",
    "request-resource-policy",
}
PROOF_OUTCOMES = {"checked", "violated", "unresolved"}
PROCESS_OUTCOMES = {"not_applicable", "approval_missing", "review_missing"}
VERUS_OPTIONS = [
    "--crate-type", "lib", "--no-cheating", "--num-threads", "1",
    "--triggers-mode", "silent", "--rlimit", "60", "--time", "--output-json",
]
IDENTIFIER = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._/-]{0,127}$")


class PipelineError(RuntimeError):
    pass


def fail(message: str) -> None:
    raise PipelineError(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"cannot read strict JSON {path}: {exc}")
    if not isinstance(value, dict):
        fail(f"top-level JSON must be an object: {path}")
    return value


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def strict(value: dict[str, Any], required: set[str], optional: set[str], where: str) -> None:
    missing = required - value.keys()
    unknown = value.keys() - required - optional
    if missing:
        fail(f"{where}: missing fields {sorted(missing)}")
    if unknown:
        fail(f"{where}: unknown fields {sorted(unknown)}")


def require_schema(value: dict[str, Any], where: str) -> None:
    if value.get("schema_version") != SCHEMA_VERSION:
        fail(f"{where}: unsupported schema_version")


def require_id(value: Any, where: str) -> str:
    if not isinstance(value, str) or not IDENTIFIER.fullmatch(value) or ".." in value:
        fail(f"{where}: invalid identifier")
    return value


def require_digest(value: Any, where: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
        fail(f"{where}: expected lowercase SHA-256")
    return value


def require_string_list(value: Any, where: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        fail(f"{where}: expected string list")
    if len(value) != len(set(value)):
        fail(f"{where}: duplicate entries")
    return value


def safe_path(root: Path, value: Any, where: str) -> Path:
    if not isinstance(value, str):
        fail(f"{where}: expected relative path")
    relative = Path(value)
    if relative.is_absolute() or ".." in relative.parts:
        fail(f"{where}: path escapes root")
    resolved_root = root.resolve()
    path = (resolved_root / relative).resolve()
    if not path.is_relative_to(resolved_root):
        fail(f"{where}: path escapes root")
    return path


def closure_digest(entries: list[dict[str, str]]) -> str:
    payload = "".join(
        entry["path"] + "\0" + entry["sha256"] + "\n"
        for entry in sorted(entries, key=lambda item: item["path"])
    ).encode()
    return sha256_bytes(payload)


def freeze_paths(root: Path, names: list[str]) -> dict[str, Any]:
    entries: list[dict[str, str]] = []
    seen: set[str] = set()
    root = root.resolve()
    for name in sorted(names):
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            fail(f"closure path escapes root: {name}")
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            fail(f"closure input is not a file under root: {name}")
        normalized = relative.as_posix()
        if normalized in seen:
            fail(f"duplicate closure path: {normalized}")
        seen.add(normalized)
        entries.append({"path": normalized, "sha256": sha256_file(path)})
    return {
        "algorithm": "sorted-path-nul-sha256-newline",
        "entries": entries,
        "digest": closure_digest(entries),
    }


def validate_closure(value: Any, root: Path, where: str) -> str:
    if not isinstance(value, dict):
        fail(f"{where}: closure must be an object")
    strict(value, {"algorithm", "entries", "digest"}, set(), where)
    if value["algorithm"] != "sorted-path-nul-sha256-newline":
        fail(f"{where}: unsupported closure algorithm")
    if not isinstance(value["entries"], list) or not value["entries"]:
        fail(f"{where}: closure entries must be nonempty")
    checked: list[dict[str, str]] = []
    seen: set[str] = set()
    for index, entry in enumerate(value["entries"]):
        if not isinstance(entry, dict):
            fail(f"{where}.entries[{index}]: expected object")
        strict(entry, {"path", "sha256"}, set(), f"{where}.entries[{index}]")
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            fail(f"{where}: closure path escapes root")
        normalized = relative.as_posix()
        if normalized in seen:
            fail(f"{where}: duplicate closure path")
        seen.add(normalized)
        digest = require_digest(entry["sha256"], f"{where}:{normalized}")
        path = (root.resolve() / relative).resolve()
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            fail(f"{where}: missing closure file {normalized}")
        if sha256_file(path) != digest:
            fail(f"{where}: stale or changed closure file {normalized}")
        checked.append({"path": normalized, "sha256": digest})
    expected = closure_digest(checked)
    if require_digest(value["digest"], f"{where}.digest") != expected:
        fail(f"{where}: closure digest mismatch")
    return expected


def validate_profile(profile: dict[str, Any], root: Path) -> None:
    strict(
        profile,
        {
            "schema_version", "profile_id", "version", "parent", "obligations",
            "admitted_domains", "models", "assumptions", "trusted_components",
            "capability_predicates", "required_evidence", "supported_families",
            "approval_refs", "review_refs", "closure",
        },
        set(),
        "profile",
    )
    require_schema(profile, "profile")
    require_id(profile["profile_id"], "profile.profile_id")
    require_id(profile["version"], "profile.version")
    if profile["parent"] is not None:
        require_digest(profile["parent"], "profile.parent")
    for field in (
        "admitted_domains", "models", "assumptions", "trusted_components",
        "required_evidence", "supported_families", "approval_refs", "review_refs",
    ):
        require_string_list(profile[field], f"profile.{field}")
    predicates = set(require_string_list(profile["capability_predicates"], "profile.capability_predicates"))
    if not predicates <= CAPABILITIES:
        fail(f"profile: unknown capability predicates {sorted(predicates - CAPABILITIES)}")
    if not isinstance(profile["obligations"], list) or not profile["obligations"]:
        fail("profile.obligations: expected nonempty list")
    seen: set[tuple[str, str]] = set()
    for index, obligation in enumerate(profile["obligations"]):
        if not isinstance(obligation, dict):
            fail(f"profile.obligations[{index}]: expected object")
        strict(
            obligation,
            {"id", "revision", "applicability", "bindings", "required_evidence"},
            set(),
            f"profile.obligations[{index}]",
        )
        key = (
            require_id(obligation["id"], "obligation.id"),
            require_id(obligation["revision"], "obligation.revision"),
        )
        if key in seen:
            fail("profile.obligations: duplicate obligation revision")
        seen.add(key)
        applicability = obligation["applicability"]
        if applicability != "all" and applicability not in predicates:
            fail(f"obligation {key[0]}: unknown applicability predicate")
        require_string_list(obligation["bindings"], f"obligation {key[0]}.bindings")
        require_string_list(obligation["required_evidence"], f"obligation {key[0]}.required_evidence")
    validate_closure(profile["closure"], root, "profile.closure")


def validate_inventory(inventory: dict[str, Any]) -> None:
    strict(inventory, {"schema_version", "source_revision", "objects"}, set(), "inventory")
    require_schema(inventory, "inventory")
    require_id(inventory["source_revision"], "inventory.source_revision")
    if not isinstance(inventory["objects"], list):
        fail("inventory.objects: expected list")
    seen: set[str] = set()
    for index, item in enumerate(inventory["objects"]):
        if not isinstance(item, dict):
            fail(f"inventory.objects[{index}]: expected object")
        strict(
            item,
            {
                "id", "kind", "source_digest", "artifact_digest", "capabilities",
                "advertised_supported", "profile_id", "profile_version",
            },
            set(),
            f"inventory.objects[{index}]",
        )
        object_id = require_id(item["id"], "inventory object id")
        if object_id in seen:
            fail("inventory.objects: duplicate id")
        seen.add(object_id)
        if item["kind"] not in {"primitive", "composition"}:
            fail(f"inventory object {object_id}: invalid kind")
        require_digest(item["source_digest"], f"inventory object {object_id}.source_digest")
        require_digest(item["artifact_digest"], f"inventory object {object_id}.artifact_digest")
        capabilities = set(require_string_list(item["capabilities"], f"inventory object {object_id}.capabilities"))
        if not capabilities <= CAPABILITIES:
            fail(f"inventory object {object_id}: unknown capabilities")
        if not isinstance(item["advertised_supported"], bool):
            fail(f"inventory object {object_id}: advertised_supported must be boolean")
        for field in ("profile_id", "profile_version"):
            if item[field] is not None:
                require_id(item[field], f"inventory object {object_id}.{field}")


def validate_case(case: dict[str, Any]) -> None:
    strict(
        case,
        {
            "schema_version", "case_id", "advisories", "mechanism", "classification",
            "obligation_ids", "regressions", "negative_controls", "approval_status",
        },
        set(),
        "case",
    )
    require_schema(case, "case")
    require_id(case["case_id"], "case.case_id")
    if case["classification"] not in {"new_class", "stronger_obligation", "existing_class"}:
        fail("case.classification: invalid value")
    if case["approval_status"] not in {"proposed", "approved"}:
        fail("case.approval_status: invalid value")
    if not isinstance(case["mechanism"], str) or not case["mechanism"].strip():
        fail("case.mechanism: required")
    for field in ("obligation_ids", "regressions", "negative_controls"):
        require_string_list(case[field], f"case.{field}")
    if not isinstance(case["advisories"], list) or not case["advisories"]:
        fail("case.advisories: expected nonempty list")
    for index, advisory in enumerate(case["advisories"]):
        strict(advisory, {"url", "sha256"}, set(), f"case.advisories[{index}]")
        if not isinstance(advisory["url"], str) or not advisory["url"].startswith("https://"):
            fail("case advisory URL must use https")
        require_digest(advisory["sha256"], "case advisory sha256")


def validate_receipt(receipt: dict[str, Any]) -> None:
    strict(
        receipt,
        {
            "schema_version", "run_id", "subject_id", "profile_digest",
            "approval_digest", "source_digest", "artifact_digest", "dependencies_digest",
            "verifier", "options", "entire_crate", "outcome", "theorem_bindings",
            "raw_receipts", "target", "trusted_components", "controls",
        },
        set(),
        "receipt",
    )
    require_schema(receipt, "receipt")
    require_id(receipt["run_id"], "receipt.run_id")
    require_id(receipt["subject_id"], "receipt.subject_id")
    for field in ("profile_digest", "approval_digest", "source_digest", "artifact_digest", "dependencies_digest"):
        require_digest(receipt[field], f"receipt.{field}")
    if not isinstance(receipt["verifier"], dict):
        fail("receipt.verifier: expected object")
    strict(receipt["verifier"], {"name", "version", "binary_sha256"}, set(), "receipt.verifier")
    require_digest(receipt["verifier"]["binary_sha256"], "receipt.verifier.binary_sha256")
    options = require_string_list(receipt["options"], "receipt.options")
    if options != VERUS_OPTIONS:
        fail("receipt.options: verifier options differ from the approved allowlist")
    if receipt["entire_crate"] is not True:
        fail("receipt.entire_crate: partial verification is not accepted")
    if receipt["outcome"] not in PROOF_OUTCOMES:
        fail("receipt.outcome: invalid proof outcome")
    require_string_list(receipt["theorem_bindings"], "receipt.theorem_bindings")
    require_string_list(receipt["raw_receipts"], "receipt.raw_receipts")
    require_string_list(receipt["trusted_components"], "receipt.trusted_components")
    if not isinstance(receipt["controls"], dict):
        fail("receipt.controls: expected object")


def applicable(obligation: dict[str, Any], item: dict[str, Any]) -> bool:
    predicate = obligation["applicability"]
    return predicate == "all" or predicate in item["capabilities"]


def derive_coverage(profile: dict[str, Any], inventory: dict[str, Any], receipts: list[dict[str, Any]]) -> dict[str, Any]:
    by_subject: dict[str, list[dict[str, Any]]] = {}
    for receipt in receipts:
        validate_receipt(receipt)
        by_subject.setdefault(receipt["subject_id"], []).append(receipt)
    rows: list[dict[str, Any]] = []
    for item in inventory["objects"]:
        if not item["advertised_supported"]:
            continue
        for obligation in profile["obligations"]:
            applies = applicable(obligation, item)
            matching = [
                receipt for receipt in by_subject.get(item["id"], [])
                if receipt["profile_digest"] == profile["closure"]["digest"]
                and receipt["source_digest"] == item["source_digest"]
                and set(obligation["bindings"]) <= set(receipt["theorem_bindings"])
            ]
            checked = any(receipt["outcome"] == "checked" for receipt in matching)
            rows.append({
                "subject_id": item["id"],
                "obligation_id": obligation["id"],
                "revision": obligation["revision"],
                "applicable": applies,
                "status": "checked" if applies and checked else (
                    "unresolved" if applies else "not_applicable"
                ),
                "rationale": "approved capability predicate matched" if applies else (
                    f"missing approved capability {obligation['applicability']}"
                ),
            })
    return {
        "schema_version": SCHEMA_VERSION,
        "profile_digest": profile["closure"]["digest"],
        "inventory_digest": sha256_bytes(json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode()),
        "rows": rows,
    }


def gate_release(root: Path, manifest: dict[str, Any], expected_profile: str, expected_approval: str) -> None:
    strict(
        manifest,
        {
            "schema_version", "release_id", "source_revision", "source_closure",
            "artifact", "inventory", "profile", "approval", "coverage", "receipts",
            "dependencies", "build", "verifier_expectation", "trusted_components",
            "independent_review",
        },
        set(),
        "release manifest",
    )
    require_schema(manifest, "release manifest")
    require_id(manifest["release_id"], "release manifest.release_id")
    require_id(manifest["source_revision"], "release manifest.source_revision")
    source_digest = validate_closure(manifest["source_closure"], root, "release.source_closure")
    for name in ("artifact", "inventory", "profile", "approval", "coverage", "dependencies"):
        entry = manifest[name]
        strict(entry, {"path", "sha256"}, set(), f"release.{name}")
        path = safe_path(root, entry["path"], f"release.{name}.path")
        digest = require_digest(entry["sha256"], f"release.{name}.sha256")
        if not path.is_file() or sha256_file(path) != digest:
            fail(f"release.{name}: missing or stale file")
    if manifest["profile"]["sha256"] != expected_profile:
        fail("gate: profile digest differs from human-provided expected digest")
    if manifest["approval"]["sha256"] != expected_approval:
        fail("gate: approval digest differs from human-provided expected digest")
    profile = read_json(root / manifest["profile"]["path"])
    validate_profile(profile, root)
    inventory = read_json(root / manifest["inventory"]["path"])
    validate_inventory(inventory)
    approval = read_json(root / manifest["approval"]["path"])
    strict(approval, {"schema_version", "approval_id", "human", "approved_at", "scope", "proposal_commit"}, set(), "approval")
    require_schema(approval, "approval")
    coverage = read_json(root / manifest["coverage"]["path"])
    strict(coverage, {"schema_version", "profile_digest", "inventory_digest", "rows"}, set(), "coverage")
    require_schema(coverage, "coverage")
    if coverage["profile_digest"] != profile["closure"]["digest"]:
        fail("gate: coverage targets a different profile")
    inventory_digest = sha256_bytes(json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode())
    if coverage["inventory_digest"] != inventory_digest:
        fail("gate: coverage targets stale inventory")
    receipt_values: list[dict[str, Any]] = []
    verifier_expectation = manifest["verifier_expectation"]
    strict(
        verifier_expectation,
        {"name", "version", "binary_sha256", "options", "target"},
        set(),
        "release.verifier_expectation",
    )
    require_digest(verifier_expectation["binary_sha256"], "release.verifier_expectation.binary_sha256")
    if require_string_list(verifier_expectation["options"], "release.verifier_expectation.options") != VERUS_OPTIONS:
        fail("gate: expected verifier options differ from the approved allowlist")
    if not isinstance(manifest["receipts"], list):
        fail("release.receipts: expected list")
    for index, entry in enumerate(manifest["receipts"]):
        strict(entry, {"path", "sha256"}, set(), f"release.receipts[{index}]")
        path = safe_path(root, entry["path"], f"release.receipts[{index}].path")
        if not path.is_file() or sha256_file(path) != require_digest(entry["sha256"], "receipt sha256"):
            fail("gate: missing or stale receipt")
        receipt = read_json(path)
        validate_receipt(receipt)
        if receipt["approval_digest"] != expected_approval:
            fail("gate: receipt approval mismatch")
        if receipt["profile_digest"] != profile["closure"]["digest"]:
            fail("gate: receipt profile mismatch")
        if receipt["verifier"] != {
            "name": verifier_expectation["name"],
            "version": verifier_expectation["version"],
            "binary_sha256": verifier_expectation["binary_sha256"],
        }:
            fail("gate: verifier identity differs from release expectation")
        if receipt["target"] != verifier_expectation["target"]:
            fail("gate: verification target differs from release expectation")
        for raw_name in receipt["raw_receipts"]:
            raw_path = safe_path(root, raw_name, "receipt.raw_receipts")
            if not raw_path.is_file():
                fail("gate: raw verification receipt missing")
        if receipt["outcome"] == "checked":
            proof_json = read_json(safe_path(root, receipt["raw_receipts"][0], "receipt proof JSON"))
            results = proof_json.get("verification-results")
            if not isinstance(results, dict):
                fail("gate: checked receipt lacks verifier results")
            if results.get("success") is not True or results.get("errors") != 0:
                fail("gate: forged checked outcome")
            if results.get("is-verifying-entire-crate") is not True:
                fail("gate: raw verifier result is partial")
            checked_roots = {
                function.get("function")
                for module in proof_json.get("times-ms", {}).get("smt", {}).get("smt-run-module-times", [])
                for function in module.get("function-breakdown", [])
                if function.get("success") is True
            }
            if not set(receipt["theorem_bindings"]) <= checked_roots:
                fail("gate: claimed theorem binding is absent from successful verifier roots")
        receipt_values.append(receipt)
    expected_coverage = derive_coverage(profile, inventory, receipt_values)
    if coverage != expected_coverage:
        fail("gate: coverage is incomplete, stale, or invented")
    for row in coverage["rows"]:
        if row["applicable"] and row["status"] != "checked":
            fail(f"gate: unresolved applicable obligation {row['subject_id']}:{row['obligation_id']}")
    advertised = {item["id"] for item in inventory["objects"] if item["advertised_supported"]}
    covered = {row["subject_id"] for row in coverage["rows"]}
    if advertised != covered:
        fail("gate: a supported object was omitted from coverage")
    artifact_digest = manifest["artifact"]["sha256"]
    if any(
        item["advertised_supported"] and item["artifact_digest"] != artifact_digest
        for item in inventory["objects"]
    ):
        fail("gate: a supported object is bound to a different shipped artifact")
    if any(
        item["advertised_supported"] and item["source_digest"] != source_digest
        for item in inventory["objects"]
    ):
        fail("gate: a supported object is bound to a different source closure")
    if manifest["dependencies"]["sha256"] != sha256_file(root / "Cargo.lock"):
        fail("gate: locked dependencies changed")
    artifact = safe_path(root, manifest["artifact"]["path"], "release.artifact.path")
    if not artifact.is_file():
        fail("gate: shipped artifact missing")
    if not isinstance(manifest["build"], dict) or not manifest["build"].get("target"):
        fail("gate: build identity missing")
    require_string_list(manifest["trusted_components"], "release.trusted_components")
    review = manifest["independent_review"]
    strict(review, {"status", "reviewer", "report_sha256", "scope"}, set(), "release.independent_review")
    if review["status"] != "approved" or not review["reviewer"]:
        fail("gate: independent specification review missing")
    require_digest(review["report_sha256"], "release.independent_review.report_sha256")
    if source_digest != manifest["source_closure"]["digest"]:
        fail("gate: source closure mismatch")


def command_inventory(args: argparse.Namespace) -> None:
    value = read_json(Path(args.file))
    validate_inventory(value)
    print(json.dumps({"objects": len(value["objects"]), "valid": True}, sort_keys=True))


def command_case(args: argparse.Namespace) -> None:
    value = read_json(Path(args.file))
    validate_case(value)
    print(json.dumps({"case_id": value["case_id"], "valid": True}, sort_keys=True))


def command_freeze(args: argparse.Namespace) -> None:
    write_json(Path(args.output), freeze_paths(Path(args.root), args.paths))


def command_coverage(args: argparse.Namespace) -> None:
    root = Path(args.root)
    profile = read_json(Path(args.profile))
    inventory = read_json(Path(args.inventory))
    validate_profile(profile, root)
    validate_inventory(inventory)
    receipts = [read_json(Path(path)) for path in args.receipts]
    write_json(Path(args.output), derive_coverage(profile, inventory, receipts))


def command_gate(args: argparse.Namespace) -> None:
    expected_profile = require_digest(args.expected_profile_digest, "expected profile digest")
    expected_approval = require_digest(args.expected_approval_digest, "expected approval digest")
    gate_release(Path(args.root), read_json(Path(args.manifest)), expected_profile, expected_approval)
    print(json.dumps({"gate": "pass", "manifest": args.manifest}, sort_keys=True))


def command_verify(args: argparse.Namespace) -> None:
    root = Path(args.root).resolve()
    job = read_json(Path(args.job))
    strict(
        job,
        {
            "schema_version", "run_id", "subject_id", "profile_digest",
            "approval_digest", "source_digest", "artifact_digest", "dependencies_digest",
            "theorem_bindings", "target", "trusted_components", "verifier_version",
        },
        set(),
        "verification job",
    )
    require_schema(job, "verification job")
    run_id = require_id(job["run_id"], "verification job.run_id")
    for field in ("profile_digest", "approval_digest", "source_digest", "artifact_digest", "dependencies_digest"):
        require_digest(job[field], f"verification job.{field}")
    verus_root = Path(os.environ.get("VERUS_ROOT", ""))
    verus = verus_root / ("verus.exe" if os.name == "nt" else "verus")
    if not verus.is_file():
        fail("verify: VERUS_ROOT does not contain the approved verifier")
    version = subprocess.run([str(verus), "--version"], cwd=root, check=True, capture_output=True, text=True).stdout.strip()
    if version != job["verifier_version"]:
        fail("verify: verifier version differs from frozen job")
    command = [str(verus), "src/lib.rs", *VERUS_OPTIONS]
    completed = subprocess.run(command, cwd=root, capture_output=True, text=True)
    run_dir = root / "evidence" / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=False)
    raw_path = run_dir / "verification.json"
    raw_path.write_text(completed.stdout)
    (run_dir / "stderr.txt").write_text(completed.stderr)
    outcome = "checked" if completed.returncode == 0 else "unresolved"
    receipt = {
        "schema_version": SCHEMA_VERSION,
        "run_id": run_id,
        "subject_id": require_id(job["subject_id"], "verification job.subject_id"),
        "profile_digest": job["profile_digest"],
        "approval_digest": job["approval_digest"],
        "source_digest": job["source_digest"],
        "artifact_digest": job["artifact_digest"],
        "dependencies_digest": job["dependencies_digest"],
        "verifier": {"name": "Verus", "version": version, "binary_sha256": sha256_file(verus)},
        "options": VERUS_OPTIONS,
        "entire_crate": True,
        "outcome": outcome,
        "theorem_bindings": require_string_list(job["theorem_bindings"], "verification job.theorem_bindings"),
        "raw_receipts": [str(raw_path.relative_to(root)), str((run_dir / "stderr.txt").relative_to(root))],
        "target": job["target"],
        "trusted_components": require_string_list(job["trusted_components"], "verification job.trusted_components"),
        "controls": {},
    }
    write_json(run_dir / "receipt.json", receipt)
    print(json.dumps({"outcome": outcome, "receipt": str(run_dir / "receipt.json")}, sort_keys=True))
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    inventory = commands.add_parser("inventory")
    inventory.add_argument("--file", required=True)
    inventory.set_defaults(handler=command_inventory)
    case = commands.add_parser("case")
    case.add_argument("--file", required=True)
    case.set_defaults(handler=command_case)
    freeze = commands.add_parser("freeze")
    freeze.add_argument("--root", default=".")
    freeze.add_argument("--output", required=True)
    freeze.add_argument("paths", nargs="+")
    freeze.set_defaults(handler=command_freeze)
    coverage = commands.add_parser("coverage")
    coverage.add_argument("--root", default=".")
    coverage.add_argument("--profile", required=True)
    coverage.add_argument("--inventory", required=True)
    coverage.add_argument("--receipt", dest="receipts", action="append", default=[])
    coverage.add_argument("--output", required=True)
    coverage.set_defaults(handler=command_coverage)
    gate = commands.add_parser("gate")
    gate.add_argument("--root", default=".")
    gate.add_argument("--manifest", required=True)
    gate.add_argument("--expected-profile-digest", required=True)
    gate.add_argument("--expected-approval-digest", required=True)
    gate.set_defaults(handler=command_gate)
    verify = commands.add_parser("verify")
    verify.add_argument("--root", default=".")
    verify.add_argument("--job", required=True)
    verify.set_defaults(handler=command_verify)
    return result


def main() -> int:
    try:
        args = parser().parse_args()
        args.handler(args)
        return 0
    except PipelineError as exc:
        print(f"DENY: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
