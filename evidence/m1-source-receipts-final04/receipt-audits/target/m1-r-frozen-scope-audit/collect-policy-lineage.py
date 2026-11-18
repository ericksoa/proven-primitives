"""Retain exact policy excerpts and earlier-repair evidence without approval inference."""
from pathlib import Path
import datetime
import hashlib
import json

base = Path(__file__).resolve().parent
repo = base.parents[1]
policy = [
    ("BROTLI_B3B_PROPOSAL.md", 64, 80, "W1 ordinary interface and retained terminal states", "proposal policy"),
    ("BROTLI_B3B_PROPOSAL.md", 231, 235, "Permanent invalid values and terminal no-further-effects rule", "proposal policy"),
    ("BROTLI_B3B_W1_ADDENDUM.md", 1, 19, "E1 status record and invalid serialized tags cause terminal InternalState", "approval record and proposal policy text; no approval inferred by this audit"),
    ("BROTLI_B3B_W1_ADDENDUM.md", 91, 106, "Existing terminal tag and detail encoding", "proposal policy"),
    ("BROTLI_B3B_W1_ADDENDUM.md", 121, 127, "Existing InternalState/public invalid-format mapping", "proposal policy"),
    ("BROTLI_B3B_W1_ADDENDUM.md", 160, 175, "Existing W1 permanent-error stopping condition", "proposal policy"),
    ("BROTLI_B3B_W1_ADDENDUM.md", 374, 388, "Existing module ownership and no-new-public-interface boundary", "proposal boundary"),
    ("BROTLI_B3B_W1_ADDENDUM.md", 513, 527, "E2 private-helper limits, including unchanged status/effects/work and human boundary", "proposal boundary; not authority for an unverified architectural decision"),
    ("BROTLI_B3C_PROPOSAL.md", 1, 20, "C1 status record and fixed architecture/dependency/trust boundary", "approval record and proposal policy text; no approval inferred by this audit"),
    ("BROTLI_B3C_PROPOSAL.md", 191, 194, "Exact reservation before mutation and existing component refinement", "proposal policy"),
    ("BROTLI_B3C_PROPOSAL.md", 443, 449, "Malformed input is not NeedInput; sticky failure/reset-only recovery", "proposal policy"),
    ("BROTLI_B3C_PROPOSAL.md", 458, 467, "Existing terminal-call and call-credit priority", "proposal policy"),
    ("BROTLI_B3C_PROPOSAL.md", 474, 505, "Existing425 initialization and source-unit/prepayment rules", "proposal policy"),
    ("BROTLI_B3C_METERING_ADDENDUM.md", 1, 40, "M1 status record, unchanged W1 interface, B3c ownership and exact read-only planning/reservation", "approval record and proposal policy text; no approval inferred by this audit"),
    ("BROTLI_B3C_METERING_ADDENDUM.md", 588, 603, "Earlier analogous saved-cursor terminal5 repair", "later implementation checkpoint prose; not a new human approval record"),
    ("BROTLI_M1_TRANSITION_RULE_DECISION.md", 28, 37, "Existing separate nested-reset transition unit; scratch bookkeeping zero", "proposal policy"),
]
excerpts = []
for path, start, end, purpose, kind in policy:
    p = repo / path
    data = p.read_bytes()
    snapshot = base / "policy-sources" / path
    snapshot.parent.mkdir(exist_ok=True)
    snapshot.write_bytes(data)
    excerpts.append(dict(path=path, source_sha256=hashlib.sha256(data).hexdigest(),
                         lines=[start, end], purpose=purpose, source_kind=kind,
                         exact_text="\n".join(data.decode().splitlines()[start-1:end])))

record_paths = [
    "evidence/m1-source-ledgers-review01/source-start.json",
    "evidence/m1-source-ledgers-review02/source-start.json",
    "evidence/m1-source-ledgers-review05/source-start.json",
    "target/m1-context-cursor-owner-fix/evidence/context-cursor-owner-fix-result.json",
    "target/m1-context-cursor-owner-fix/evidence/before-fix-runtime-attempt02.log",
    "target/m1-context-cursor-owner-fix/evidence/after-fix-runtime.log",
    "target/m1-context-cursor-owner-fix/context-cursor-owner-fix.patch",
    "target/m1-suffix-closure-agent/evidence-manifest.json",
    "target/m1-suffix-closure-agent/malformed-suffix-closure.patch",
]
records = []
for path in record_paths:
    p = repo / path
    data = p.read_bytes()
    out = base / "prior-evidence" / path
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(data)
    records.append(dict(path=path, sha256=hashlib.sha256(data).hexdigest(),
                        fs_mtime_utc=datetime.datetime.fromtimestamp(p.stat().st_mtime, datetime.timezone.utc).isoformat()))

context = json.loads((repo / record_paths[3]).read_text())
checks = {}
for key in ["before", "after"]:
    data = (repo / context["regression"][key]).read_bytes()
    checks[key + "_hash_matches_record"] = hashlib.sha256(data).hexdigest() == context["regression"][key + "_sha256"]
for key in ["source_patch", "test_patch"]:
    checks[key + "_hash_matches_record"] = hashlib.sha256((repo / context[key]).read_bytes()).hexdigest() == context[key + "_sha256"]
checks["retained_context_clone_source_hash_matches_record"] = hashlib.sha256((repo / "target/m1-context-cursor-owner-fix/src/brotli_input.rs").read_bytes()).hexdigest() == context["source_input_sha256"]
assert all(checks.values())

report = dict(
    status="Read-only retained policy/source evidence; no assertion of fresh human approval.",
    policy_excerpts=excerpts, retained_prior_evidence=records,
    prior_context_repair=dict(source_sha256=context["source_input_sha256"],
                             finished_utc=context["finished_utc"], regression=context["regression"],
                             retained_hash_checks=checks,
                             historical_result_only=True, fresh_test_or_proof_run=False),
    timing=[
        dict(label="f1a source tar-member modification", utc="2026-11-17T01:31:49.309370+00:00"),
        dict(label="review02 manifest started on exact frozen f1a/prefix112 pair", utc="2026-11-17T01:40:00.189929+00:00"),
        dict(label="isolated context cursor repair finished, per retained manifest", utc=context["finished_utc"]),
        dict(label="e10c source tar-member modification", utc="2026-11-17T04:43:41.122485+00:00"),
        dict(label="review05 manifest started on actual pre-R e10c baseline", utc="2026-11-17T04:45:04.979304+00:00"),
    ],
    distinction=[
        "The400-mismatch cursor repair is already present in the archived e10c pre-R source. It is an earlier M1 admitted-state refinement repair, not a runtime effect introduced by R receipt transport.",
        "The exact f1a and e10c snapshots each have322 ordinary executable helpers and zero explicit Approach R paired returns. Their prefix bytes match the proposal's112d frozen hash.",
        "The two changed owners now use the previously existing W1 terminal action and existing B3c-owned terminal5 reservation. Existing policy text requires permanent internal-state failure and exact prepayment. No new terminal tag/status, storage layout, public/private helper interface, module ownership, dependency/tool or unit classification is introduced by this delta.",
        "This observation does not substitute for the required human verification of architectural decisions or approve a mismatch with a frozen-source decision. The proposal f1a and actual e10c baselines remain distinct evidence identities.",
        "C1's four-unit public terminal escrow and M1's four-byte-plus-one-transition private terminal5 are separately recorded policies; the audit does not conflate or change either.",
    ],
    timing_limit="Tar member mtimes and retained manifest timestamps are historical recorded metadata; they are not human approval times.",
)
(base / "policy-and-earlier-repair-lineage.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(dict(policy_excerpts=len(excerpts), retained_prior_files=len(records),
                      prior_hashes_verified=all(checks.values()), prior_regression=context["regression"]), indent=2))
