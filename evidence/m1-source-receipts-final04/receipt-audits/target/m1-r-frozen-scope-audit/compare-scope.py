"""Exact retained pre-R source comparison. Static only; no approval inference."""
from pathlib import Path
import collections
import difflib
import hashlib
import json
import re
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "m1-r-final-static-audit"))
from audit_tools import close, declarations, definitions, mask_code

base = Path(__file__).resolve().parent
roots = {"f1a": base / "frozen-f1a", "e10c": base / "baseline-e10c"}
norm = lambda s: re.sub(r"\s+", "", mask_code(s))


def all_items(root):
    rows = {}
    for d in declarations(root):
        source = (root / "src" / f"{d['module']}.rs").read_text().split("\n#[cfg(test)]", 1)[0]
        masked = mask_code(source)
        op = masked.index("(", d["start"])
        end_args = close(source, op)
        first_brace = masked.index("{", end_args)
        clauses = re.search(r"\b(?:requires|ensures|decreases|recommends|returns)\b", masked[end_args:first_brace])
        if clauses is None:
            opening = first_brace
        else:
            indentation = 4 if d["impl"] else 0
            m = re.search(r"(?m)^" + " " * indentation + r"\{", masked[end_args:])
            assert m, d["id"]
            opening = end_args + m.start() + indentation
        end = close(source, opening, "{", "}") + 1
        header, body = source[d["start"]:opening], source[opening:end]
        declaration_rx = r"(?m)^[ \t]*(?:(?:pub(?:\([^)]*\))?|open|closed|spec|proof|exec|broadcast)\s+)*fn\s+\w+\s*(?:<[^\n(]*>)?\s*\("
        assert not re.search(declaration_rx, mask_code(source[end_args:opening])), (d["id"], "swallowed header")
        assert not re.search(declaration_rx, mask_code(body[1:-1])), (d["id"], "swallowed body")
        rows[d["id"]] = dict(d, header=header, body=body,
                             full_sha256=hashlib.sha256((header + body).encode()).hexdigest())
    return rows


def projected_body(s):
    """Read-only source projection, not compiler erasure/equivalence proof."""
    mask = mask_code(s)
    edits = []
    for m in re.finditer(r"\bproof\s*\{", mask):
        op = mask.index("{", m.start())
        edits.append((m.start(), close(s, op, "{", "}") + 1))
    for m in re.finditer(r"\blet\s+(?:ghost|tracked)\b", mask):
        if any(a <= m.start() < z for a, z in edits): continue
        end = mask.find(";", m.end())
        assert end >= 0
        edits.append((m.start(), end + 1))
    for m in re.finditer(r"\b(?:reveal|hide|reveal_with_fuel)\s*\(", mask):
        if any(a <= m.start() < z for a, z in edits): continue
        op = mask.index("(", m.start())
        end = close(s, op) + 1
        while end < len(s) and s[end].isspace(): end += 1
        if end < len(s) and s[end] == ";": end += 1
        edits.append((m.start(), end))
    for m in re.finditer(r"(?m)^(?P<indent>[ \t]*)while\b", mask):
        if any(a <= m.start() < z for a, z in edits): continue
        opening = re.search(r"(?m)^" + re.escape(m.group("indent")) + r"\{", mask[m.end():])
        assert opening, "while body"
        op = m.end() + opening.start() + len(m.group("indent"))
        spec = re.search(r"\b(?:invariant|invariant_except_break|decreases)\b", mask[m.end():op])
        if spec:
            edits.append((m.end() + spec.start(), op))
    for a, z in sorted(edits, reverse=True):
        if any(x < a and z <= y for x, y in edits): continue
        s = s[:a] + s[z:]
    return s


old, new = (all_items(roots[k]) for k in ["f1a", "e10c"])
model_rows = [dict(id=n, f1a_line=d["line"], e10c_line=new[n]["line"],
                   f1a_header_sha256=hashlib.sha256(d["header"].encode()).hexdigest(),
                   e10c_header_sha256=hashlib.sha256(new[n]["header"].encode()).hexdigest(),
                   f1a_body_sha256=hashlib.sha256(d["body"].encode()).hexdigest(),
                   e10c_body_sha256=hashlib.sha256(new[n]["body"].encode()).hexdigest(),
                   normalized_header_and_body_preserved=norm(d["header"] + d["body"]) == norm(new[n]["header"] + new[n]["body"]))
              for n, d in old.items() if d["kind"] == "spec" and n in new]
(base / "preexisting-model-body-audit.json").write_text(json.dumps(model_rows, indent=2) + "\n")
(base / "preexisting-helper-ids.json").write_text(json.dumps(sorted(n for n, d in old.items() if d["kind"] == "exec"), indent=2) + "\n")
added = sorted(set(new) - set(old))
removed = sorted(set(old) - set(new))
spec_changes = [n for n in old.keys() & new.keys() if old[n]["kind"] == "spec"
                and norm(old[n]["header"] + old[n]["body"]) != norm(new[n]["header"] + new[n]["body"])]
proof_changes = [n for n in old.keys() & new.keys() if old[n]["kind"] == "proof"
                 and norm(old[n]["header"] + old[n]["body"]) != norm(new[n]["header"] + new[n]["body"])]
runtime_changes, exec_changes = [], []
for identity in sorted(old.keys() & new.keys()):
    a, b = old[identity], new[identity]
    if a["kind"] != "exec": continue
    header_changed = norm(a["header"]) != norm(b["header"])
    body_changed = norm(a["body"]) != norm(b["body"])
    attrs_changed = [x["text"] for x in a["attributes"]] != [x["text"] for x in b["attributes"]]
    projected_a, projected_b = projected_body(a["body"]), projected_body(b["body"])
    runtime_changed = norm(projected_a) != norm(projected_b)
    if header_changed or body_changed or attrs_changed:
        row = dict(id=identity, f1a_line=a["line"], e10c_line=b["line"],
                   contract_changed=header_changed, proof_or_runtime_body_changed=body_changed,
                   projected_runtime_body_changed=runtime_changed,
                   f1a_attributes=[x["text"] for x in a["attributes"]],
                   e10c_attributes=[x["text"] for x in b["attributes"]])
        exec_changes.append(row)
    if runtime_changed:
        runtime_changes.append(identity)
        out = base / "projected-runtime-diffs" / (identity.replace("::", "__") + ".diff")
        out.parent.mkdir(exist_ok=True)
        out.write_text("".join(difflib.unified_diff(projected_a.splitlines(True), projected_b.splitlines(True),
                                                 fromfile="f1a/" + identity, tofile="e10c/" + identity)))

def graph(label):
    data = json.loads((base / f"{label}-exec-graph.json").read_text())
    return {(d["id"], callee) for d in data["functions"]
            for edge in d["ordinary_exec_edges"] + d["composite_receipt_edges"]
            for callee in edge["resolved_callees"]}

g0, g1 = graph("f1a"), graph("e10c")
preservation = json.loads((base / "ordinary-interface-preservation.json").read_text())
report = dict(
    status="read-only exact-byte comparison, not human approval or a new validation run",
    frozen_proposal_input_sha256=hashlib.sha256((roots["f1a"] / "src/brotli_input.rs").read_bytes()).hexdigest(),
    actual_pre_R_baseline_input_sha256=hashlib.sha256((roots["e10c"] / "src/brotli_input.rs").read_bytes()).hexdigest(),
    proposal_prefix_and_both_archived_prefix_sha256=hashlib.sha256((roots["f1a"] / "src/brotli_prefix.rs").read_bytes()).hexdigest(),
    core_counts={label: dict(collections.Counter(d["kind"] for d in items.values())) for label, items in [("f1a", old), ("e10c", new)]},
    preexisting_exec_helpers=len([d for d in old.values() if d["kind"] == "exec"]),
    removed_declarations=removed,
    new_declarations=[dict(id=n, kind=new[n]["kind"], e10c_line=new[n]["line"],
                           attributes=[x["text"] for x in new[n]["attributes"]]) for n in added],
    changed_existing_spec_definitions=sorted(spec_changes), changed_existing_proof_functions=sorted(proof_changes),
    ordinary_arguments_requires_return_and_old_guarantees_preservation=preservation["passed"],
    ordinary_interface_preservation_violations=preservation["violations"],
    changed_existing_exec_declarations=exec_changes,
    changed_projected_runtime_functions=runtime_changes,
    runtime_projection_limit="Explicit proof blocks, ghost/tracked declarations, reveal/hide calls, loop invariants/decreases, comments and whitespace are removed only for static comparison. No compiler erasure or semantic equivalence check was run.",
    helper_graph=dict(exec_ids_unchanged=True, old_edge_pairs=len(g0), new_edge_pairs=len(g1),
                      added_edges=[dict(caller=a, callee=b) for a, b in sorted(g1 - g0)],
                      removed_edges=[dict(caller=a, callee=b) for a, b in sorted(g0 - g1)],
                      limit="Exec-name call graph from exact complete function bodies; one preexisting reset receiver ambiguity is retained in both graphs."),
    observations=[
        "f1a and e10c are distinct retained pre-R source states; neither archive contains explicit Approach R return pairs.",
        "The only ordinary runtime body changes are two existing B3c context-cursor owners. Their StateEncoding planner rejection now selects existing Literal/DistanceContextMap phase, builds existing CompressedActionPlan terminal5, and invokes existing execute_fixed_compressed_plan/W1. Before: direct error, no terminal image or work debit. After: exact five-unit reservation before terminal writes, or ResourceLimit with unchanged workspace/budget on short credit.",
        "No ordinary function node is added/removed. Ordinary arguments, return types, requirements and all previous guarantees are retained across322 helpers. Thirteen existing exec contracts gain guarantees; one additional exec body changes only proof visibility; install_completed_simple_tree gains spinoff_prover.",
        "Eight input-private spec definitions and four proof functions are added for malformed suffix/context domains and owner effects. All416 existing spec definitions and all313 existing proof functions retain exact normalized bodies/signatures under this declaration scanner. These additions are not Approach R receipt carriers.",
        "Across43 archived source/test/config files, only input.rs and proof_rejection.rs differ. Prefix, all other modules, dependencies, toolchain configs, fixture data and workspace representations are byte-identical.",
        "The runtime call graph changes within existing input-private helpers. The changed owners use the existing B3c reservation owner, existing terminal plan representation and existing W1 mutator. No new cross-module boundary, module, runtime/dependency, signature, representation, unit constant, reset charge or public/W1 interface appears in this delta.",
        "Whether an actual source mismatch is covered by a human approval is not decided here. The proposal's f1a frozen scope and the actual e10c preimplementation baseline remain separately identified; this evidence does not rewrite either or confer approval.",
    ],
)
(base / "scope-comparison.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ["core_counts", "changed_existing_spec_definitions", "changed_existing_proof_functions", "ordinary_arguments_requires_return_and_old_guarantees_preservation", "changed_projected_runtime_functions", "helper_graph"]}, indent=2))
