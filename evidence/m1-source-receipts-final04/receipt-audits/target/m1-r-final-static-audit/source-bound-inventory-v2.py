"""Full executable-body structural inventory, never proof of cost equality."""
from pathlib import Path
import hashlib
import json
import re
import sys
from audit_tools import close, definitions, mask_code

root, output = map(Path, sys.argv[1:])
defs = definitions(root)
named = {}
for d in defs:
    named.setdefault(d["name"], []).append(d)


def resolve(caller, body, start, name):
    candidates = named[name]
    pre = body[max(0, start - 100):start]
    if re.search(r"\bself\.\s*$", pre):
        matches = [d for d in candidates if d["module"] == caller["module"] and d["impl"] == caller["impl"]]
    elif re.search(r"crate::brotli_prefix::\s*$", pre):
        matches = [d for d in candidates if d["module"] == "brotli_prefix" and not d["impl"]]
    elif name in ["read_bits", "bit_at"]:
        matches = [d for d in candidates if d["impl"] == "BitQueue"]
    elif name == "advance_field" and caller["name"] in ["plan_code_description_field", "advance_serialized_tree"]:
        matches = [d for d in candidates if d["impl"] == "CodeDescriptionDecoder"]
    elif name == "advance_field" and caller["name"] == "advance_serialized_meta_header":
        matches = [d for d in candidates if d["impl"] == "MetaBlockDecoder"]
    else:
        method = re.search(r"(\w+)::\s*$", pre)
        matches = ([d for d in candidates if d["impl"] == method.group(1)] if method else
                   [d for d in candidates if not d["impl"] and d["module"] == caller["module"]])
    return matches if len(matches) == 1 else candidates if len(candidates) == 1 else matches or candidates


rows, discarded, ambiguous, findings = [], [], [], []
for d in defs:
    body = d["body"]
    masked = mask_code(body)
    paired_edges, ordinary_edges = [], []
    for call in re.finditer(r"\b(\w+)\s*\(", masked):
        name = call.group(1)
        if name not in named:
            continue
        resolved = resolve(d, body, call.start(), name)
        opening = masked.index("(", call.start())
        end = close(body, opening) + 1
        edge = dict(callee=name, resolved_callees=[v["id"] for v in resolved],
                    source_line=d["body_line"] + body[:call.start()].count("\n"),
                    receipt_discarded_by_projection=bool(re.match(r"\s*\.0\b", body[end:])))
        if len(resolved) != 1:
            ambiguous.append(dict(caller=d["id"], **edge))
        if any(v["paired"] for v in resolved):
            paired_edges.append(edge)
            if d["paired"] and edge["receipt_discarded_by_projection"]:
                discarded.append(dict(caller=d["id"], **edge))
        else:
            ordinary_edges.append(edge)
    if d["paired"]:
        # Definite unused single-occurrence bindings only. This cannot establish
        # that a repeated/shadowed binding is added to the correct producer.
        for binding in re.finditer(r"\blet\b[^;=]*\bGhost\((\w+)\)[^;=]*=", masked):
            var = binding.group(1)
            if len(re.findall(r"\b" + re.escape(var) + r"\b", masked)) == 1:
                findings.append(dict(caller=d["id"], kind="unused_receipt_binding", variable=var))
        produced = set()
        for ghost in re.finditer(r"\bGhost\(([^()]+)\)", masked):
            produced.update(re.findall(r"\b[A-Za-z_]\w*\b", ghost.group(1)))
        for var in sorted(produced - {"nat", "u64", "u32", "u16", "u8"}):
            # Crucially do not confuse logical ==, ==> etc. with assignment.
            pattern = r"\b" + re.escape(var) + r"\s*(?::\s*nat\s*)?=(?!=|>)\s*([^;]+);"
            for assignment in re.finditer(pattern, masked):
                expression = body[assignment.start(1):assignment.end(1)].strip()
                if re.search(r"\b(?:planning_work|execution_work|work_remaining|source_work|reserved_work)\b", expression):
                    findings.append(dict(caller=d["id"], kind="producer_assignment_needs_review", variable=var,
                                         expression=expression,
                                         source_line=d["body_line"] + body[:assignment.start()].count("\n")))
    rows.append({k: d[k] for k in ["id", "module", "impl", "name", "line", "body_line", "paired", "sha256"]} |
                dict(composite_receipt_edges=paired_edges, ordinary_exec_edges=ordinary_edges))

report = dict(
    source_sha256={f"src/{m}.rs": hashlib.sha256((root / "src" / f"{m}.rs").read_bytes()).hexdigest()
                   for m in ["brotli_input", "brotli_prefix"]},
    audit_kind="Full executable-body structural audit; retained bindings are not proof of receipt equality.",
    supersedes="Original structural-inventory.json body slicing and additional-static-pattern-audit.json assignment scan.",
    paired_function_count=sum(d["paired"] for d in defs),
    ambiguous_exec_edges=ambiguous, discarded_receipts_inside_paired_functions=discarded,
    pattern_findings=findings, functions=rows,
)
output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ["paired_function_count", "discarded_receipts_inside_paired_functions", "pattern_findings"]}, indent=2))
