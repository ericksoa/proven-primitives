"""Target-only static readers; these do not invoke Verus or execute mutants."""
from pathlib import Path
import functools
import hashlib
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "m1-r-metered-fields"))
import receipt_tools

receipt_tools.mask_code = functools.lru_cache(maxsize=8)(receipt_tools.mask_code)
mask_code = receipt_tools.mask_code
close = receipt_tools.close


def definitions(root):
    result = []
    for module in ["brotli_input", "brotli_prefix"]:
        path = Path(root) / "src" / f"{module}.rs"
        source = path.read_text().split("\n#[cfg(test)]", 1)[0]
        masked = mask_code(source)
        impls = []
        for m in re.finditer(r"\bimpl(?:<[^>]*>)?\s+(\w+)(?:<[^>]*>)?\s*\{", masked):
            opening = masked.index("{", m.start())
            line_start = source.rfind("\n", 0, m.start()) + 1
            impl_indent = len(source[line_start:m.start()])
            impls.append((m.start(), close(source, opening, "{", "}") + 1, m.group(1), impl_indent))
        pattern = r"(?m)^(?P<indent>[ \t]*)(?:pub(?:\([^)]*\))?\s+)?fn\s+(?P<name>\w+)\s*\("
        for m in re.finditer(pattern, source):
            start = m.start()
            impl_match = next(((name, indent) for a, z, name, indent in impls if a <= start < z), None)
            owner = impl_match[0] if impl_match else ""
            # A contract may itself contain standalone opening braces. Only the
            # brace at executable indentation starts the body. The frozen W1
            # source has impl declarations at columns 0 and 8 whose bodies are
            # indented four spaces. Derive method indentation from its impl,
            # independently of a method's declaration indentation.
            declaration_indent = m.group("indent")
            body_indent = " " * (impl_match[1] + 4) if impl_match else declaration_indent
            parameters_opening = masked.index("(", m.start())
            parameters_end = close(source, parameters_opening)
            first_brace = masked.index("{", parameters_end)
            clause = re.search(r"\b(?:requires|ensures|decreases|recommends|returns)\b",
                               masked[parameters_end:first_brace])
            if clause is None:
                # Ordinary no-contract helpers can put their body brace on the
                # signature line, e.g. map_meta_error(...) -> CoreFailure {.
                opening = first_brace
            else:
                body_pattern = r"(?m)^" + re.escape(body_indent) + r"\{"
                body_match = re.search(body_pattern, masked[m.end():])
                if not body_match:
                    raise ValueError((module, m.group("name"), "no executable body"))
                opening = m.end() + body_match.start() + len(body_indent)
            end = close(source, opening, "{", "}") + 1
            header, body = source[start:opening], source[opening:end]
            name = m.group("name")
            any_declaration = r"(?m)^[ \t]*(?:(?:pub(?:\([^)]*\))?|open|closed|uninterp|spec|proof|exec|broadcast)\s+)*fn\s+\w+\s*(?:<[^\n(]*>)?\s*\("
            if re.search(any_declaration, mask_code(header[m.end()-start:])):
                raise ValueError((module, name, "header swallowed another function declaration"))
            if re.search(any_declaration, mask_code(body[1:-1])):
                raise ValueError((module, name, "span swallowed another exec function"))
            result.append(dict(
                id=f"{module}::" + (owner + "::" if owner else "") + name,
                impl=owner, module=module, name=name,
                line=source[:start].count("\n") + 1,
                body_line=source[:opening].count("\n") + 1,
                start=start, opening=opening, end=end,
                declaration_indent=len(declaration_indent), body_indent=len(body_indent),
                header=header, body=body,
                paired=bool(re.search(r"->\s*\(\s*\w+\s*:\s*\(.*Ghost<nat>", header, re.S)),
                sha256=hashlib.sha256(source[start:end].encode()).hexdigest(),
            ))
    return result


def selected(root, selector, module="brotli_input"):
    parts = selector.split("::")
    name = parts[-1]
    owner = parts[-2] if len(parts) > 1 else ""
    candidates = [d for d in definitions(root) if d["module"] == module and d["name"] == name
                  and (not owner or d["impl"] == owner)]
    if len(candidates) != 1:
        raise ValueError((module, selector, [d["id"] for d in candidates]))
    return candidates[0]


def declarations(root):
    """All exec/spec/proof declarations with exact attached attribute spans.

    Attributes may be separated from the declaration by whitespace/comments.
    This intentionally does not infer intended attachments from source history.
    """
    result = []
    for module in ["brotli_input", "brotli_prefix"]:
        source = (Path(root) / "src" / f"{module}.rs").read_text().split("\n#[cfg(test)]", 1)[0]
        masked = mask_code(source)
        impls = []
        for m in re.finditer(r"\bimpl(?:<[^>]*>)?\s+(\w+)(?:<[^>]*>)?\s*\{", masked):
            opening = masked.index("{", m.start())
            impls.append((m.start(), close(source, opening, "{", "}") + 1, m.group(1)))
        prefix = r"(?:(?:pub(?:\([^)]*\))?|open|closed|uninterp|spec|proof|exec|broadcast)\s+)*"
        pattern = r"(?m)^[ \t]*(?P<prefix>" + prefix + r")fn\s+(?P<name>\w+)\s*(?:<[^\n(]*>)?\s*\("
        for m in re.finditer(pattern, masked):
            owner = next((name for a, z, name in impls if a <= m.start() < z), "")
            attrs = []
            before = m.start()
            while True:
                cursor = before - 1
                while cursor >= 0 and masked[cursor].isspace():
                    cursor -= 1
                if cursor < 0 or masked[cursor] != "]":
                    break
                end = cursor + 1
                depth = 0
                while cursor >= 0:
                    if masked[cursor] == "]": depth += 1
                    elif masked[cursor] == "[":
                        depth -= 1
                        if depth == 0: break
                    cursor -= 1
                if cursor <= 0 or masked[cursor - 1] != "#":
                    break
                start = cursor - 1
                attrs.insert(0, dict(start=start, end=end, text=source[start:end],
                                     line=source[:start].count("\n") + 1))
                before = start
            name = m.group("name")
            result.append(dict(id=f"{module}::" + (owner + "::" if owner else "") + name,
                               module=module, impl=owner, name=name,
                               kind="spec" if "spec" in m.group("prefix").split() else
                                    "proof" if "proof" in m.group("prefix").split() else "exec",
                               start=m.start(), line=source[:m.start()].count("\n") + 1,
                               attributes=attrs))
    ids = [d["id"] for d in result]
    if len(ids) != len(set(ids)):
        raise ValueError("ambiguous declaration ids")
    return result
