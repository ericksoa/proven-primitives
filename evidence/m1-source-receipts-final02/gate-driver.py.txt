#!/usr/bin/env python3
"""Pinned P1 final R evidence gate. This driver does not claim M1 completion."""
from pathlib import Path
import argparse
import concurrent.futures
import datetime
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
TOOL = Path('/Users/aerickson/Documents/NemoDev/formal-verification-pilot-2026-10-23/tools/verus-arm64-macos')
INPUT_NAMES = ['prior37-control-manifest.json', 'affected-suites.json',
               'baseline-five-control-updates.json', 'original-suite-inventory.json',
               'original-driver.py.txt', 'RESTORE_CANARIES.txt', 'frozen-scope-audit.json']
RUNTIME = [
    ('runtime-library', ['cargo', 'test', '--locked', '--release', '--lib']),
    ('runtime-primitives', ['cargo', 'test', '--locked', '--release', '--test', 'primitives']),
    ('runtime-comparison', ['cargo', 'test', '--locked', '--release', '--test', 'upstream_comparison']),
    ('runtime-trust', ['cargo', 'test', '--locked', '--release', '--test', 'proof_rejection',
                       'project_source_contains_no_proof_trust_bypasses', '--', '--exact']),
]
WHOLE = [str(TOOL / 'verus'), 'src/lib.rs', '--crate-type', 'lib', '--no-cheating',
         '--num-threads', '8', '--triggers-mode', 'silent', '--rlimit', '300',
         '--trace', '--time', '--output-json']
ENV_KEYS = ['DEVELOPER_DIR', 'RUSTUP_TOOLCHAIN', 'VERUS_ROOT', 'RUSTFLAGS',
            'CARGO_ENCODED_RUSTFLAGS', 'RUSTDOCFLAGS', 'CARGO_BUILD_TARGET',
            'CARGO_TARGET_DIR', 'RUSTC', 'RUSTDOC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER']

class GateError(RuntimeError):
    pass

def need(condition, message):
    if not condition:
        raise GateError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def file_hash(path):
    return digest(Path(path).read_bytes())

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)

def source_snapshot(root):
    files = []
    for folder in ['src', 'tests', 'benches']:
        files.extend(p for p in (root / folder).rglob('*') if p.is_file())
    files.extend(root / name for name in ['Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml'])
    for name in ['build.rs', '.cargo/config', '.cargo/config.toml']:
        if (root / name).is_file():
            files.append(root / name)
    need(all(p.is_file() for p in files), 'Missing frozen source/build input')
    return {str(p.relative_to(root)): file_hash(p) for p in sorted(set(files))}

def input_snapshot():
    return {name: file_hash(HERE / name) for name in INPUT_NAMES}

def tool_snapshot(env):
    paths = {name: TOOL / name for name in ['verus', 'rust_verify', 'z3']}
    paths['python'] = Path(sys.executable)
    for name in ['cargo', 'rustup']:
        launcher = shutil.which(name, path=env.get('PATH'))
        need(launcher, 'Cannot resolve tool launcher: ' + name)
        paths[name + '_launcher'] = Path(launcher)
    for key in ['RUSTC', 'RUSTDOC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER']:
        if env.get(key):
            value = env[key]
            binary = Path(value) if Path(value).is_file() else Path(shutil.which(value, path=env.get('PATH')) or '')
            need(binary.is_file(), 'Cannot freeze configured tool: ' + key)
            paths[key.lower()] = binary
    for name in ['cargo', 'rustc']:
        result = subprocess.run(['rustup', 'which', '--toolchain', '1.99.1', name],
                                env=env, capture_output=True, text=True)
        need(result.returncode == 0, 'Cannot resolve pinned Rust tool: ' + name)
        paths[name] = Path(result.stdout.strip())
    return {name: {'path': str(path.resolve()), 'sha256': file_hash(path)}
            for name, path in paths.items()}

def rust_mask(source):
    """Hide comments/literals while preserving offsets and newlines."""
    out = list(source)
    raw = re.compile(r'r(#{0,})"')
    char = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F_]+\}|.)|[^'\\\n])'")
    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '
    i = 0
    while i < len(source):
        if source.startswith('//', i):
            end = source.find('\n', i)
            end = len(source) if end < 0 else end
            blank(i, end); i = end
        elif source.startswith('/*', i):
            begin = i; depth = 1; i += 2
            while depth and i < len(source):
                if source.startswith('/*', i): depth += 1; i += 2
                elif source.startswith('*/', i): depth -= 1; i += 2
                else: i += 1
            need(depth == 0, 'Unclosed Rust block comment')
            blank(begin, i)
        elif source[i] == 'r' and (match := raw.match(source, i)):
            end_marker = '"' + match.group(1)
            end = source.find(end_marker, match.end())
            need(end >= 0, 'Unclosed Rust raw string')
            end += len(end_marker); blank(i, end); i = end
        elif source[i] == '"':
            begin = i; i += 1
            while i < len(source):
                if source[i] == '\\': i += 2
                elif source[i] == '"': i += 1; break
                else: i += 1
            blank(begin, min(i, len(source)))
        elif source[i] == "'" and (match := char.match(source, i)):
            blank(i, match.end()); i = match.end()
        else:
            i += 1
    return ''.join(out)

def suite_inventory(source):
    masked = rust_mask(source)
    suites = {}
    for match in re.finditer(r'(?m)^fn (the_prover_rejects_[A-Za-z0-9_]+)\(', masked):
        name = match.group(1)
        begin = masked.index('{', match.end()); depth = 0; end = None
        for i in range(begin, len(masked)):
            if masked[i] == '{': depth += 1
            elif masked[i] == '}':
                depth -= 1
                if depth == 0: end = i + 1; break
        need(end is not None, 'Unclosed test suite: ' + name)
        text = source[match.start():end]
        identities = list(dict.fromkeys(re.findall(r'"(brotli-[a-z0-9-]+)"', text)))
        suites[name] = {'suite': name, 'mutants': identities, 'suite_source_sha256': digest(text.encode())}
    return suites

def required_controls(root):
    source = (root / 'tests/proof_rejection.rs').read_text()
    suites = suite_inventory(source)
    prior = json.loads((HERE / 'prior37-control-manifest.json').read_text())
    need(len(prior) == 37, 'Expected the exact prior37 frozen manifest')
    affected = json.loads((HERE / 'affected-suites.json').read_text())
    baseline = json.loads((HERE / 'baseline-five-control-updates.json').read_text())['cases']
    old_names = set(json.loads((HERE / 'original-suite-inventory.json').read_text())['suites'])
    required = {entry['suite'] for entry in prior} | {entry['suite'] for entry in affected}
    baseline_suites = set()
    for entry in baseline:
        matches = [name for name, row in suites.items() if entry['name'] in row['mutants']]
        need(len(matches) == 1, 'Baseline case must occur in exactly one suite: ' + entry['name'])
        baseline_suites.add(matches[0])
    required |= baseline_suites
    # Exact new function names, independent of naming choices within the R suite.
    new_suites = {name for name, row in suites.items() if name not in old_names and row['mutants']}
    need(new_suites, 'New R defect suite is not present yet; final positive is not ready')
    required |= new_suites
    need(required <= suites.keys(), 'Missing mandatory suite(s): ' + repr(sorted(required - suites.keys())))
    for old in prior:
        need(set(old['mutants']) <= set(suites[old['suite']]['mutants']),
             'Prior control identity was removed: ' + old['suite'])
    rows = [suites[name] for name in sorted(required)]
    need(all(row['mutants'] for row in rows), 'Mandatory suite has no discovered Brotli case identities')
    identities = [case for row in rows for case in row['mutants']]
    need(len(identities) == len(set(identities)), 'Canary identities collide across required suites')
    for row in rows:
        row['case_identities'] = [{'name': case, 'identity_sha256': digest(canonical({
            'name': case, 'suite': row['suite'], 'suite_source_sha256': row['suite_source_sha256'],
            'test_source_sha256': digest(source.encode())}))} for case in row['mutants']]
    return {'schema': 'm1-r-control-union-v1', 'suites': rows,
            'prior_suites': sorted(entry['suite'] for entry in prior),
            'affected_suites': sorted(entry['suite'] for entry in affected),
            'baseline_five_suites': sorted(baseline_suites), 'new_suites': sorted(new_suites),
            'test_source_sha256': digest(source.encode()), 'case_count': len(identities)}

def run(root, env, folder, name, command):
    log = folder / (name + '.log'); started_ns = time.time_ns(); began = time.monotonic()
    row = {'command': command, 'started_utc': stamp(), 'started_ns': started_ns}
    try:
        with log.open('w') as output:
            result = subprocess.run(command, cwd=root, env=env, stdout=output, stderr=subprocess.STDOUT)
        code = result.returncode
    except OSError as error:
        log.write_text(str(error) + '\n'); code = 127
    row.update(exit_code=code, elapsed_seconds=time.monotonic()-began, finished_utc=stamp(),
               log=str(log.relative_to(folder)), log_sha256=file_hash(log))
    print(json.dumps({'step': name, 'exit_code': code, 'seconds': row['elapsed_seconds']}), flush=True)
    return row, log.read_text()

def proof_report(text):
    begin = text.find('{\n  "func-details"')
    need(begin >= 0, 'No pinned-verifier JSON report')
    report = json.loads(text[begin:])
    result = report['verification-results']
    need(result['success'] is True and type(result['errors']) is int and result['errors'] == 0
         and result['is-verifying-entire-crate'] is True,
         'Positive was not an unchanged entire-crate success')
    return report

def semantic_rejection(text):
    lower = text.lower()
    tooling = any(word in lower for word in [
        'resource limit', 'rlimit) exceeded', 'expected rlimit-count', 'panicked',
        'internal compiler error', 'unexpected smt output', 'thread panicked',
        'out of memory', 'segmentation fault', 'solver process exited', 'timed out'])
    syntax = bool(re.search(r'(?m)^error\[E[0-9]+\]', text)) or bool(re.search(r'(?m)^error(?:\[[A-Z0-9]+\])?: (?:expected\b|unexpected\b|cannot find\b|'
                            r'mismatched types\b|no method\b|no field\b|failed to resolve\b)', text))
    computed = 'error: expression simplifies to false' in lower and 'by (compute_only)' in text
    checked = bool(re.search(r'verification results:: .*\b[1-9][0-9]* errors', text)) and any(
        word in lower for word in ['postcondition not satisfied', 'precondition not satisfied',
                                  'requires not satisfied', 'invariant not satisfied', 'assertion failed'])
    return {'semantic_rejection': bool(computed or checked) and not tooling and not syntax,
            'tool_or_resource_failure': tooling, 'syntax_or_type_failure': syntax,
            'computed_false': computed, 'checked_semantic_error': checked}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['positive', 'controls'])
    parser.add_argument('--tag', required=True)
    parser.add_argument('--suite', action='append')
    args = parser.parse_args(); need(re.fullmatch('[a-z0-9-]+', args.tag), 'Invalid evidence tag')
    root = Path.cwd(); evidence = root / 'evidence'; out = evidence / args.tag
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, DEVELOPER_DIR='/Library/Developer/CommandLineTools',
               RUSTUP_TOOLCHAIN='1.99.1', VERUS_ROOT=str(TOOL))
    controls = required_controls(root)
    lineage = json.loads((HERE / 'frozen-scope-audit.json').read_text())
    scope_identities = {
        'proposal_frozen_input_sha256': lineage['identities']['proposal_frozen_input'],
        'actual_preimplementation_input_sha256': lineage['identities']['actual_preimplementation_input'],
        'shared_preimplementation_prefix_sha256': lineage['identities']['both_prefix'],
    }
    need(scope_identities['proposal_frozen_input_sha256'] != scope_identities['actual_preimplementation_input_sha256'],
         'Distinct proposal/preimplementation identities must not be collapsed')
    frozen = {'source_sha256': source_snapshot(root), 'driver_sha256': file_hash(__file__),
              'scope_identities': scope_identities,
              'input_sha256': input_snapshot(), 'tools': tool_snapshot(env),
              'environment': {name: env.get(name) for name in ENV_KEYS},
              'required_controls_sha256': digest(canonical(controls))}
    def unchanged():
        return (source_snapshot(root) == frozen['source_sha256'] and
                file_hash(__file__) == frozen['driver_sha256'] and
                input_snapshot() == frozen['input_sha256'] and tool_snapshot(env) == frozen['tools'])
    if args.phase == 'positive':
        need(not args.suite, '--suite applies only to diagnostic control subsets')
        need(not (out / 'positive.json').exists(), 'Use a fresh tag for a new positive cohort')
        write(out / 'source-start.json', dict(frozen, started_utc=stamp()))
        write(out / 'required-controls.json', controls)
        shutil.copyfile(__file__, out / 'gate-driver.py.txt')
        for name in INPUT_NAMES:
            shutil.copyfile(HERE / name, out / name)
        runtime = []
        for name, command in RUNTIME:
            row, text = run(root, env, out, name, command)
            row['passed'] = sum(map(int, re.findall(r'test result: ok\. (\d+) passed; 0 failed', text)))
            runtime.append(row); write(out / 'runtime-results.json', runtime)
            need(row['exit_code'] == 0 and row['passed'] > 0 and unchanged(), 'Runtime/source failure: ' + name)
        whole, text = run(root, env, out, 'whole-crate', WHOLE)
        whole['source_unchanged'] = unchanged(); write(out / 'whole-result.json', whole)
        need(whole['exit_code'] == 0 and whole['source_unchanged'], 'Whole positive failed or inputs drifted')
        report = proof_report(text); write(out / 'verification.json', report)
        write(out / 'positive.json', {'schema': 'm1-r-positive-v1', **frozen,
              'runtime_passed': sum(row['passed'] for row in runtime),
              'runtime': runtime, 'whole': whole, 'verification': report['verification-results'],
              'source_unchanged': True, 'completed_utc': stamp()})
        return
    positive = json.loads((out / 'positive.json').read_text())
    for key, value in frozen.items():
        need(positive[key] == value, 'Positive cohort mismatch: ' + key)
    need(positive['source_unchanged'], 'Positive did not freeze source')
    need(positive['whole']['command'] == WHOLE and positive['whole']['exit_code'] == 0,
         'Positive command/exit mismatch')
    need(file_hash(out / positive['whole']['log']) == positive['whole']['log_sha256'], 'Positive transcript changed')
    report = proof_report((out / positive['whole']['log']).read_text())
    need(report['verification-results'] == positive['verification'], 'Positive report mismatch')
    for row, (name, command) in zip(positive['runtime'], RUNTIME):
        need(row['command'] == command and row['exit_code'] == 0 and row['passed'] > 0,
             'Positive runtime mismatch: ' + name)
        need(file_hash(out / row['log']) == row['log_sha256'], 'Positive runtime transcript changed')
        text = (out / row['log']).read_text()
        actual_passed = sum(map(int, re.findall(r'test result: ok\. (\d+) passed; 0 failed', text)))
        need(actual_passed == row['passed'], 'Positive runtime result mismatch')
    need(len(positive['runtime']) == len(RUNTIME), 'Missing positive runtime check')
    need(json.loads((out / 'required-controls.json').read_text()) == controls, 'Suite closure changed')
    selected = controls['suites']
    if args.suite:
        requested = set(args.suite); need(requested <= {r['suite'] for r in selected}, 'Unknown/nonmandatory suite')
        selected = [row for row in selected if row['suite'] in requested]
    need(selected, 'No selected suites')
    attempt = out / 'control-attempts' / str(time.time_ns()); attempt.mkdir(parents=True)
    write(attempt / 'selected-controls.json', selected)
    # Preserve preexisting evidence exactly; no automatic checkout/restore occurs.
    backup_path = out / 'canary-restoration-manifest.json'
    if not backup_path.exists():
        backups = []
        for suite in controls['suites']:
            for case in suite['mutants']:
                path = evidence / ('canary-' + case + '.log')
                row = {'name': case, 'path': str(path.relative_to(root)), 'existed': path.exists()}
                if path.exists():
                    dest = out / 'historical-canary-backup' / path.name; dest.parent.mkdir(exist_ok=True)
                    shutil.copyfile(path, dest); row.update(backup=str(dest.relative_to(out)), sha256=file_hash(dest))
                backups.append(row)
        write(backup_path, {'positive_source_sha256': frozen['source_sha256'], 'cases': backups})
    else:
        backups = json.loads(backup_path.read_text())
        need(backups['positive_source_sha256'] == frozen['source_sha256'], 'Canary backup cohort mismatch')
        for row in backups['cases']:
            if row['existed']: need(file_hash(out / row['backup']) == row['sha256'], 'Historical canary backup changed')
    def control(suite):
        name = suite['suite']; before = {}
        for case in suite['mutants']:
            path = evidence / ('canary-' + case + '.log')
            before[case] = path.stat().st_mtime_ns if path.exists() else None
        command = ['cargo', 'test', '--locked', '--release', '--test', 'proof_rejection', name,
                   '--', '--ignored', '--exact', '--nocapture']
        row, text = run(root, env, attempt, 'controls-' + name, command)
        if row['exit_code'] == 0 and 'test result: ok. 0 passed;' in text:
            command = ['cargo', 'test', '--locked', '--release', '--test', 'proof_rejection', name,
                       '--', '--exact', '--nocapture']
            row, text = run(root, env, attempt, 'controls-' + name, command)
        row.update(suite=name, suite_source_sha256=suite['suite_source_sha256'],
                   expected_mutants=len(suite['mutants']), mutants=[], validation_errors=[],
                   executed_once='test result: ok. 1 passed; 0 failed' in text,
                   source_and_tools_unchanged=unchanged())
        if row['exit_code'] == 0 and not row['executed_once']:
            row['validation_errors'].append('Exactly one executed test was required')
        if row['exit_code'] == 0 and row['executed_once']:
            for case, identity in zip(suite['mutants'], suite['case_identities']):
                path = evidence / ('canary-' + case + '.log')
                if not path.exists() or path.stat().st_mtime_ns < row['started_ns'] or path.stat().st_mtime_ns == before[case]:
                    row['validation_errors'].append('Missing or stale canary: ' + case); continue
                data = path.read_bytes(); dest = attempt / path.name; dest.write_bytes(data)
                row['mutants'].append({**identity, 'log': dest.name, 'sha256': digest(data),
                                       **semantic_rejection(data.decode(errors='replace'))})
        write(attempt / ('control-' + name + '.json'), row)
        return row
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        rows = list(pool.map(control, selected))
    write(attempt / 'controls-results.json', rows)
    passed = all(row['exit_code'] == 0 and row['executed_once'] and not row['validation_errors'] and
                 row['source_and_tools_unchanged'] and len(row['mutants']) == row['expected_mutants'] and
                 all(case['semantic_rejection'] for case in row['mutants']) for row in rows)
    need(unchanged(), 'Frozen source/tool/driver/input closure drifted during controls')
    full = {row['suite'] for row in selected} == {row['suite'] for row in controls['suites']}
    summary = {'schema': 'm1-r-controls-v1', **frozen, 'attempt': str(attempt.relative_to(out)),
               'attempt_results_sha256': file_hash(attempt / 'controls-results.json'),
               'selected_suites': len(selected), 'required_suites': len(controls['suites']),
               'selected_semantic_controls_passed': passed, 'all_required_suites_executed': full,
               'complete_frozen_control_gate': bool(passed and full),
               'semantic_rejections': sum(len(row['mutants']) for row in rows),
               'completed_utc': stamp(), 'claim': 'Named frozen proof/control evidence only; not M1 or decoder completion'}
    write(attempt / 'summary.json', summary)
    write(out / 'controls-results.json', summary)
    if passed and full:
        write(out / 'controls-complete.json', summary)
        # Standalone frozen source package; no canary restoration mutates this archive.
        with tarfile.open(out / 'frozen-source.tar.gz', 'w:gz') as archive:
            for name, expected_hash in frozen['source_sha256'].items():
                data = (root / name).read_bytes()
                need(digest(data) == expected_hash, 'Source drift while packaging: ' + name)
                info = tarfile.TarInfo(name); info.size = len(data); info.mode = 0o644
                archive.addfile(info, io.BytesIO(data))
        need(unchanged(), 'Closure drift while packaging')
        bound_files = [out / row['log'] for row in positive['runtime']]
        bound_files += [out / positive['whole']['log']]
        bound_files += [out / name for name in ['source-start.json', 'required-controls.json',
                       'verification.json', 'runtime-results.json', 'whole-result.json', 'positive.json',
                       'controls-complete.json', 'gate-driver.py.txt', 'canary-restoration-manifest.json',
                       'frozen-source.tar.gz'] + INPUT_NAMES]
        bound_files += [path for path in attempt.rglob('*') if path.is_file()]
        write(out / 'evidence-package.json', {'schema': 'm1-r-package-v1',
              'files': {str(path.relative_to(out)): file_hash(path) for path in sorted(set(bound_files))},
              'positive_sha256': file_hash(out / 'positive.json'),
              'controls_complete_sha256': file_hash(out / 'controls-complete.json'),
              'source_archive_sha256': file_hash(out / 'frozen-source.tar.gz'),
              'driver_sha256': frozen['driver_sha256'], 'tools': frozen['tools'],
              'scope_identities': frozen['scope_identities'],
              'input_sha256': frozen['input_sha256'], 'required_controls_sha256': frozen['required_controls_sha256'],
              'source_sha256': frozen['source_sha256'], 'canary_restoration': 'RESTORE_CANARIES.txt'})
    print(json.dumps(summary), flush=True)
    need(passed, 'Control suite did not produce only fresh semantic rejections')
    if not full: print('Diagnostic subset only; no full-control completion claim.', flush=True)

if __name__ == '__main__':
    try:
        main()
    except (GateError, FileNotFoundError, KeyError, json.JSONDecodeError) as error:
        print('GATE FAILED: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
