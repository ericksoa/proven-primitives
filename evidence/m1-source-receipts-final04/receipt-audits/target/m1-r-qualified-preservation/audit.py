"""Read-only qualified declaration preservation; no approval or proof conclusion."""
from pathlib import Path
import argparse
import collections
import difflib
import hashlib
import json
import re
import sys
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(HERE))
from audit_tools import close, declarations, mask_code

REFS = {
    'proposal_f1a': REPO / 'target/m1-r-frozen-scope-audit/frozen-f1a',
    'preimplementation_e10c': REPO / 'target/m1-r-frozen-scope-audit/baseline-e10c',
}
EXPECTED = {
    'proposal_f1a': {'brotli_input': 'f1a37362e128944c9c0ca49f00f30c172270677140e60027d3d655c46d831eef',
                     'brotli_prefix': '112d237139f6df4b6f3975b75c50543639b894fc733ddb024b6842471c265e03'},
    'preimplementation_e10c': {'brotli_input': 'e10c61b1354c5b1debef9e76aa55b412d06e35de210cb8949a73ef33b912da23',
                               'brotli_prefix': '112d237139f6df4b6f3975b75c50543639b894fc733ddb024b6842471c265e03'},
}
INDEX_SUM = 'brotli_prefix::m1_canonical_nonzero_index_sum'
CLAUSES = r'requires|ensures|decreases|recommends|returns|opens_invariants|no_unwind'


def sha(data): return hashlib.sha256(data).hexdigest()
def write(path, data): path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
def hashes(root):
    return {module: sha((Path(root) / 'src' / (module + '.rs')).read_bytes())
            for module in ['brotli_input', 'brotli_prefix']}


def all_items(root):
    """Group declarations/all_items span approach, retaining qualified IDs."""
    rows = {}
    sources = {m: (Path(root) / 'src' / (m + '.rs')).read_text().split('\n#[cfg(test)]', 1)[0]
               for m in ['brotli_input', 'brotli_prefix']}
    for d in declarations(root):
        source = sources[d['module']]; masked = mask_code(source)
        # Ignore visibility parentheses in pub(crate); start after the actual fn name.
        fn = re.search(r'\bfn\s+' + re.escape(d['name']) + r'\s*(?:<[^\n(]*>)?\s*\(', masked[d['start']:])
        assert fn, d['id']
        op = d['start'] + fn.end() - 1; args_end = close(source, op)
        first = masked.index('{', args_end)
        clause = re.search(r'\b(?:' + CLAUSES + r')\b', masked[args_end:first])
        if clause is None:
            opening = first
        else:
            indent = 4 if d['impl'] else 0
            body = re.search(r'(?m)^' + ' ' * indent + r'\{', masked[args_end:])
            assert body, (d['id'], 'body not found')
            opening = args_end + body.start() + indent
        end = close(source, opening, '{', '}') + 1
        header = source[d['start']:opening]; body = source[opening:end]
        rx = r'(?m)^[ \t]*(?:(?:pub(?:\([^)]*\))?|open|closed|uninterp|spec|proof|exec|broadcast)\s+)*fn\s+\w+\s*(?:<[^\n(]*>)?\s*\('
        assert not re.search(rx, mask_code(source[args_end:opening])), (d['id'], 'swallowed header')
        assert not re.search(rx, mask_code(body[1:-1])), (d['id'], 'swallowed body')
        assert d['id'] not in rows, ('duplicate qualified ID', d['id'])
        rows[d['id']] = dict(d, header=header, body=body, opening=opening, end=end,
                             args_open=op-d['start'], args_end=args_end-d['start'],
                             header_sha256=sha(header.encode()), body_sha256=sha(body.encode()))
    return rows


# Preserve string/character/raw-string tokens; only comments/layout are ignored.
TOKEN = re.compile(r'[A-Za-z_][A-Za-z_0-9]*|[0-9][A-Za-z_0-9]*|<==>|==>|=~=' 
                   r'|&&&|\|\|\||::|==|!=|<=|>=|&&|\|\||=>|->|\+=|-=|<<|>>|\.\.|[^\s]')
RAW = re.compile(r'(?:b)?r(#{0,})"')
CHAR = re.compile(r"(?:b)?'(?:\\(?:u\{[0-9a-fA-F_]+\}|.)|[^'\\\n])'")

def tokens(source):
    result = []; i = 0
    while i < len(source):
        if source[i].isspace(): i += 1; continue
        if source.startswith('//', i):
            z = source.find('\n', i); i = len(source) if z < 0 else z; continue
        if source.startswith('/*', i):
            depth = 1; i += 2
            while depth:
                assert i < len(source), 'unclosed comment'
                if source.startswith('/*', i): depth += 1; i += 2
                elif source.startswith('*/', i): depth -= 1; i += 2
                else: i += 1
            continue
        raw = RAW.match(source, i)
        if raw:
            ending = '"' + raw.group(1); z = source.find(ending, raw.end()); assert z >= 0
            z += len(ending); result.append(source[i:z]); i = z; continue
        char = CHAR.match(source, i)
        if char:
            result.append(char.group()); i = char.end(); continue
        if source[i] == '"' or source.startswith('b"', i):
            z = i + (2 if source.startswith('b"', i) else 1)
            while z < len(source):
                if source[z] == '\\': z += 2
                elif source[z] == '"': z += 1; break
                else: z += 1
            result.append(source[i:z]); i = z; continue
        match = TOKEN.match(source, i); assert match, source[i:i+30]
        result.append(match.group()); i = match.end()
    return result


def norm(source): return '\x1f'.join(tokens(source))
def attrs(item): return [a['text'] for a in item['attributes']]

def contract(item):
    header = item['header']; masked = mask_code(header)
    op, end = item['args_open'], item['args_end']
    matches = list(re.finditer(r'\b(' + CLAUSES + r')\b', masked[end+1:]))
    matches = [(end+1+m.start(), end+1+m.end(), m.group(1)) for m in matches]
    signature_end = matches[0][0] if matches else len(header)
    tail = header[end+1:signature_end].strip()
    ret = tail[2:].strip() if tail.startswith('->') else '()'
    binder = None
    if ret.startswith('('):
        rt = re.fullmatch(r'\(\s*(\w+)\s*:\s*(.*)\)', ret, re.S)
        if rt: binder, ret = rt.groups()
    clauses = {}
    for index, (start, finish, key) in enumerate(matches):
        stop = matches[index+1][0] if index+1<len(matches) else len(header)
        assert key not in clauses, (item['id'], 'repeated contract clause', key)
        clauses[key] = header[finish:stop]
    return dict(args=header[op:end+1], ret=ret, binder=binder, clauses=clauses)


def replace_identifier(source, old, new):
    masked = mask_code(source); edits = list(re.finditer(r'\b'+re.escape(old)+r'\b', masked))
    for match in reversed(edits): source = source[:match.start()]+new+source[match.end():]
    return source


def compare_specs(label, old, new, out):
    rows = []; missing = []; changes = []
    for identity, a in sorted(old.items()):
        if a['kind'] != 'spec': continue
        b = new.get(identity)
        if b is None or b['kind'] != 'spec':
            missing.append(identity); continue
        expected = a['header']; allowed = False
        if identity == INDEX_SUM:
            expected, n = re.subn(r'\bspec\s+fn\s+m1_canonical_nonzero_index_sum\b',
                                 'pub(crate) open spec fn m1_canonical_nonzero_index_sum', expected, count=1)
            assert n == 1, identity
            allowed = b['header'] == expected
        header_equal = a['header'] == b['header']
        body_equal = a['body'] == b['body']
        attrs_equal = attrs(a) == attrs(b)
        preserved = body_equal and attrs_equal and (header_equal or allowed)
        row = dict(id=identity, baseline_line=a['line'], candidate_line=b['line'],
                   body_byte_exact=body_equal, header_byte_exact=header_equal,
                   attributes_exact=attrs_equal, allowed_index_sum_visibility_only=allowed,
                   normalized_body_equal=norm(a['body'])==norm(b['body']),
                   normalized_expected_header_equal=norm(expected)==norm(b['header']),
                   baseline_header_sha256=a['header_sha256'], candidate_header_sha256=b['header_sha256'],
                   baseline_body_sha256=a['body_sha256'], candidate_body_sha256=b['body_sha256'],
                   preserved_under_exact_R_exception=preserved)
        rows.append(row)
        if not preserved:
            changes.append(identity)
            path = out/'diffs'/(label+'__'+identity.replace('::','__')+'.diff');path.parent.mkdir(exist_ok=True)
            path.write_text(''.join(difflib.unified_diff((a['header']+a['body']).splitlines(True),
                (b['header']+b['body']).splitlines(True),fromfile=label+'/'+identity,tofile='candidate/'+identity)))
    return dict(rows=rows, count=len(rows), missing=missing, unexpected_changes=changes,
                allowed_visibility_openings=[r['id'] for r in rows if r['allowed_index_sum_visibility_only']],
                passed=not missing and not changes)


def compare_contracts(label, old, new):
    rows = []; violations = []
    for identity, a in sorted(old.items()):
        if a['kind']=='spec': continue
        b = new.get(identity)
        if b is None or b['kind'] != a['kind']:
            violations.append(dict(id=identity, reason='missing or changed declaration kind'));continue
        x, y = contract(a), contract(b)
        paired = a['kind']=='exec' and norm(y['ret']) == norm('('+x['ret']+', Ghost<nat>)')
        same_ret = norm(x['ret'])==norm(y['ret'])
        row = dict(id=identity, kind=a['kind'], baseline_line=a['line'], candidate_line=b['line'],
                   ordinary_arguments_preserved=norm(x['args'])==norm(y['args']),
                   original_requires_preserved=norm(x['clauses'].get('requires',''))==norm(y['clauses'].get('requires','')),
                   original_return_preserved=same_ret, approved_return_pair=paired)
        expected = x['clauses'].get('ensures','')
        if x['binder'] and y['binder']:
            expected=replace_identifier(expected,x['binder'],y['binder']+('.0' if paired else ''))
        row['all_old_guarantees_text_retained']=not norm(expected) or norm(expected) in norm(y['clauses'].get('ensures',''))
        row['other_old_clauses_preserved']=all(norm(value)==norm(y['clauses'].get(key,''))
            for key,value in x['clauses'].items() if key not in ['requires','ensures'])
        row['original_attributes_retained']=all(attr in attrs(b) for attr in attrs(a))
        row['attributes_exact']=attrs(a)==attrs(b)
        row['baseline_attributes']=attrs(a);row['candidate_attributes']=attrs(b)
        for key in ['ordinary_arguments_preserved','original_requires_preserved','all_old_guarantees_text_retained',
                    'other_old_clauses_preserved','original_attributes_retained']:
            if not row[key]:violations.append(dict(id=identity,reason=key))
        if not(same_ret or paired):violations.append(dict(id=identity,reason='return representation changed outside R pair'))
        rows.append(row)
    return dict(rows=rows, count=len(rows), violations=violations, passed=not violations,
                paired_exec_count=sum(r['approved_return_pair'] for r in rows))


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--candidate',default=str(REPO));p.add_argument('--out',required=True)
    p.add_argument('--expected-input');p.add_argument('--expected-prefix');p.add_argument('--expected-tests');p.add_argument('--final',action='store_true');a=p.parse_args()
    out=Path(a.out).resolve();target=(REPO/'target').resolve();assert out.is_relative_to(target),'Reports must stay under target'
    out.mkdir(parents=True,exist_ok=True);candidate=Path(a.candidate).resolve()
    if a.final:assert a.expected_input and a.expected_prefix,'Final attestation requires root-provided exact hashes'
    tests_hash=sha((candidate/'tests/proof_rejection.rs').read_bytes())
    if a.expected_tests:assert tests_hash==a.expected_tests,'root tests hash mismatch'
    gate=REPO/'target/m1-r-final-gate'
    gate_before={str(p.relative_to(gate)):sha(p.read_bytes()) for p in gate.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
    data={m:(candidate/'src'/(m+'.rs')).read_bytes() for m in ['brotli_input','brotli_prefix']}
    actual={m:sha(b) for m,b in data.items()};assert hashes(candidate)==actual,'candidate changed during read'
    if a.expected_input:assert actual['brotli_input']==a.expected_input,'root input hash mismatch'
    if a.expected_prefix:assert actual['brotli_prefix']==a.expected_prefix,'root prefix hash mismatch'
    frozen=out/'candidate-snapshot';(frozen/'src').mkdir(parents=True,exist_ok=True)
    for m,b in data.items():(frozen/'src'/(m+'.rs')).write_bytes(b)
    catalogs={label:all_items(root) for label,root in REFS.items()};catalogs['candidate']=all_items(frozen)
    for label,root in REFS.items():assert hashes(root)==EXPECTED[label],('retained reference bytes mismatch',label)
    summaries={};new=catalogs['candidate']
    for label in REFS:
        old=catalogs[label];spec=compare_specs(label,old,new,out);interfaces=compare_contracts(label,old,new)
        write(out/(label+'-specs.json'),spec);write(out/(label+'-contracts.json'),interfaces)
        old_spec=[d for d in old.values() if d['kind']=='spec'];duplicates=collections.defaultdict(list)
        for d in old_spec:duplicates[d['name']].append(d['id'])
        duplicates={n:ids for n,ids in duplicates.items() if len(ids)>1}
        attribute_changes=[dict(id=n,kind=d['kind'],baseline_attributes=attrs(d),candidate_attributes=attrs(new[n]))
            for n,d in old.items() if n in new and attrs(d)!=attrs(new[n])]
        write(out/(label+'-attribute-changes.json'),attribute_changes)
        summaries[label]=dict(reference_hashes=EXPECTED[label],counts=dict(collections.Counter(d['kind'] for d in old.values())),
            existing_spec_count=len(old_spec),spec_basenames_that_would_collide=duplicates,
            specs_passed=spec['passed'],spec_unexpected_changes=spec['unexpected_changes'],spec_missing=spec['missing'],
            allowed_index_sum_openings=spec['allowed_visibility_openings'],contracts_passed=interfaces['passed'],
            contract_violations=interfaces['violations'],paired_exec_count=interfaces['paired_exec_count'],
            attribute_changes=attribute_changes,
            added_declarations=[dict(id=n,kind=new[n]['kind']) for n in sorted(set(new)-set(old))])
        write(out/(label+'-qualified-catalog.json'),[{k:v for k,v in d.items() if k not in ['header','body']}
            for n,d in sorted(old.items())])
    write(out/'candidate-qualified-catalog.json',[{k:v for k,v in d.items() if k not in ['header','body']}
        for n,d in sorted(new.items())])
    assert hashes(candidate)==actual,'candidate drifted; report cannot attest current source'
    assert sha((candidate/'tests/proof_rejection.rs').read_bytes())==tests_hash,'tests drifted during read'
    gate_after={str(p.relative_to(gate)):sha(p.read_bytes()) for p in gate.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
    assert gate_after==gate_before,'frozen gate bundle drifted during audit'
    result=dict(status='final qualified static preservation audit' if a.final else 'PRELIMINARY qualified static preservation audit; awaiting root final hash',
        final_attestation=bool(a.final),candidate=str(candidate),candidate_hashes=actual,
        tests_sha256=tests_hash,gate_bundle_hashes_unchanged=gate_after,
        candidate_counts=dict(collections.Counter(d['kind'] for d in new.values())),comparisons=summaries,
        all_existing_specs_preserved_under_only_named_R_visibility_exception=all(x['specs_passed'] for x in summaries.values()),
        old_args_requires_returns_and_guarantees_retained=all(x['contracts_passed'] for x in summaries.values()),
        parser_lineage=json.loads((HERE/'parser-lineage.json').read_text()),source_stable_for_read=True,
        authority_conclusion='None. Distinct proposal f1a and actual preimplementation e10c identities remain separate; no human approval inferred.',
        limitations=['Static textual preservation is not a proof, compiler-erasure equivalence, whole-crate gate, or permission to change architecture.',
                     'Added declarations/attribute changes are inventoried, not approved by this audit.'],
        gate_bundle_changed=False,source_mutations=0,mutant_runs=0)
    write(out/'audit-result.json',result)
    print(json.dumps({k:result[k] for k in ['status','candidate_hashes','candidate_counts',
          'all_existing_specs_preserved_under_only_named_R_visibility_exception','old_args_requires_returns_and_guarantees_retained']},indent=2))
    print(json.dumps({label:{k:v for k,v in value.items() if k not in ['added_declarations','spec_basenames_that_would_collide','reference_hashes']}
                      for label,value in summaries.items()},indent=2))

if __name__=='__main__':main()
