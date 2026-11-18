"""Read-only, rerunnable qualified audit of frozen3e2f field candidate/main."""
from pathlib import Path
import argparse, ast, bisect, collections, difflib, hashlib, importlib.util, json, re, sys
REPO=Path(__file__).resolve().parents[2]
QA=REPO/'target/m1-r-qualified-preservation/audit.py'
spec=importlib.util.spec_from_file_location('qualified_base_auditor',QA)
q=importlib.util.module_from_spec(spec);spec.loader.exec_module(q)
FIELD='brotli_input::CodeDescriptionDecoder::advance_field'
INDEX=q.INDEX_SUM
EXPECTED_INPUT='3e2f1bb6f4535920666f2cf1c838f5db4d23f8ed2dbd4545f49194bfd940789e'
EXPECTED_PREFIX='daf8ab85002cb576fd70446f4ffc76e15bf879edfc3d45ad7a5fe3c80cbb8c15'
OLD_INPUT='25c4718fb0f7debeecf6d1cf0f1de604c77e09ff30a344b8cbf662316bc511aa'
INTENTIONAL_SP={'brotli_input::CompressedMetaBlockDecoder::apply_block_count_value',
                'brotli_input::store_complex_code_description_payload'}

def sha(data):return hashlib.sha256(data).hexdigest()
def write(p,data):p.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def attrs(d):return q.attrs(d)
def specs_compare(old,new):
 rows=[];violations=[]
 for n,a in sorted(old.items()):
  if a['kind']!='spec':continue
  b=new.get(n)
  if b is None or b['kind']!='spec':violations.append((n,'missing/kind change'));continue
  expected=a['header'];opened=False
  if n==INDEX and not re.search(r'\bpub\(crate\)\s+open\s+spec\s+fn',expected):
   expected,count=re.subn(r'\bspec\s+fn\s+m1_canonical_nonzero_index_sum\b','pub(crate) open spec fn m1_canonical_nonzero_index_sum',expected,count=1);assert count==1
   opened=b['header']==expected and b['header']!=a['header']
  row={'id':n,'body_byte_exact':a['body']==b['body'],'header_byte_exact':a['header']==b['header'],
       'only_approved_visibility_opening':opened,'attributes_byte_exact':attrs(a)==attrs(b),
       'decreases_byte_exact':q.contract(a)['clauses'].get('decreases','')==q.contract(b)['clauses'].get('decreases',''),
       'baseline_header_sha256':a['header_sha256'],'candidate_header_sha256':b['header_sha256'],
       'baseline_body_sha256':a['body_sha256'],'candidate_body_sha256':b['body_sha256']}
  row['passed']=row['body_byte_exact'] and row['attributes_byte_exact'] and (row['header_byte_exact'] or opened) and row['decreases_byte_exact']
  if not row['passed']:violations.append((n,'unexpected spec change'))
  rows.append(row)
 return {'rows':rows,'violations':violations,'passed':not violations}

def balanced_statement_end(body,start):
 masked=q.mask_code(body);stack=[];pairs={')':'(',']':'[','}':'{'}
 for i in range(start,len(masked)):
  c=masked[i]
  if c in '([{':stack.append(c)
  elif c in ')]}':
   if not stack:break
   assert stack.pop()==pairs[c]
  elif c==';' and not stack:return i+1
 return len(body)

def receipt_signature(item):
 body=item['body'];masked=q.mask_code(body);bindings=[];binding_ghosts=set()
 for m in re.finditer(r'\blet\b[^;=]*\bGhost\((\w+)\)[^;=]*=',masked):
  gm=list(re.finditer(r'\bGhost\((\w+)\)',masked[m.start():m.end()]))
  for g in gm:binding_ghosts.add(m.start()+g.start())
  end=balanced_statement_end(body,m.end())
  bindings.append({'variable':m.group(1),'initializer':q.norm(body[m.end():end].rstrip(';'))})
 constructors=[];sink_vars=set()
 for m in re.finditer(r'\bGhost\(',masked):
  if m.start() in binding_ghosts:continue
  op=masked.index('(',m.start());end=q.close(body,op);expr=body[op+1:end]
  constructors.append(q.norm(expr));sink_vars.update(re.findall(r'\b[A-Za-z_]\w*\b',expr))
 # A producer is initialized/updated in its own body, or passed through from a child.
 assignments=[]
 for name in sorted(sink_vars):
  rx=r'\b'+re.escape(name)+r'\s*(?::\s*[^;=]+)?(?P<op>\+=|-=|=(?!=|>))\s*'
  for m in re.finditer(rx,masked):
   end=balanced_statement_end(body,m.end());rhs=body[m.end():end].rstrip(';').strip()
   assignments.append({'variable':name,'operator':m.group('op'),'rhs':q.norm(rhs),
                       'budget_or_reservation_terms':re.findall(r'\b(?:work_remaining|planning_work|execution_work|reserved_work)\b',rhs)})
 return {'constructors_in_return_order':constructors,'child_receipt_bindings':bindings,
         'producer_assignments':assignments,
         'direct_child_forwarder':not constructors,
         'budget_or_reservation_assignment_findings':[a for a in assignments if a['budget_or_reservation_terms']]}

def byte_projection_tokens(function):
 # Exact existing byte-agent audit function, loaded without its top-level writes.
 path=REPO/'target/m1-r-field-decomp12/audit_proof_only.py';text=path.read_text();tree=ast.parse(text)
 node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='tokens')
 source='\n'.join(text.splitlines()[node.lineno-1:node.end_lineno]);ns={'re':re,'masked':q.mask_code}
 exec(compile(source,str(path)+'::tokens','exec'),ns)
 return ns['tokens'](function)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--candidate',default=str(REPO));p.add_argument('--out',required=True);a=p.parse_args()
 candidate=Path(a.candidate).resolve();out=Path(a.out).resolve();assert out.is_relative_to((REPO/'target').resolve());out.mkdir(parents=True,exist_ok=True)
 expected={'brotli_input':EXPECTED_INPUT,'brotli_prefix':EXPECTED_PREFIX};assert q.hashes(candidate)==expected,'candidate not expected frozen3e2f/daf'
 all_source={str(p.relative_to(candidate)):p.read_bytes() for p in (candidate/'src').glob('*.rs')};source_hashes={n:sha(b) for n,b in all_source.items()}
 gate=REPO/'target/m1-r-final-gate';gate_before={str(p.relative_to(gate)):sha(p.read_bytes()) for p in gate.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
 snapshot=out/'candidate-snapshot';(snapshot/'src').mkdir(parents=True,exist_ok=True)
 for name,data in all_source.items():(snapshot/name).write_bytes(data)
 refs={**q.REFS,'retained_main25':REPO/'target/m1-r-qualified-preservation/final-main/candidate-snapshot'}
 assert q.hashes(refs['retained_main25'])=={'brotli_input':OLD_INPUT,'brotli_prefix':EXPECTED_PREFIX}
 catalogs={label:q.all_items(root) for label,root in refs.items()};new=q.all_items(snapshot);summaries={}
 for label,old in catalogs.items():
  s=specs_compare(old,new);c=q.compare_contracts(label,old,new);write(out/(label+'-specs.json'),s);write(out/(label+'-contracts.json'),c)
  changes=[]
  for n,d in sorted(old.items()):
   if n in new and attrs(d)!=attrs(new[n]):changes.append({'id':n,'kind':d['kind'],'old':attrs(d),'new':attrs(new[n])})
  old_rlimit={n:[x for x in attrs(d) if 'rlimit' in x] for n,d in old.items()}
  assert all(old_rlimit[n]==[x for x in attrs(new[n]) if 'rlimit' in x] for n in old if n in new),'allowance value/attachment changed'
  summaries[label]={'old_counts':dict(collections.Counter(d['kind'] for d in old.values())),
    'old_qualified_spec_count':len(s['rows']),'byte_exact_old_spec_bodies':sum(r['body_byte_exact'] for r in s['rows']),
    'byte_exact_old_spec_headers':sum(r['header_byte_exact'] for r in s['rows']),
    'allowed_visibility_openings':[r['id'] for r in s['rows'] if r['only_approved_visibility_opening']],
    'spec_passed':s['passed'],'spec_violations':s['violations'],'contracts_passed':c['passed'],'contract_violations':c['violations'],
    'new_R_pairs_vs_reference':c['paired_exec_count'],'original_rlimit_attributes_unchanged':True,'attribute_changes':changes}
  write(out/(label+'-qualified-catalog.json'),[{k:v for k,v in d.items() if k not in ['body','header']} for n,d in sorted(old.items())])
 old=catalogs['retained_main25'];added=[{'id':n,'kind':new[n]['kind'],'attributes':attrs(new[n]),'header_sha256':new[n]['header_sha256'],'body_sha256':new[n]['body_sha256']} for n in sorted(set(new)-set(old))]
 assert collections.Counter(d['kind'] for d in added)=={'proof':15,'spec':1},added
 assert all(new[d['id']]['impl']=='' for d in added)
 changed_exec=[]
 for n,d in sorted(old.items()):
  if d['kind']=='exec' and (d['header']!=new[n]['header'] or d['body']!=new[n]['body'] or attrs(d)!=attrs(new[n])):
   changed_exec.append({'id':n,'header_exact':d['header']==new[n]['header'],'body_exact':d['body']==new[n]['body'],'old_attributes':attrs(d),'new_attributes':attrs(new[n])})
 assert {d['id'] for d in changed_exec}=={FIELD}|INTENTIONAL_SP
 for n in INTENTIONAL_SP:assert attrs(old[n])==[] and attrs(new[n])==['#[verifier::spinoff_prover]'] and old[n]['header']==new[n]['header'] and old[n]['body']==new[n]['body']
 assert attrs(old[FIELD])==attrs(new[FIELD])==['#[verifier::rlimit(500)]','#[verifier::spinoff_prover]']
 # Actual receipt constructors/captures/assignments, separate from erased runtime.
 paired=[n for n,d in new.items() if d['kind']=='exec' and re.search(r'Ghost\s*<\s*nat\s*>',q.contract(d)['ret'])]
 origin_rows=[];origin_diffs=[]
 for n in sorted(paired):
  x=receipt_signature(old[n]);y=receipt_signature(new[n]);same=x==y
  row={'id':n,'header_exact_vs_main25':old[n]['header']==new[n]['header'],'body_exact_vs_main25':old[n]['body']==new[n]['body'],
       'receipt_origin_signature_unchanged':same,'candidate':y}
  origin_rows.append(row)
  if not same:origin_diffs.append(n)
 assert not origin_diffs,('receipt origin changed',origin_diffs)
 assert not any(r['candidate']['budget_or_reservation_assignment_findings'] for r in origin_rows),'modeled debit/forecast assignment needs review'
 field_before=old[FIELD]['body'];field_after=new[FIELD]['body'];bt=byte_projection_tokens(field_before);at=byte_projection_tokens(field_after);assert bt==at and len(bt)==2456,('body projection',len(bt),len(at),bt==at)
 # New proof-only table subtotal mirrors reached table events; it is not a returned receipt.
 body=new[FIELD]['body'];masked=q.mask_code(body);table=[]
 for m in re.finditer(r'\btable_reads\s*(?::\s*nat\s*)?=(?!=|>)\s*',masked):
  end=balanced_statement_end(body,m.end());table.append(body[m.start():end])
 assert table and all(not re.search(r'\b(?:work_remaining|planning_work|execution_work|reserved_work)\b',v) for v in table)
 # New helper arguments contain no mutable counter channel; no new trust bypass.
 for d in added:
  item=new[d['id']];assert '&mut' not in q.contract(item)['args'].replace(' ','')
  assert not re.search(r'\b(?:assume|admit)\b|external_body|uninterp',q.mask_code(item['header']+item['body']))
 write(out/'actual-receipt-origin-catalog.json',{'scope':'All158paired producers in input/prefix. Static construction/child-binding/producer-assignment identity vs frozen main25, not a proof of event equality.','rows':origin_rows,'new_field_table_subtotal_statements':table,'origin_differences':origin_diffs})
 write(out/'proof-only-delta.json',{'added_declarations':added,'new_private_opaque_table_spec':next(d for d in added if d['kind']=='spec'),
   'changed_existing_execs':changed_exec,'field_literal_header_exact':old[FIELD]['header']==new[FIELD]['header'],
   'field_runtime_projection_tokens_equal':True,'field_runtime_projection_token_count':len(bt),
   'projection_rule':'Exactly byte audit tokens(), including replacing new proof-validity invocation by equivalent old Verus assert before proof erasure; static only, not compiler/source-to-binary equivalence.',
   'all_actual_receipt_origin_signatures_unchanged':True,'no_new_ordinary_execs':True,'new_table_subtotal_is_nonreturned_proof_counter':True,
   'new_helper_mutable_counter_channels':0,'new_trust_bypass_tokens':0})
 assert q.hashes(candidate)==expected and {str(p.relative_to(candidate)):sha(p.read_bytes()) for p in (candidate/'src').glob('*.rs')}==source_hashes,'candidate drifted'
 assert {str(p.relative_to(gate)):sha(p.read_bytes()) for p in gate.rglob('*') if p.is_file() and '__pycache__' not in p.parts}==gate_before,'frozen gate bundle changed'
 tests_path=REPO/'tests/proof_rejection.rs';observed_tests=sha(tests_path.read_bytes()) if tests_path.exists() else None
 result={'status':'Final read-only CORE audit on frozen3e2f/daf; test freeze pending separately','candidate':str(candidate),'candidate_core_hashes':expected,
  'all_source_hashes':source_hashes,'counts':dict(collections.Counter(d['kind'] for d in new.values())),
  'comparisons':summaries,'existing_e10_specs':424,'existing_main25_specs':444,'new_spec_count':1,'new_proof_helper_count':15,'new_ordinary_exec_count':0,
  'all_receipt_producers':len(paired),'receipt_origin_signature_changes':origin_diffs,'all_receipt_budget_formula_findings':0,
  'field_header_exact':True,'field2456runtime_projection_tokens_equal':True,'intentional_SP_additions':sorted(INTENTIONAL_SP),'no_original_allowance_value_changes':True,
  'tests_observed_unfrozen_sha256':observed_tests,'test_hash_final_attestation':False,'gate_bundle_unchanged':True,
  'audit_script_sha256':sha(Path(__file__).read_bytes()),'qualified_auditor_sha256':sha(QA.read_bytes()),
  'source_mutations':0,'gate_mutations':0,'mutant_runs':0,'authority_conclusion':'None. Qualified preservation, proof-only/source-origin inventory and existing-unit observations do not grant architectural approval.',
  'limitations':['Static origin signatures are not independent proofs of source-event equality; actual whole/source-bound evidence remains separately named.',
                 'The3e2fwhole1397/0 and native105/0 are parent execution evidence; this audit runs no checker or mutants.',
                 'Tests may receive the three pending K7/K8Rcarrier literal repairs; their final hash must be rebound before final gates.']}
 write(out/'audit-result.json',result);write(out/'report-sha256.json',{str(p.relative_to(out)):sha(p.read_bytes()) for p in out.rglob('*') if p.is_file() and p.name!='report-sha256.json'})
 print(json.dumps({k:result[k] for k in ['candidate_core_hashes','counts','existing_e10_specs','existing_main25_specs','new_spec_count','new_proof_helper_count','all_receipt_producers','receipt_origin_signature_changes','intentional_SP_additions','no_original_allowance_value_changes']},indent=2))

if __name__=='__main__':main()
