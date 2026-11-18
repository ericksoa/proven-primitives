from pathlib import Path
import sys,re,json,hashlib
b=Path(__file__).resolve().parent;sys.path.insert(0,str(b));from r_util import bounds,masked
src=(b/'src/brotli_input.rs').read_text();a,body,z=bounds(src,'CodeDescriptionDecoder::advance_field');new=src[a:z];old=(b.parent/'m1-r-field-decomp01/field-before.txt').read_text()
def tokens(t):
 t=t.replace('proof { r_m1_field_valid_from_components(*self); }','assert(self.valid());')
 m=masked(t);sp=[]
 for hit in re.finditer(r'\bproof\s*\{',m):
  if any(a<=hit.start()<z for a,z in sp):continue
  i=m.index('{',hit.start())+1;depth=1
  while depth:depth+=(m[i]=='{')-(m[i]=='}');i+=1
  sp.append((hit.start(),i))
 for hit in re.finditer(r'\blet\s+ghost\b',m):
  if not any(a<=hit.start()<z for a,z in sp):sp.append((hit.start(),m.index(';',hit.end())+1))
 for a,z in sorted(sp,reverse=True):t=t[:a]+t[z:]
 t=re.sub(r'\b(?:hide|reveal|reveal_with_fuel)\([^;]+;','',t)
 t=re.sub(r'\binvariant\b.*?\bdecreases\b[^\n]*\n','',t,flags=re.S)
 return re.findall(r'\w+|[^\s]',masked(t))
oldpos=old.index('\n    {\n');newpos=new.index('\n    {\n');assert old[:oldpos]==new[:newpos];x,y=tokens(old[oldpos:]),tokens(new[newpos:]);assert x==y
report={'header_exact':True,'executable_tokens_exact_after_proof_erasure':True,'runtime_tokens':len(x),'attrs':'original rlimit500/spinoff intact','source_sha256':hashlib.sha256(src.encode()).hexdigest(),'main_unchanged':hashlib.sha256((b.parents[1]/'src/brotli_input.rs').read_bytes()).hexdigest()=='25c4718fb0f7debeecf6d1cf0f1de604c77e09ff30a344b8cbf662316bc511aa'};(b/'proof-only-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
