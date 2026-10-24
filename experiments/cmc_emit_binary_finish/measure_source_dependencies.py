"""Incremental mathematical source closure; excludes previously charged models."""
from pathlib import Path
import json,re,hashlib,shutil
R=Path(__file__).resolve().parent
D={}
for filename in ['cmc_lang.c','cmc_codegen.c','cmc_concrete_defs.c','cmc_temp_algebra.c']:
 p=R/'baseline'/filename
 if not p.exists():shutil.copy2(Path('/Users/nizitong/cmc')/filename,p)
 text=p.read_text();masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),text,flags=re.S)
 for m in re.finditer(r'^PROOF\s+(?:static\s+|extern\s+)?\w+\s+(\w+)\b',masked,re.M):
  at=m.end();depth=0
  while at<len(masked):
   c=masked[at]
   if c=='{':depth+=1
   if c=='}':
    depth-=1
    if depth==0:at+=1;break
   if c==';' and depth==0:at+=1;break
   at+=1
  frag=text[m.start():at]
  D[m.group(1)]=dict(name=m.group(1),file='baseline/'+filename,span=[text[:m.start()].count('\n')+1,text[:at-1].count('\n')+1],nonblank_lines=sum(bool(x.strip())for x in frag.splitlines()),sha256=hashlib.sha256(frag.encode()).hexdigest(),text=frag)
roots=['cm_pointer_encode_pointee','cm_type_code_wf_pointee','cm_type_refs_pointee']
proofs=set(roots)
while True:
 more=set()
 for n in proofs:
  for name in set(re.findall(r'\b\w+\b',D[n]['text']))&D.keys():
   d=D[name]
   if name.startswith('get_') or re.search(r'new_(?:fun|rec|datatype)_definition',d['text']) or 'cst_add_const_to_header' in d['text']:continue
   more.add(name)
 more-=proofs
 if not more:break
 proofs|=more
rows=[]
for name in sorted(proofs):
 d={k:v for k,v in D[name].items()if k!='text'};d['category']='public_proof_closure';rows.append(d)
result=dict(scope='Incremental pointee encoding/wellformedness/reference proof closure; existing pointer bridges, size, opcodes, plan and binary_finish definitions reused',declarations=rows,definition_count=0,equation_slices=0,definition_lines=0,public_proof_lines=sum(x['nonblank_lines']for x in rows),new_public_roots=roots,historical_development_seconds=None,reused_models=['cm_pointer_scale and cm_binary_finish_code from emit-expr-call','cm_rep_is_pointer_code and pointer code value bridge/cases from counts','cm_type_size and expression type encoding from leaf/layout','core opcode, temp-load and plan models'],note='Six source-private shape/value proof helpers remain in case proof; previously used public bridge/plan proof closures are excluded. This is source dependency size, not historical migration time.')
(R/'metrics/source-additional-definitions.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
