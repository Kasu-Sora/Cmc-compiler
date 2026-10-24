#!/usr/bin/env python3
"""Classify fixed C* runtime contracts, annotations and proof support separately."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parent
s=(R/'baseline/cmc_concrete_emit_core.c').read_text();lines=s.splitlines()
fs=json.loads((R/'metrics/source-functions.json').read_text())
mask=lambda t:re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),t,flags=re.S)
masked=mask(s)
clean=re.sub(r'/\*.*?\*/|//[^\n]*',lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S).splitlines()
span=lambda a,b:[s[:a].count('\n')+1,s[:b-1].count('\n')+1]
count=lambda a,b:sum(bool(l.strip()) for l in clean[a-1:b])
decl=[]
for m in re.finditer(r'^PROOF\s+(?:static\s+|extern\s+)?\w+\s+(\w+)\b',masked,re.M):
 d=re.search(r'[;{]',masked[m.end():]);at=m.end()+d.start();end=at+1
 if masked[at]=='{':
  depth=1
  while depth:depth+=(masked[end]=='{')-(masked[end]=='}');end+=1
 a,b=span(m.start(),end);text=s[m.start():end]
 kind='model' if re.search(r'new_(fun|rec|datatype)_definition',text) else 'export_scaffolding' if 'cst_add_const_to_header' in text else 'proof'
 decl.append(dict(name=m.group(1),kind=kind,span=[a,b],nonblank_lines=count(a,b),text=text))
names={x['name']for x in decl};byname={x['name']:x for x in decl}
for x in decl:x['dependencies']=sorted((set(re.findall(r'\b\w+\b',x['text']))&names)-{x['name']})
runtime_text='\n'.join('\n'.join(lines[a-1:b]) for f in fs if not f['prototype'] for a,b in [f['source_span']])
direct=set(re.findall(r'\b\w+\b',runtime_text))&names
def closure(seed):
 result=set(seed)
 while True:
  more={n for x in result for n in byname[x]['dependencies']}-result
  if not more:return result
  result|=more
used=closure(direct)
header=(R/'baseline/cmc_concrete_emit_core.h').read_text()
exports=set(re.findall(r'^PROOF\s+(?:extern\s+)?\w+\s+(\w+)',header,re.M))
proof_exports={x for x in exports&names if not x.startswith('get_cm_concrete_')}
shared=closure(proof_exports)
for x in decl:
 if x['kind']=='model':x['category']='source_case_model' if x['name'] in used else 'outside_runtime_dependency_closure_model'
 elif x['kind']=='export_scaffolding':x['category']='export_scaffolding'
 elif x['name']in shared:x['category']='exported_shared_proof_closure'
 elif x['name']not in used:x['category']='outside_runtime_dependency_closure_proof_support'
 else:x['category']='private_case_proof_support'
function_counts=[];attribute_entries=[]
for f in fs:
 if f['prototype']:continue
 item=dict(function=f['name'],source_span=f['source_span'])
 for cat in ['specification','annotation','inline_proof']:item[cat]=sum(count(a,b) for a,b in f[cat])
 function_counts.append(item)
 for a,b in f['annotation']:
  text='\n'.join(lines[a-1:b]);k=re.search(r'\[\[cst::(\w+)',text).group(1)
  attribute_entries.append(dict(function=f['name'],kind=k,span=[a,b],nonblank_lines=count(a,b)))
totals={k:sum(f[k]for f in function_counts) for k in ['specification','annotation','inline_proof']}
for category in sorted({d['category']for d in decl}):totals[category]=sum(d['nonblank_lines']for d in decl if d['category']==category)
totals['case_proof']=totals['inline_proof']+totals.get('private_case_proof_support',0)
totals['proof_including_shared']=totals['case_proof']+totals.get('exported_shared_proof_closure',0)
result=dict(source_sha256=hashlib.sha256(s.encode()).hexdigest(),function_counts=function_counts,source_top_level_proof_helpers=decl,totals=totals,annotation_entries=attribute_entries,public_proof_roots=sorted(proof_exports),public_wrappers_not_called_by_runtime_proof=sorted(proof_exports-used),counting_note='Nonblank non-comment physical lines; body contracts counted once; forward/header duplicates excluded. Exported proof helper wrappers and transitive same-file support counted once as shared; unused source readiness definitions/getters inventoried separately.')
(R/'metrics/source-effort.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(functions=len(function_counts),totals=totals,public_roots=sorted(proof_exports),annotation_entries=len(attribute_entries),declaration_count=len(decl)),indent=2))
