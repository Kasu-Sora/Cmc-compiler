#!/usr/bin/env python3
"""Supplement physical line metrics with lexical size; token counts are not difficulty."""
from pathlib import Path
import re,json
from audit_syntax import c_functions,coq_mask
R=Path(__file__).resolve().parent
source=(R/'baseline/cmc_concrete_emit_ast.c').read_text().splitlines()
fs=json.loads((R/'metrics/source-functions.json').read_text())
se=json.loads((R/'metrics/source-effort.json').read_text())
sizes=lambda s:dict(characters=len(s),lexical_tokens=len(re.findall(r'\w+|\S',s)),nonblank_lines=sum(bool(l.strip()) for l in s.splitlines()))
rows=[]
for f in fs:
 if f['prototype']:continue
 for kind in ['specification','annotation','inline_proof']:
  text='\n'.join('\n'.join(source[a-1:b]) for a,b in f[kind])
  rows.append(dict(function=f['name'],category=kind,**sizes(text)))
(R/'metrics/source-text-size.json').write_text(json.dumps(rows,indent=2)+'\n')
# Target must be a final verified experiment snapshot, never a mutable working file.
cfile=R/'target/cmc_emit_ast_migration.c'
if cfile.exists():
 c=cfile.read_text();functions=c_functions(c);counts={};entries=[]
 for m in re.finditer(r'/\*@.*?\*/',c,re.S):
  f=next((f for f in functions if f['start']<=m.start()<f['end']),None)
  if not f:kind='coq_imports' if 'Import Coq' in m.group() else 'external_declarations'
  elif f['prototype']:kind='duplicate_prototype_specification' if f['name'] in {x['name'] for x in fs} else 'integration_helper_specification'
  elif m.start()<f['body_start']:kind='specification'
  else:kind='annotation'
  text=m.group();entry={'category':kind,'function':f['name'] if f else None,'entry_type':re.search(r'/\*@\s*(\w+)',text).group(1),**sizes(text)}
  entries.append(entry);counts[kind]=counts.get(kind,0)+1
 (R/'metrics/annotation-entry-counts.json').write_text(json.dumps({'target':counts,'entries':entries,'source':se['annotation_entries']},indent=2)+'\n')
 print(json.dumps(counts))
