#!/usr/bin/env python3
"""Map source model declarations to names used by the target model library.
This inventory counts original reusable definitions, not new QCP proof effort.
"""
from pathlib import Path
import re,json
from audit_syntax import line_span,coq_mask,coq_regions
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_counts_migration_lib.v').read_text()
known=set(re.findall(r'\bcm_\w+\b',coq_mask(lib)));allrows=[]
target_defined={x['name'] for x in coq_regions(lib) if x['kind'] in ['Definition','Fixpoint','Record','Inductive']}
reused_lib=(Q/'Rocq/examples/QCP_demos_human/cmc_layout_migration_lib.v').read_text()
reused_defined={x['name'] for x in coq_regions(reused_lib) if x['kind'] in ['Definition','Fixpoint','Record','Inductive']}
for n in ['cmc_lang.c','cmc_rep.c','cmc_codegen.c','cmc_concrete_defs.c','cmc_concrete_counts.c']:
 p=R/'baseline'/n;s=p.read_text()
 masked=re.sub(r'/\*.*?\*/|//[^\n]*|`[^`]*`|"(?:\\.|[^"\\])*"',lambda m:re.sub(r'[^\n]',' ',m.group()),s,flags=re.S)
 for m in re.finditer(r'^PROOF (?:thm|indtype) (\w+)\s*=\s*new_(?:fun|rec|datatype)_definition\s*\(',masked,re.M):
  primary=re.sub(r'_(def|ty)$','',m.group(1))
  end=masked.index(';',m.end())+1;chunk=s[m.start():end]
  allrows.append(dict(file=str(p.relative_to(R)),declaration=m.group(1),primary=primary,span=line_span(s,m.start(),end),nonblank_lines=sum(bool(l.strip())for l in chunk.splitlines()),text=chunk))
rows=[]
while True:
 selected=[x for x in allrows if x['primary'] in known and x not in rows]
 if not selected:break
 rows.extend(selected)
 for x in selected:known.update(re.findall(r'\bcm_\w+\b',x['text']))
for x in rows:
 x['classification']=('direct_target_declaration' if x['primary'] in target_defined else 'existing_layout_declaration' if x['primary'] in reused_defined else 'source_transitive_dependency_or_renamed_translation')
 x['note']='Source closure inventory, not a claim that every source definition has a translated Rocq declaration; emitter predicates are parameterized.'
(R/'metrics/source-model-definitions.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(declaration_blocks=len(rows),nonblank_lines=sum(x['nonblank_lines'] for x in rows))))
