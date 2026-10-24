"""Measure matched source declarations, explicitly not the full support closure."""
from pathlib import Path
import runpy,json,re
R=Path(__file__).resolve().parent
ctx=runpy.run_path(str(R/'audit.py'));source=ctx['source'];eff=ctx['result']
# Pair only identical-name statements/definitions. No guessed counterpart for
# stronger/combined/new lemmas, and no ratios over this incomplete subset.
rows=[];seen=set();totals={'definition_lines':0,'proof_constructor_lines':0,'proof_constant_scaffolding_lines':0}
for mod in eff['modules']:
 for d in mod['declarations']:
  if d['kind']=='Ltac':continue
  kind='proof' if d['kind']=='Lemma' else 'definition'
  key=d['name'] if kind=='proof' else d['name']+'_def'
  originals=source.get(key,[])
  if not originals:continue
  chosen=[]
  for orig in originals:
   token=(orig['file'],tuple(orig['span']))
   if token not in seen:
    seen.add(token);chosen.append(dict(orig,category='definition_lines' if kind=='definition' else 'proof_constant_scaffolding_lines'))
   if kind=='proof':
    # The exported theorem initialization names its exact constructor.
    for callee in re.findall(r'\b(\w+)\s*\(',orig['text'].split('=',1)[-1]):
     for body in source.get(callee,[]):
      if body['file']!=orig['file'] or '{' not in body['text']:continue
      token=(body['file'],tuple(body['span']))
      if token not in seen:
       seen.add(token);chosen.append(dict(body,category='proof_constructor_lines'))
  for x in chosen:totals[x['category']]+=x['nonblank_lines'];x.pop('text',None)
  rows.append(dict(target=d['name'],kind=kind,source=chosen))
report=dict(status='partial_same_name_reference_inventory',totals=totals,entries=rows,
 full_source_incremental_public_cost=None,full_source_to_target_ratio=None,
 note='Exact source declarations and directly named proof constructors only. Transitive shared proof tactics and dependencies are NOT included. Names alone are not theorem-equivalence evidence; use source/target statements. Combined, strengthened-local and newly factored lemmas have no guessed cost. Do not compare these partial source lines with all target proof lines.')
(R/'metrics/source-reference-cost.json').write_text(json.dumps(report,indent=2)+'\n')
print(totals)
