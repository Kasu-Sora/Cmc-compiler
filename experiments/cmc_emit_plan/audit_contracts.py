#!/usr/bin/env python3
"""Freeze main's manual semantic review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_plan_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_plan.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());expected={f['name'] for f in fs if not f['prototype']};assert len(expected)==8
checks={
'cm_emit_plan':['Original opcode encoding equality and non-CALL restriction retained','Consume singleton from todo; append exact singleton to done; arbitrary tail retained'],
'cm_emit_call_plan':['No function-id validity, range, readiness or PC-representability premise','All signed int IDs supported by SAME existing total lookup policy','Logical resolved CALL(PC(id)) consumed/appended, physical helper called on raw ID'],
'cm_emit_normalize_plan':['Original encoded-type equality and type-code-wf only','Exact original normalize fragment consumed/appended; arbitrary tail retained'],
'cm_emit_load_plan':['Original encoded-type equality and type-code-wf only','Exact original load fragment consumed/appended; arbitrary tail retained'],
'cm_emit_store_plan':['Original encoded-type equality and type-code-wf only','Exact original store fragment consumed/appended; arbitrary tail retained'],
'cm_emit_fp_address_plan':['Original exact FP-address fragment consumed/appended','No additional offset, pc or readiness assumptions; arbitrary tail retained'],
'cm_emit_temp_store_plan':['Original eight pure facts retained in both pre and post','Full function context ownership and exact store fragment transformation','Same total lookup policy; no new fid bound; arbitrary tail retained'],
'cm_emit_temp_load_plan':['Original eight pure facts retained in both pre and post','Full function context ownership and exact load fragment transformation','Same total lookup policy; no new fid bound; arbitrary tail retained']}

rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
 sources.append(dict(function=n,contract=source));rows.append(dict(function=n,source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=checks[n]))
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_lib.v').read_text();models=[];baseline=[]
source_map={'cm_resolved_emitter_plan_rep':'cm_resolved_emitter_plan_rep_def'}
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map, 'Unreviewed new definition: '+x['name']
  item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit={'status':'Source contracts and resolved-plan model manually reviewed; final verification pending','contracts':rows,'annotation_stage_model_declarations':models,'model_review':['Plan is pure Zlength(done)+Zlength(todo)<=capacity plus EXISTING resolved representation of done','todo is a logical remaining capacity budget, with no extra physical ownership','No reachability, program-wide code equality, readiness or valid-call constraint added','Existing raw-buffer and patch logical semantics and same total lookup policy reused unchanged'],'adaptations':['Consistent explicit existing cm_lookup_policy parameter','Rocq Zlength represents original ilength; plan assertion maps conjunction of pure bound and resolved heap predicate','Eight identical helper contracts reused from verified resolved case'],'scope_boundary':'Concrete plan wrappers under existing logical patch view; no physical CALL rewrite pass, full TVM execution or compiler preservation claim.','review_method':'Manual comparison of contracts and representation; hashes detect later drift, not semantic equivalence.'}
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Recorded eight reviewed contracts and one resolved-plan model declaration.')
