#!/usr/bin/env python3
"""Record manually reviewed semantic mapping; hashes detect later drift only."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_ast_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_ast.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());expected={f['name'] for f in fs if not f['prototype']};assert len(expected)==2
checks={
'cm_emit_binding_address':['All ten source pure facts retained in pre/post, including complete parameterized cm_wf_program','Both full context ownership predicates preserved','Exact global/local/default address fragment appended to done','No new fid validity, range, offset or readiness premise'],
'cm_emit_binding_address_plan':['All ten source pure facts retained in pre/post','Both full context ownership predicates preserved','Exact binding fragment consumed from todo and appended to done; arbitrary tail unchanged','Same existing lookup policy and cg obligations parameters']}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
 sources.append(dict(function=n,contract=source));rows.append(dict(function=n,source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=checks[n]))
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_lib.v').read_text();models=[];baseline=[]
source_map={n:n+'_def' for n in ['cm_slots_prefix','cm_globals_prefix','cm_global_address','cm_param_offset','cm_local_offset','cm_push_code','cm_binding_address_code']}
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map,'Unreviewed new definition: '+x['name']
  item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit=dict(status='Source contracts, seven models and prefix lemmas manually reviewed; final verification pending',contracts=rows,annotation_stage_model_declarations=models,model_review=['Prefixes recurse on lists at every Z index with equality-zero guard, including negatives','Global address 16+semantic globals prefix; params8+prefix; locals8+params size+prefix','Push singleton exact; binding code has original global/local/default branches','Prefix bridge premises match source wellformedness; existing size lemmas reused','Existing cm_binding_valid, total cm_lookup_policy and full cm_wf_program policy cg preserved'],adaptations=['Explicit inherited lookup policy and codegen-obligations parameters','Rocq Zlength / list app for ilength / ++','Five exact verified helper contracts reused; raw resolved memory and plan budget unchanged'],scope_boundary='Concrete binding-address functions under existing logical patch view; four codegen obligations remain parameterized as in counts. No complete emitter semantics, physical CALL rewrite pass, TVM execution or compiler preservation claim.',review_method='Manual source/target comparison and theorem review; hashes detect drift, not semantic equivalence.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Recorded two reviewed contracts and seven semantic model declarations.')
