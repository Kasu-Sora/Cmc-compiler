#!/usr/bin/env python3
"""Record main's source/target review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_function_pc_total_migration.c').read_text()
src=(R/'baseline/cmc_concrete_function_pc_total.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text())
expected={f['name'] for f in fs if not f['prototype']};assert len(expected)==2
checks={
'cmc_function_prefix_total':['Full program context and function list restored','wf, structs safety, nonnegative index, index/length alignment and int32 length upper bound preserved','Counts representability and complete recursive readiness retained','Exact prefix at target-index and i32 result preserved; arbitrary signed64 target'],
'cmc_function_pc_total':['Full program context and function list restored','Original wf and complete code-ready retained','Exact function PC and i32 result preserved; arbitrary signed64 target']}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b]) for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 sources.append({'function':n,'contract':source})
 rows.append({'function':n,'source_contract_sha256':hashlib.sha256(source.encode()).hexdigest(),'target_contract_sha256':hashlib.sha256(target.encode()).hexdigest(),'checks':checks[n],'adaptation':'Same universally quantified lookup policy/codegen obligations; source-proved emit_stmt length normalization to statement count.'})
assert {r['function']for r in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_lib.v').read_text();regs=coq_regions(lib)
models=[];baseline=[]
for x in regs:
 a,b=line_span(lib,x['start'],x['end']);fragment=lib[x['start']:x['end']]
 item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=hashlib.sha256(fragment.encode()).hexdigest())
 baseline.append(item)
 if x['kind'] in ['Definition','Fixpoint','Record','Inductive']:models.append(item)
assert {x['name']for x in models}=={'cm_temp_offset','cm_concrete_function_ready','cm_concrete_functions_ready','cm_concrete_structs_ready','cm_concrete_code_ready'},'Additional models require explicit review.'
audit={'status':'Two contracts and four complete readiness definitions plus original cm_temp_offset manually reviewed; final verification pending','contracts':rows,'annotation_stage_model_declarations':models,'inherited_model_boundary':'Verified counts/layout definitions unchanged, same lookup policy and four universally quantified emitter/TVM obligations; no concrete TVM instantiation.','source_proved_normalization':{'theorem':'cm_stmt_code_length','source':'baseline/cmc_codegen.c','lines':[1460,1487],'meaning':'For every stmt, p, fid, pc, temp, breakpc and continuepc, emitted statement length equals cm_stmt_code_count; unconditional','source_use':'baseline/cmc_concrete_function_ready.c lines 217-234','rocq_emitter_semantics_bridge_reproved':False},'review_method':'Manual comparison of all source/target pre/post resources and readiness conjuncts; no automatic semantic equivalence claim.'}
previous=R/'metrics/semantic-audit.json'
if previous.exists():assert json.loads(previous.read_text())['contracts']==rows,'Contracts changed: explicitly re-review.'
previous.write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Recorded reviewed contracts and readiness models.')
