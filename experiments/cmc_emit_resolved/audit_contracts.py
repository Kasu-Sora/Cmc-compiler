#!/usr/bin/env python3
"""Freeze main's manual semantic review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_resolved_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_resolved.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());expected={f['name'] for f in fs if not f['prototype']};assert len(expected)==8
checks={
'cm_emit_resolved':['op equals opcode code; non-CALL exclusion and singleton capacity bound retained','Exact resolved singleton appended; raw buffer represented existentially'],
'cm_emit_resolved_call':['No function-id validity, range, readiness or PC-representability premise','All signed int function_id supported, raw CALL identifier written','Resolved result is CALL(cm_function_pc policy p function_id)'],
'cm_emit_resolved_normalize':['Original type-code-wf and encoded equality only','Exact normalize fragment length capacity bound and resolved append'],
'cm_emit_resolved_load':['Original type-code-wf and encoded equality only','Exact load fragment length capacity bound and resolved append'],
'cm_emit_resolved_store':['Original type-code-wf and encoded equality only','Exact store fragment length capacity bound and resolved append'],
'cm_emit_resolved_fp_address':['Exact source FP-address fragment and capacity condition','Raw and resolved prefixes linked by full patch map'],
'cm_emit_resolved_temp_store':['Original eight pure facts retained in both pre and post','Additional pre fragment capacity bound, full function context ownership','Same total lookup policy for function identity/offset; no new fid bound','Exact resolved temp-store fragment append'],
'cm_emit_resolved_temp_load':['Original eight pure facts retained in both pre and post','Additional pre fragment capacity bound, full function context ownership','Same total lookup policy for function identity/offset; no new fid bound','Exact resolved temp-load fragment append']}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
 sources.append(dict(function=n,contract=source));rows.append(dict(function=n,source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=checks[n]))
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_lib.v').read_text();models=[];baseline=[]
source_map={x:x+'_def' for x in ['cm_patch_inst','cm_patch_code','cm_resolved_emitter_rep']}
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map, 'Unreviewed new definition: '+x['name']
  item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit={'status':'Source contracts and patch/resolved models manually reviewed; final verification pending','contracts':rows,'annotation_stage_model_declarations':models,'model_review':['Patch changes only CALL immediate to existing total cm_function_pc, retaining opcode','Patch-code map retains instruction order and cardinality','Resolved representation existentially owns RAW buffer, with equality to patched logical prefix','Core representation/fragment models, total lookup and function-PC definitions unchanged'],'adaptations':['Consistent explicit cm_lookup_policy parameter throughout patch model and wrapper contracts','Rocq map represents source list recursion; Zlength represents ilength','Reused exact emitter ABI declaration and seven verified helper contracts'],'scope_boundary':'Concrete emission wrappers under logical patch interpretation. Actual call-buffer rewrite pass, complete TVM semantics and compiler preservation not claimed.','review_method':'Manual comparison of definitions/contracts and ownership; hashes detect later drift.'}
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Recorded eight reviewed contracts and three patch/resolved model declarations.')
