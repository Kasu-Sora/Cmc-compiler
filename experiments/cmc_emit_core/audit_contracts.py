#!/usr/bin/env python3
"""Record completed main semantic review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_core_migration.c').read_text()
src=(R/'baseline/cmc_concrete_emit_core.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text())
expected={f['name']for f in fs if not f['prototype']};assert len(expected)==9
checks={
'cm_emit_raw':['Original spare-capacity premise and full emitter representation','Append exact op and immediate to equal-length int32/int64 prefixes; advance pc and preserve undefined suffixes'],
'cm_emit':['Opcode/code equality retained','Move exact head instruction from todo to end of done; restore complete plan'],
'cm_emit_normalize':['Encoded-type equality and only cm_type_code_wf preserved','Char has six exact instructions; every other type has empty fragment'],
'cm_emit_load':['Encoded-type equality and only cm_type_code_wf preserved','Char LOADB, otherwise LOAD, immediate 0'],
'cm_emit_store':['Encoded-type equality and only cm_type_code_wf preserved','Char STOREB, otherwise STORE, immediate 0'],
'cm_emit_fp_address':['Exact PUSH 8, LOAD 0, PUSH offset, ADD 0 fragment','Prefix/tail plan resources and original capacity condition preserved'],
'cm_emit_temp_store':['All eight pure preconditions also retained in postcondition','Complete function context ownership preserved','Same total lookup policy and cm_temp_offset; no extra fid bounds','Exact address fragment followed by STORE 0'],
'cm_emit_temp_load':['All eight pure preconditions also retained in postcondition','Complete function context ownership preserved','Same total lookup policy and cm_temp_offset; no extra fid bounds','Exact address fragment followed by LOAD 0'],
'cmc_binary_opcode':['Emp precondition, all signed int inputs','Exact ten-case/default MOD map and code !=22 postcondition']}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 assert 'Require' in target and 'Ensure' in target
 sources.append({'function':n,'contract':source});rows.append({'function':n,'source_contract_sha256':sha(source),'target_contract_sha256':sha(target),'checks':checks[n]})
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_core_migration_lib.v').read_text();regs=coq_regions(lib);models=[];baseline=[]
source_map={'tvm_opcode':'tvm_opcode_ty','tvm_opcode_code':'tvm_opcode_code_def','tvm_inst':'tvm_inst_ty','tvm_inst_op':'tvm_inst_op_def','tvm_inst_imm':'tvm_inst_imm_def','cm_rep_ops':'cm_rep_ops_def','cm_rep_imms':'cm_rep_imms_def','cm_emitter_rep':'cm_emitter_rep_def','cm_emitter_plan_rep':'cm_emitter_plan_rep_def','cm_char_normalize_code':'cm_char_normalize_code_def','cm_load_code':'cm_load_code_def','cm_store_code':'cm_store_code_def','cm_fp_relative_address_code':'cm_fp_relative_address_code_def','cm_temp_store_code':'cm_temp_store_code_def','cm_temp_load_code':'cm_temp_load_code_def','cm_binary_opcode':'cm_binary_opcode_def'}
for x in regs:
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name'] in source_map,'New model needs explicit review: '+x['name']
  item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
source_codes=dict(re.findall(r'\(tvm_opcode_code (TVM\w+Op) = (\d+)i\)',(R/'baseline/tvm_model.c').read_text()))
target_codes=dict(re.findall(r'\| (TVM\w+Op) => (\d+)\b',lib));assert len(source_codes)==28 and target_codes==source_codes
adaptations=['HOL lists represented by Rocq lists with Zlength; recursive projections represented by map','HOL type equality against CMCharTy represented by exhaustive datatype match','IntArray/Int64Array seg/undef_seg use indices instead of explicit byte-offset start pointers; widths unchanged','Existing arbitrary total cm_lookup_policy passed consistently to function lookup and cm_temp_offset','Source cm_emitter declaration copied exactly alongside frozen common ABI; no runtime edits']
audit={'status':'Main reviewed original contracts and concrete models; controller final verification pending','contracts':rows,'annotation_stage_model_declarations':models,'adaptations':adaptations,'model_review':['Full 28-opcode datatype/code table identical','Instruction constructor and selectors preserve opcode and unbounded integer immediate','All seven fragments preserve exact source instruction sequence','Emitter existential buffers, five owned fields, nonzero pointer facts, equal lengths and capacity bounds retained','Plan capacity condition and projections preserved; no abstract emitter or execution parameters introduced'],'review_method':'Manual source/target comparison; hash checks detect later changes and do not establish semantic equivalence. Full QCP pipeline checks implementation obligations.'}
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
print('Recorded nine reviewed contracts and concrete instruction/emitter model mapping.')
