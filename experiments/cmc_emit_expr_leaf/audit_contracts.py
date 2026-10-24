"""Freeze main's actual source/target semantic review. Hashes detect drift only."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_expr_leaf_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_expr_leaf.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());expected={f['name']for f in fs};assert len(expected)==9
checks={
'cmc_const_immediate':['All signed64 inputs retained; unsigned64 remainder gives Euclidean low byte for char','Exact encoding and type_code_wf facts retained in pre/post; nonchar identity'],
'cm_emit_const_expr':['Original BODY type_code_wf pre/post retained; weaker header discrepancy disclosed','lvalue bounds, constructor shape and total f lookup retained','Full program/function/expression resources; exact singleton or empty leaf plan consumption'],
'cm_emit_string_expr':['Original sid[0,INT_MAX], typed, globals/strings-safe and combined-size facts retained in pre/post','No sid<length strengthening','Exact semantic string address; complete resources and plan tail preserved'],
'cm_emit_getc_expr':['Original lvalue bounds, constructor shape, total f lookup retained; no typed/wf added','Exact GETC0 or empty fragment; full three contexts and plan tail preserved'],
'cm_sizeof_value':['Original code encoding, typed, code-wf, type refs, structs-safe retained in pre/post','Return semantic type_size, full program context preserved; pointer and narrowed branches verified'],
'cm_type_size_value':['Same full original type-size contract; static helper body also verified'],
'cm_emit_sizeof_expr':['Original lvalue, constructor, lookup, typed, asked-code-wf/type-refs and structs-safe facts retained','Exact semantic sizeof PUSH or empty fragment; full resources and tail retained'],
'cm_member_array_value_context':['Original six pure conditions retained in pre/post and complete program context','Return original member_array_code under original member validity'],
'cm_member_offset_value_context':['Original six pure conditions retained in pre/post and complete program context','Return semantic member_offset; C remainder bridged under derived nonnegative pointer encoding, no new bounds']}
rows=[];sources=[]
for f in c_functions(c):
 if f['prototype']:continue
 n=f['name'];a=next(x for x in fs if x['name']==n);source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
 sources.append(dict(function=n,contract=source));rows.append(dict(function=n,source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=checks[n]))
assert {x['function']for x in rows}==expected
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_lib.v').read_text();models=[];baseline=[]
source_map={n:n+'_def'for n in ['cm_const_immediate','cm_strings_prefix','cm_string_address','cm_member_offset_slots','cm_member_offset']}
source_map.update({'cm_leaf_expr':'Typed four-constructor restriction adapter; no general emitter claim','cm_leaf_source_expr':'Embedding into existing cm_expr constructors','cm_leaf_of_expr':'Partial projection; None for unsupported constructors','cm_leaf_rvalue':'cm_emit_expr_pair_def four leaf equations + cm_rcode_of_def + cm_emit_rvalue_def','cm_leaf_code_for':'cm_expr_code_for_def restricted to leaves; all four lcode branches empty'})
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map,'Unreviewed model: '+x['name']
  item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit=dict(status='Manual contract/model review recorded; final verification pending',contracts=rows,annotation_stage_model_declarations=models,model_review=[
'四类leaf采用独立cm_leaf_expr类型，嵌入现有cm_expr；非leaf投影为None，没有把非leaf代码伪定义为空。',
'cm_leaf_rvalue/code_for对应源Const/String/Getc/Sizeof四条方程及lvalue选择；这些分支不依赖fid/pc/temp，函数契约仍保留原参数和总f查询。',
'cm_const_immediate与源char低字节/非char恒等分支一致；使用既有tower_u8。',
'cm_strings_prefix直接复用现有表示前缀；其递归与源字符串前缀在所有Z索引上按加法结合律相同，包含负索引。',
'语义string_address保持16+globals语义大小+strings前缀；typed条件用于连接表示与语义global大小。',
'成员前缀使用cm_struct_member_size，保留所有Z索引递归；member_offset保留合法sid判断，越界为0。',
'既有cm_type_size/struct_slots_size模型复用；slots_wf下普通槽大小与结构槽大小相等，再连接表示struct大小与语义type大小。',
'源与目标的leaf方程对应由源码审计确认；本例不把这些Rocq方程引理称为已完成HOL到Rocq元定理。'],adaptations=['Existing lookup policy/typed_program preserved','Typed leaf-only specialization under existing constructor premises, no added precondition','Six exact previous helper contracts reused; both static runtime helpers separately verified'],scope_boundary='验证范围为该九个具体实现及所需leaf模型/桥接；完整递归expression emitter、TVM运行语义及编译保持性仍未全量迁移。',review_method='Manual review of original contracts, exact leaf equations, representations and bridge premises; later hashes detect drift, not equivalence.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps(sources,indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n');print('Recorded nine contracts and reviewed leaf model declarations.')
