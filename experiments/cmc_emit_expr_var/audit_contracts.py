"""Freeze the actual main-owned semantic review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_expr_var_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_expr_var.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());assert len(fs)==1
f=next(f for f in c_functions(c) if not f['prototype']);assert f['name']=='cm_emit_var_expr'
a=fs[0];source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
rows=[dict(function=f['name'],source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=['Original lvalue/slot bounds, constructor identity, wf_program, total f lookup, binding_valid and type_code_wf retained in pre/post','Original params/locals slots_wf and all globals/member-safe facts retained in pre/post','Full program/function/expression ownership retained; exact code consumption, output append and arbitrary tail','No added fid bounds, binding type equality, scalar or typed input requirement'])]
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_expr_var_migration_lib.v').read_text();models=[];baseline=[]
source_map={'cm_var_lcode':'cm_emit_expr_pair.Var lcode + cm_lcode_of + cm_emit_lvalue','cm_var_rcode':'cm_emit_expr_pair.Var rcode + cm_rcode_of + cm_emit_rvalue; existing array code encoding','cm_var_code_for':'cm_expr_code_for restricted under CMVarE constructor premise'}
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map,'Unreviewed model: '+x['name'];item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit=dict(status='Contract/model review recorded; final verification pending',contracts=rows,annotation_stage_model_declarations=models,model_review=[
'cm_var_lcode直接复用既有binding_address_code；cm_var_rcode为地址加条件加载；cm_var_code_for保留lvalue零/非零选择。',
'变量专用定义不接受任意cm_expr，原契约e=CMVarE支持该特化；源方程不依赖pc/temp，C参数仍保留。',
'源cm_binding_array的global/local非零count与既有cm_binding_array_code编码一致；在原binding_valid与总f查询条件下复用既有lookup语义，参数分支非数组。',
'cm_var_source_equation以布尔取反展开源Var分支；是本地Rocq等式，HOL到Rocq对应另由源审计确认，未宣称跨逻辑元定理。',
'既有wf_program及四个codegen obligation参数保持；三个helper按已验证契约接入。'],adaptations=['Variable-only specialization under original constructor premise','Existing lookup/codegen obligation parameters unchanged','Three verified helper contracts reused'],scope_boundary='仅验证变量表达式生成实现及所需模型；完整递归表达式、TVM语义和编译保持性未全量迁移。',review_method='Manual source/target contract and model correspondence review; later hashes only guard drift.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps([dict(function=f['name'],contract=source)],indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n');print('Recorded reviewed variable contract and models.')
