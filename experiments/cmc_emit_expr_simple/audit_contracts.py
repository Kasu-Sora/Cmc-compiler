"""Freeze the actual main-owned semantic review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_expr_simple_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_expr_simple.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());assert len(fs)==1
f=next(f for f in c_functions(c) if not f['prototype']);assert f['name']=='cm_emit_simple_expr'
a=fs[0];source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
rows=[dict(function=f['name'],source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=['All original pre/post pure facts retained: lvalue, simple, wf/typed program, total lookup, expr wf/counts, params/locals slots wf, structs/globals/strings/member safety and aggregate size bound','Original full program/function/expression resources retained; exact code consumption/append and arbitrary tail','Simple representation witness has proved coverage and uniqueness; no stronger input domain','Both verified helper BODY contracts unchanged; var/leaf premises derived from original facts'])]

lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_lib.v').read_text();models=[];baseline=[]
source_map={'cm_simple_expr':'cmc_concrete_defs.c cm_simple_expr_def: leaf or kind2','cm_simple_view':'Explicit sum of existing leaf view and CMVarE fields under source simple domain','cm_simple_source_expr':'Embedding of selected leaf/var constructors into existing cm_expr','cm_simple_code_for':'Composition of already reviewed leaf/var code_for, source cm_expr_code_for restricted to simple domain'}
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map,'Unreviewed model: '+x['name'];item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit=dict(status='Contract/model review recorded; final verification pending',contracts=rows,annotation_stage_model_declarations=models,model_review=[
 'cm_simple_expr精确对应源leaf-or-kind2；复用已验证cm_dispatch_leaf。',
 'cm_simple_view只含leaf和var，embedding显式嵌入原cm_expr。coverage双向定理和unique证明表示见证不缩小原合法域。',
 'cm_simple_code_for直接调用既有leaf/var代码模型，不为其余构造子伪造输出；这些源方程不依赖pc/temp，运行时参数仍保留。',
 'var分支的slot范围、type_code_wf来自counts，binding_valid来自expr_wf；leaf分支得到既有leaf域。两个helper保留完整上下文及计划。',
 '全部源前后置纯事实保留；原policy/codegen obligations参数化边界不变；两个helper BODY契约规范化一致。'],adaptations=['Explicit simple view with proved coverage and uniqueness','Reuse verified leaf/var models and dispatch correspondence lemmas','Two verified helper BODY contracts reused'],scope_boundary='仅验证simple表达式生成实现；未声称完整递归表达式、TVM语义或编译保持性迁移完成。',
review_method='Manual source/target contract and model correspondence review; later hashes only guard drift.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps([dict(function=f['name'],contract=source)],indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n');print('Recorded reviewed simple contract and models.')
