"""Freeze the actual main-owned semantic review; hashes detect drift, not equivalence."""
from pathlib import Path
import json,re,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases');sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_expr_dispatch_migration.c').read_text();src=(R/'baseline/cmc_concrete_emit_expr_dispatch.c').read_text().splitlines();fs=json.loads((R/'metrics/source-functions.json').read_text());assert len(fs)==1
f=next(f for f in c_functions(c) if not f['prototype']);assert f['name']=='cm_emit_leaf_expr'
a=fs[0];source='\n'.join('\n'.join(src[a-1:b])for a,b in a['specification']);target='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S));assert 'Require' in target and 'Ensure' in target
rows=[dict(function=f['name'],source_contract_sha256=sha(source),target_contract_sha256=sha(target),checks=['All original pure conditions retained: lvalue bounds, leaf, wf/typed program, total f lookup, expr wf/counts, structs/globals/strings safe and aggregate size bound','All original program/function/expression resources retained; exact consumed/appended code and arbitrary tail','Leaf logical witness has proved coverage and uniqueness, preserving the source leaf domain','Four verified helper BODY contracts retained; their premises are derived rather than added as input requirements'])]

lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_lib.v').read_text();models=[];baseline=[]
source_map={'cm_dispatch_leaf':'cmc_concrete_defs.c cm_leaf_expr_def: kind = 0 or 1 or 9 or 10'}
for x in coq_regions(lib):
 fragment=lib[x['start']:x['end']];item=dict(name=x.get('name'),kind=x['kind'],nonblank_lines=sum(bool(l.strip())for l in coq_mask(fragment,False).splitlines()),sha256=sha(fragment));baseline.append(item)
 if x['kind']in ['Definition','Fixpoint','Record','Inductive']:
  assert x['name']in source_map,'Unreviewed model: '+x['name'];item['source_declaration']=source_map[x['name']];models.append(item)
assert {m['name']for m in models}==set(source_map)
audit=dict(status='Contract/model review recorded; final verification pending',contracts=rows,annotation_stage_model_declarations=models,model_review=[
 'cm_dispatch_leaf逐项对应原kind析取；目标已有cm_leaf_expr是独立类型，因此使用不同谓词名称。',
 '原e与leaf表示见证通过e=cm_leaf_source_expr leaf相连；coverage双向证明覆盖原leaf条件，unique保证表示唯一。',
 'cm_leaf_code_for复用四条已审计源方程及lvalue选择，未为非leaf构造子编造输出。pc/temp在这些方程中不影响代码，C参数仍保留。',
 '常量type_code_wf可由原counts推出；最终手工证明使用原expr_wf的整数类型条件。字符串sid范围来自counts，sizeof asked合法性来自expr_wf；完整纯事实与空间资源保留。',
 '既有wf_program与四项codegen obligations参数保持，四条helper契约规范化一致；未导入旧manual/auto。'],adaptations=['Explicit leaf-view witness with proved source-domain coverage','Existing policy/codegen-obligation parameter boundary','Four verified leaf body helper contracts reused'],scope_boundary='仅验证叶子表达式分派实现；完整递归表达式、TVM语义和编译保持性未全量迁移。',
review_method='Manual source/target contract and model correspondence review; later hashes only guard drift.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(R/'metrics/source-contracts.json').write_text(json.dumps([dict(function=f['name'],contract=source)],indent=2)+'\n');(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n');print('Recorded reviewed dispatch contract and models.')
