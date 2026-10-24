"""Gate the exact temp-readiness statements and publish audited effort."""
from pathlib import Path
import hashlib,json,re,shutil
from audit_syntax import coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lib=Q/'Rocq/examples/QCP_demos_human/cmc_temp_ready_migration_lib.v'
source=json.loads((R/'metrics/cstar-verification.json').read_text())
assert source['clean'] and source['exit_code']==0
assert source['source_sha256']==sha(R/'baseline/cmc_concrete_temp_ready.c')
checks=json.loads((R/'metrics/checks.json').read_text())
for kind in ['development','audit','kernel','publication']:
 last=next(x for x in reversed(checks) if x['kind']==kind)
 assert last['exit_code']==0,(kind,last)
 assert last['source_sha256']==sha(R/'target/TempReadinessAudit.v' if kind=='audit' else lib)
audit=next(x for x in reversed(checks) if x['kind']=='audit')
audit_text=Path(audit['log']).read_text()
assert audit_text.count('Closed under the global context')==13 and 'Axioms:' not in audit_text
unchanged={}
for file in ['source-manifest.json','target-manifest.json']:
 manifest=json.loads((R/'baseline'/file).read_text());unchanged[file]=len(manifest)
 for row in manifest:assert sha(Path(row['path']))==row['sha256'],row['path']
deps=json.loads((R/'baseline/dependency-snapshot.json').read_text())
for row in deps['base_sources']+deps['base_artifacts']:
 assert sha(R/'build'/row['relative_path'])==row['sha256']
 assert sha(Q/row['relative_path'])==row['sha256']
assert not any(re.search(r'_proof_(auto|manual)',x['relative_path'])for x in deps['base_sources'])
txt=lib.read_text();mask=coq_mask(txt);regions=coq_regions(txt)
assert not re.search(r'\b(?:Admitted|Axiom|Parameter|Abort)\b',mask)
assert not any(r['kind']in ['Definition','Fixpoint','Inductive','Record']for r in regions)
se=json.loads((R/'metrics/source-effort.json').read_text());sd=json.loads((R/'metrics/source-additional-definitions.json').read_text())
srows={r['name']:r for r in se['source_top_level_proof_helpers']if r['kind']=='proof'}
groups=[
 ('maximum_and_tail_arithmetic',['cm_prove_imax_upper','cm_temp_imax_upper','cm_prove_imax_add_upper','cm_temp_imax_add_upper','cm_prove_binary_tail_positive','cm_binary_tail_positive'],['cm_temp_imax_upper','cm_temp_imax_add_upper','cm_binary_tail_positive']),
 ('node_and_pair_projection',['cm_prove_expr_count_node_from_tree','cm_expr_count_node_from_tree','cm_prove_args_count_node_from_tree','cm_args_count_node_from_tree','cm_prove_args_temps_safe_pair','cm_args_temps_safe_pair','cm_prove_stmt_count_node_from_tree','cm_stmt_count_node_from_tree'],['cm_expr_count_node_from_tree','cm_args_count_node_from_tree','cm_args_temps_safe_pair','cm_stmt_count_node_from_tree']),
 ('expression_and_arguments',['cm_expr_ready_ih','cm_prepare_expr_ready_case','cm_prove_expr_and_args_temps_ready','cm_expr_and_args_temps_ready','cm_expr_temps_ready_from_counts','cm_args_temps_ready_from_counts'],['cm_expr_temps_ready_from_counts','cm_args_temps_ready_from_counts','cm_expr_and_args_temps_ready']),
 ('statements',['cm_expr_ready_from_counts','cm_stmt_ready_ih','cm_prepare_stmt_ready_case','cm_prove_stmt_temps_ready','cm_stmt_temps_ready_with_bound','cm_prove_stmt_temps_ready_from_counts','cm_stmt_temps_ready_from_counts'],['cm_stmt_temps_ready_with_bound','cm_stmt_temps_ready_from_counts']),
 ('same_module_shared_support',['cm_add_ready_parts','cm_close_ready_arithmetic','cm_reduce_expr_ready_branch','cm_find_open_temp_leaf'],['cm_args_temps_ready_cons'])]
rows=[]
for r in regions:
 if r['kind']not in ['Lemma','Theorem']:continue
 assert r['ending']=='Qed'
 rows.append(dict(name=r['name'],target_span=line_span(txt,r['start'],r['end']),target_nonblank_lines=sum(bool(l.strip())for l in mask[r['start']:r['end']].splitlines()),sha256=hashlib.sha256(txt[r['start']:r['end']].encode()).hexdigest()))
assert len(rows)==13
assert sorted(n for _,ss,_ in groups for n in ss)==sorted(srows)
assert sorted(n for _,_,tt in groups for n in tt)==sorted(r['name']for r in rows)
tr={r['name']:r for r in rows}
group_rows=[dict(group=n,source_declarations=ss,target_theorems=tt,source_proof_lines=sum(srows[x]['nonblank_lines']for x in ss),target_proof_lines=sum(tr[x]['target_nonblank_lines']for x in tt))for n,ss,tt in groups]
assert sum(r['source_proof_lines']for r in group_rows)==se['totals']['proof']==788
assert sd['public_proof_lines']==0 and sd['definition_lines']==0
reuse=['cm_args_pair_safe__expr_safety','cm_expr_temps_nonnegative__index_bounds','cm_char_normalize_count_nonnegative','cm_expr_code_counts_nonnegative','cm_expr_counts_repr_call','cm_expr_safe_call','cm_expr_tpair_call','cm_expr_counts_call']
usage=[dict(name=n,manual_references=len(re.findall(r'\b'+n+r'\b',mask)),new_lines=0)for n in reuse]
assert all(x['manual_references']for x in usage)
manifest=[]
for p in [lib,lib.with_suffix('.vo'),R/'target/TempReadinessAudit.v']:
 if p.parent!=R/'target':shutil.copy2(p,R/'target'/p.name)
 manifest.append(dict(path=str(p),sha256=sha(p)))
(R/'target/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
exports=re.findall(r'PROOF extern thm (\w+);',(R/'baseline/cmc_concrete_temp_ready.h').read_text())
assert len(exports)==4 and set(exports)<=tr.keys()
result=dict(status='passed',direction='C*/HOL -> Rocq (QCP shared mathematical library)',source_unit='cmc_concrete_temp_ready.c',runtime_functions=0,annotation=0,specification_plus_annotation=0,c_vcs='not applicable: pure PROOF support',new_definitions=0,new_theorems=13,source_exported_theorems=exports,source_proof_lines=se['totals']['proof'],target_proof_lines=sum(x['target_nonblank_lines']for x in rows),new_external_common_definition_lines=0,new_external_common_proof_lines=0,new_public_library_theorems=13,new_public_library_proof_lines=sum(x['target_nonblank_lines']for x in rows),source_effort=se,source_additional_dependencies=sd,per_theorem=rows,grouped_cost=group_rows,reused_helper_usage=usage,source_replay=source,checks=checks,all_thirteen_theorems_closed_under_global_context=True,new_assumptions=False,trusted_auto_witnesses_added=0,manual_proof_regions_end_in_qed=True,unchanged_files=unchanged,historical_source_active_seconds=None,human_active_seconds=None,model_active_seconds=None,
 semantic_review={
 'coverage':'All four public theorem constants; seven static helper theorem statements and the combined expr/args theorem retained. The target adds one cons-step lemma for internal arithmetic reuse. Source gnode functions map to Rocq proof scripts, not runtime C wrappers.',
 'definitions':'Source module defines no mathematical models. Count, temporary-slot, pair-safety and recursive representation models imported unchanged from accepted counts/layout libraries.',
 'premises':'The four public results require only the original recursive counts_representable predicate; no typed_program, expression well-formedness, valid fid/callee, nonempty lists, or extra temporary-slot assumptions introduced.',
 'expressions':'14 AST constructors, all integer op choices, logical short circuits, address/dereference, member/variable array tests, and recursively nested calls. Preserves both left/right temporary bounds and the strict right-child <2147483647 condition even for short-circuit binary expressions.',
 'arguments':'Empty and nonempty lists; preserves pair count/depth bounds, count+depth<=2147483647, strict tail arity <2147483647, recursive child safety, and args_temps<=args code count. Cons arithmetic shared inside/outside nested expression recursion.',
 'statements':'All 11 constructors. Keeps stmt safety plus stemps<=stmt code count and the safety-only corollary. Initialization and return use the existing character-normalization nonnegativity theorem.',
 'lookup_policy':'Existing universal lookup-policy parameter retained; no restriction or concrete value for malformed/out-of-range function lookups.',
 'trust':'All 13 final theorems Print Assumptions closed under the global context; recursive coqchk can list inherited framework axioms, none used by these results. No generated proof_auto/proof_manual imported.',
 'scope':'Completes temp_ready support, not function_ready, compile_ready, top-level compiler correctness or TVM semantics.'},
 counting_note='Nonblank non-comment lines, including theorem statements and Proof/Qed. Source internal shared support is 121 lines counted once within the 788 module lines; target cons-step support is counted once inside module proof. All target proof is reusable public-library code; external common dependency increment is zero. Source 5 guard/scaffolding lines, target imports/scopes and audit harness excluded. Historical time unknown. Line counts are final artifact size, not comparative development time.')
result['development_attempts']=dict(calls=sum(x['kind']=='development'for x in checks),failed=sum(x['kind']=='development'and x['exit_code']!=0 for x in checks))
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
labels={'maximum_and_tail_arithmetic':'max 与 binary-tail 算术','node_and_pair_projection':'节点／pair 投影','expression_and_arguments':'表达式与参数列表','statements':'语句','same_module_shared_support':'同文件共用支持（只计一次）'}
table='\n'.join(f"| {labels[x['group']]} | {x['source_proof_lines']} | {x['target_proof_lines']} |"for x in group_rows)
report=f'''# cmc_concrete_temp_ready.c：C* → Rocq

已完整迁移临时槽 readiness 证明。目标是 QCP 可复用数学库，源文件无运行时函数；annotation 与 specification+annotation 均为 0，定理陈述计入 proof。

## 含义与覆盖

原头文件 4 条定理全部保留：表达式安全与左右值临时槽界、参数列表安全与总临时槽界、语句安全与临时槽界、语句安全推论。唯一前提仍是各自的 counts_representable，没有增加类型正确性、有效函数索引或临时槽预设上界。

覆盖 14 种表达式、空／非空参数列表和 11 种语句构造子；保留原 2147483647 上界、右子表达式严格界、参数尾 arity 严格界以及 count+depth 上界。临时槽需求不超过代码计数的结论没有删减。既有 lookup policy 保持任意值，未限定越界查找行为。

源内七条辅助定理、expr/args 合取定理也保留；目标新增一条 cons-step 支持引理，总计 13 条 Qed 定理。已有 counts/layout 定义直接导入，源与目标新增数学定义均为 0。

## 验证

- C* 隔离重放通过，耗时 {source['verification_seconds']:.3f} 秒；verification_conditions、axioms、strategies 全为空。
- Rocq 8.20.1 编译、13 条精确签名审计、递归 coqchk、正式路径编译均通过。
- 13 条定理 Print Assumptions 全为 Closed under the global context；新增 Admitted/Axiom/Parameter、可信自动 witness 均为 0。
- 导入环境含既有框架公理，内核日志如实保留；本例定理不依赖这些公理，未导入 proof_auto/proof_manual。
- {unchanged['source-manifest.json']} 个源 C/H、{unchanged['target-manifest.json']} 个既有目标源文件，以及冻结依赖源码和对象哈希保持不变。

## 工作量

| 项目（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
{table}
| 本模块 proof 合计 | {result['source_proof_lines']} | {result['target_proof_lines']} |
| 额外公共依赖新增 proof | 0 | 0 |
| 新增数学定义 | 0 | 0 |
| annotation / specification+annotation | 0 / 0 | 0 / 0 |

13 条目标定理全部放在新公共库中，其 {result['target_proof_lines']} 行已完整计入“本模块 proof”；额外公共依赖为 0，不代表没有新公共证明。八项旧引理／模型方程的实际引用及零增量记录见 effort.json。源内部共用支持 121 行计入模块一次，目标 cons-step 同样只计一次。

源框架守卫 5 行、目标 import/scope 与验证 harness 排除。Proof 包含声明及 Proof/Qed；逐区域行号和哈希保存在指标中。开发编译 {result['development_attempts']['calls']} 次，其中 {result['development_attempts']['failed']} 次失败（包括定位输出）；失败日志全部保留。修复涉及现有引理命名、显式展开算术定义和投影、Ltac 匹配变量、调用分支嵌套递归与初始化 slot 名称衔接，没有改变公开定理前提或结论。历史人工／模型活跃时间未知，记 null；本对比不能推出工具耗时或难度优劣。

## 产物

- [目标公共库]({lib})
- [完整计量与语义审计]({R/'metrics/effort.json'})
- [验证命令、哈希及耗时]({R/'metrics/checks.json'})
- [定理签名与假设核验]({R/'target/TempReadinessAudit.v'})

运行时进度仍为 30 个实现单元、131 个函数。readiness 纯支持已完成 data_ready、program_ready、code_ready、temp_ready 四项；下一项为 function_ready，然后 compile_ready。尚未声称顶层 CMC/TVM 证明全部完成。
'''
(R/'REPORT.md').write_text(report)
print(json.dumps({k:result[k] for k in ['status','source_proof_lines','target_proof_lines','new_theorems','development_attempts','unchanged_files']},indent=2))
