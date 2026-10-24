"""Gate compile-readiness composition, reused definition and incremental cost."""
from pathlib import Path
import hashlib,json,re,shutil
from audit_syntax import coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lib=Q/'Rocq/examples/QCP_demos_human/cmc_compile_ready_migration_lib.v'
source=json.loads((R/'metrics/cstar-verification.json').read_text())
assert source['clean'] and source['exit_code']==0
assert source['source_sha256']==sha(R/'baseline/cmc_concrete_compile_ready.c')
checks=json.loads((R/'metrics/checks.json').read_text())
for kind in ['development','audit','kernel','publication']:
 last=next(x for x in reversed(checks)if x['kind']==kind)
 assert last['exit_code']==0,(kind,last)
 assert last['source_sha256']==sha(R/'target/CompileReadinessAudit.v' if kind=='audit' else lib)
audit=next(x for x in reversed(checks)if x['kind']=='audit');audit_text=Path(audit['log']).read_text()
assert audit_text.count('Closed under the global context')==2 and 'Axioms:' not in audit_text
assert 'SimpleC.EE.QCP_demos_human.CompileReadinessAudit' in next(x for x in checks if x['kind']=='kernel')['command']
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
proofs=[r for r in regions if r['kind']in ['Lemma','Theorem']]
assert len(proofs)==1 and proofs[0]['name']=='cm_concrete_code_ready_from_wf' and proofs[0]['ending']=='Qed'
r=proofs[0];target_lines=sum(bool(l.strip())for l in mask[r['start']:r['end']].splitlines())
se=json.loads((R/'metrics/source-effort.json').read_text());sd=json.loads((R/'metrics/source-additional-definitions.json').read_text())
assert se['totals']==dict(definition=4,proof=23,getter=3,framework_scaffolding=7)
assert sd['public_proof_lines']==0 and sd['definition_lines']==0 and target_lines==7
reuse=['cmc_structs_ready_from_typed','cm_concrete_functions_ready_from_wf']
usage=[dict(name=n,references=len(re.findall(r'\b'+n+r'\b',mask)),new_lines=0)for n in reuse]
assert all(x['references']for x in usage)
# Record the already-published definition, separately from new work.
oldlib=Q/'Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_lib.v';old=oldlib.read_text()
dr=next(x for x in coq_regions(old)if x['name']=='cm_concrete_code_ready')
reused=dict(name='cm_concrete_code_ready',source_definition_lines=4,target_definition_lines=sum(bool(l.strip())for l in coq_mask(old)[dr['start']:dr['end']].splitlines()),incremental_lines=0,target_file=str(oldlib),target_span=line_span(old,dr['start'],dr['end']),sha256=hashlib.sha256(old[dr['start']:dr['end']].encode()).hexdigest(),audit='compile_ready_original_definition; exact conjunction and starting function ID zero')
assert reused['target_definition_lines']==2
manifest=[]
for p in [lib,lib.with_suffix('.vo'),R/'target/CompileReadinessAudit.v']:
 if p.parent!=R/'target':shutil.copy2(p,R/'target'/p.name)
 manifest.append(dict(path=str(p),sha256=sha(p)))
(R/'target/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
result=dict(status='passed',direction='C*/HOL -> Rocq (QCP shared mathematical library)',source_unit='cmc_concrete_compile_ready.c',runtime_functions=0,annotation=0,specification_plus_annotation=0,c_vcs='not applicable: pure PROOF module',module_theorems=1,new_definitions=0,new_common_dependency_theorems=0,source_proof_lines=23,target_proof_lines=7,source_new_common_proof_lines=0,target_new_common_proof_lines=0,new_common_definition_lines=0,reused_definition=reused,source_effort=se,source_additional_dependencies=sd,target_proof_region=dict(name=r['name'],span=line_span(txt,r['start'],r['end']),nonblank_lines=7,sha256=hashlib.sha256(txt[r['start']:r['end']].encode()).hexdigest()),reused_helper_usage=usage,source_replay=source,checks=checks,theorem_and_definition_equivalence_closed_under_global_context=True,new_assumptions=False,trusted_auto_witnesses_added=0,proof_regions_end_in_qed=True,unchanged_files=unchanged,historical_source_active_seconds=None,human_active_seconds=None,model_active_seconds=None,
 semantic_review={
 'definition':'Exact original conjunction: concrete_structs_ready p AND concrete_functions_ready policy p 0 (program_functions p). Reuses its prior function-pc-total definition; no new alias/model or altered starting ID.',
 'theorem':'forall policy cg p, cm_wf_program policy cg p -> cm_concrete_code_ready policy p. Sole source premise retained, no added bounds, typing, or readiness premises.',
 'composition':'Extract typed_program from the original wf_program; use the already-verified typed-to-structs theorem and wf-to-functions theorem. Both original conjuncts retained.',
 'parameters':'Existing arbitrary lookup policy and codegen-obligation parameters preserved. Four source admissibility obligations remain in wf_program; no new axiom and no claim they have been separately discharged.',
 'trust':'Library theorem and definition equivalence closed under global context. Recursive coqchk includes both library and audit; inherited framework axioms not used by these results.',
 'scope':'Completes the compile_ready pure support file and six readiness support units. This theorem concerns code readiness, not a new complete correctness theorem for runtime cmc_compile or CMC/TVM semantic preservation.'},
 counting_note='23 source proof lines and 7 target lines, including statement/Proof/Qed. Existing definition is 4/2 lines but incremental definition cost is zero; do not double count earlier library investment. Source getter 3 and framework registration/guards 7 lines, target import and audit harness excluded. The seven public library proof lines are module proof, not an additional seven dependency lines.')
result['development_attempts']=dict(coqc_calls=sum(x['kind']=='development'for x in checks),coqc_failed=sum(x['kind']=='development'and x['exit_code']!=0 for x in checks))
result['excluded_audit_harness_lines']=sum(bool(l.strip())for l in coq_mask((R/'target/CompileReadinessAudit.v').read_text()).splitlines())
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
(R/'REPORT.md').write_text(f'''# cmc_concrete_compile_ready.c：C* → Rocq

已完成原 code-ready 定义含义核验及唯一公开定理迁移：`cm_wf_program policy cg p -> cm_concrete_code_ready policy p`。原文件为纯 PROOF 支持，没有运行时函数，annotation 为 0。

## 定义与性质

完整复用 function-pc-total 库的 `cm_concrete_code_ready`，仍是结构体 readiness 与从编号 0 开始的整个程序函数列表 readiness 的合取。审计中的 compile_ready_original_definition 精确核验原定义方程，没有新建别名或平行模型。

主定理仅以原 wf_program 为前提，从其中提取 typed_program，复用 cmc_structs_ready_from_typed 与 cm_concrete_functions_ready_from_wf。没有添加额外界、类型或 readiness 假设，也没有省略结论。既有任意 policy／cg 参数保留，wf_program 中四项 codegen admissibility 义务保持原边界。

## 验证

C* 隔离重放通过，耗时 {source['verification_seconds']:.3f} 秒；verification_conditions、axioms、strategies 均为空。Rocq 8.20.1 编译、精确定理签名和定义等价检查、递归 coqchk（库与审计模块）、正式路径编译全部通过。

主定理与定义等价证明的 Print Assumptions 均为 Closed under the global context，无新增 Admitted/Axiom/Parameter 或可信自动 witness。导入框架既有公理在内核日志中保留，但不被本例结果依赖，未导入 proof_auto/proof_manual。

{unchanged['source-manifest.json']} 个源 C/H、{unchanged['target-manifest.json']} 个既有目标源文件，以及冻结依赖源码／对象哈希均保持不变。

## 工作量

| 项目（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
| 本模块 proof | 23 | 7 |
| 额外公共依赖新增 proof | 0 | 0 |
| 新增数学定义 | 0 | 0 |
| 既有定义规模，仅核验、不重复计增量 | 4 | 2 |
| annotation / specification+annotation | 0 / 0 | 0 / 0 |

目标公共库新增的 1 条定理、7 行 proof 已计入模块，不能再计为额外依赖。源 getter 3 行、注册／公理守卫 7 行、目标 import 及验证 harness 排除；proof 包含声明和 Proof/Qed。逐区域行号与哈希见 effort.json。

开发 coqc {result['development_attempts']['coqc_calls']} 次、失败 {result['development_attempts']['coqc_failed']} 次；完整命令、耗时和日志均保留。历史人工／模型活跃时间未知记 null；行数是成品规模，不代表开发时间或工具难度排名。

## 产物与范围

- [正式公共库]({lib})
- [计量与语义审计]({R/'metrics/effort.json'})
- [完整验证记录]({R/'metrics/checks.json'})
- [原定义及定理核验]({R/'target/CompileReadinessAudit.v'})

readiness 纯支持六项已完成：data_ready、program_ready、code_ready、temp_ready、function_ready、compile_ready。运行时仍为 30 个实现单元、131 个函数。接下来是顶层 cmc_compile 组合及剩余语义保持性依赖；本结果不等于整个 CMC/TVM 正确性证明已迁移。
''')
print(json.dumps({k:result[k]for k in ['status','source_proof_lines','target_proof_lines','new_definitions','development_attempts','unchanged_files']},indent=2))
