"""Review exact code-readiness contracts, final artifacts and incremental cost."""
from pathlib import Path
import hashlib,json,re,shutil
from audit_syntax import coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lib=Q/'Rocq/examples/QCP_demos_human/cmc_code_ready_migration_lib.v'
source=json.loads((R/'metrics/cstar-verification.json').read_text())
assert source['clean'] and source['exit_code']==0
assert source['source_sha256']==sha(R/'baseline/cmc_concrete_code_ready.c')
checks=json.loads((R/'metrics/checks.json').read_text())
for kind in ['development','audit','kernel','publication']:
    last=next(x for x in reversed(checks) if x['kind']==kind)
    assert last['exit_code']==0,(kind,last)
    assert last['source_sha256']==sha(R/'target/CodeReadinessAudit.v' if kind=='audit' else lib)
audit=next(x for x in checks if x['kind']=='audit' and x['exit_code']==0)
audit_text=Path(audit['log']).read_text()
assert audit_text.count('Closed under the global context')==6 and 'Axioms:' not in audit_text
for file in ['source-manifest.json','target-manifest.json']:
    for row in json.loads((R/'baseline'/file).read_text()):assert sha(Path(row['path']))==row['sha256'],row['path']
deps=json.loads((R/'baseline/dependency-snapshot.json').read_text())
for row in deps['base_sources']+deps['base_artifacts']:
    assert sha(R/'build'/row['relative_path'])==row['sha256']
    assert sha(Q/row['relative_path'])==row['sha256']
assert not any(re.search(r'_proof_(auto|manual)',x['relative_path'])for x in deps['base_sources'])
txt=lib.read_text();mask=coq_mask(txt);regions=coq_regions(txt)
assert not re.search(r'\b(?:Admitted|Axiom|Parameter|Abort)\b',mask)
assert not any(r['kind']in ['Definition','Fixpoint','Inductive','Record']for r in regions)
rows=[]
mapping={
 'cm_slots_nonnegative':['cm_prove_slots_nonnegative','cm_slots_nonnegative'],
 'cm_slots_safe':['cm_prove_slots_safe','cm_slots_safe'],
 'cm_structs_wf_head':['cm_prove_structs_wf_head','cm_structs_wf_head'],
 'cm_structs_wf_tail':['cm_prove_structs_wf_tail','cm_structs_wf_tail'],
 'cm_structs_safe':['cm_prove_structs_safe','cm_structs_safe'],
 'cmc_structs_ready_from_typed':['cm_prove_structs_ready_from_typed','cmc_structs_ready_from_typed']}
se=json.loads((R/'metrics/source-effort.json').read_text());sd=json.loads((R/'metrics/source-additional-definitions.json').read_text())
source_rows={r['name']:r for r in se['source_top_level_proof_helpers']}
for r in regions:
    if r['kind']not in ['Lemma','Theorem']:continue
    assert r['ending']=='Qed' and r['name']in mapping
    rows.append(dict(name=r['name'],target_span=line_span(txt,r['start'],r['end']),target_nonblank_lines=sum(bool(l.strip())for l in mask[r['start']:r['end']].splitlines()),source_declarations=mapping[r['name']],source_nonblank_lines=sum(source_rows[n]['nonblank_lines']for n in mapping[r['name']]),sha256=hashlib.sha256(txt[r['start']:r['end']].encode()).hexdigest()))
assert len(rows)==6
assert sum(x['source_nonblank_lines']for x in rows)+source_rows['cm_slot_rep_positive']['nonblank_lines']==se['totals']['proof']
assert sd['public_proof_lines']==0 and sd['definition_lines']==0
reuse=['cm_slots_size_matches__temp_context','cm_slots_size_nonnegative__call_bounds','cm_slot_size_matches__temp_context','cm_slots_struct_size_matches']
usage=[dict(name=n,manual_references=len(re.findall(r'\b'+n+r'\b',mask)),new_lines=0)for n in reuse]
assert all(x['manual_references']for x in usage)
manifest=[]
for p in [lib,lib.with_suffix('.vo'),R/'target/CodeReadinessAudit.v']:
    if p.parent!=R/'target':shutil.copy2(p,R/'target'/p.name)
    manifest.append(dict(path=str(p),sha256=sha(p)))
(R/'target/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
result=dict(status='passed',direction='C*/HOL -> Rocq (QCP shared mathematical library)',source_unit='cmc_concrete_code_ready.c',runtime_functions=0,annotation=0,c_vcs='not applicable: pure PROOF module',new_definitions=0,new_theorems=6,source_proof_lines=se['totals']['proof'],target_proof_lines=sum(x['target_nonblank_lines']for x in rows),new_external_common_definition_lines=0,new_external_common_proof_lines=0,reused_definition={'name':'cm_concrete_structs_ready','source_lines':3,'target_lines':1,'incremental_lines':0,'source':'cmc_concrete_code_ready.c','target':'cmc_function_pc_total_migration_lib.v'},source_effort=se,source_additional_dependencies=sd,per_theorem=rows,source_shared_internal_helper=source_rows['cm_slot_rep_positive'],reused_helper_usage=usage,source_replay=source,checks=checks,all_six_theorems_closed_under_global_context=True,new_assumptions=False,trusted_auto_witnesses_added=0,manual_proof_regions_end_in_qed=True,source_unchanged=518,previous_target_sources_unchanged=181,historical_source_active_seconds=None,human_active_seconds=None,model_active_seconds=None,
semantic_review={
 'public_exports':'All four source header exports covered: one reused definition plus the exact nonnegative, safe and typed-to-structs-ready theorems. The audit also checks all three private supporting theorem signatures.',
 'definition':'cm_concrete_structs_ready p is exactly cm_rep_structs_safe (cm_program_structs p), reusing its earlier function-pc-total definition; no parallel model introduced.',
 'slot_nonnegative':'Exact original slot_wf premise and representation-size conclusion; reuses old semantic nonnegativity and the old representation/semantic size equality.',
 'slot_safe':'Exact original upper bound 1048576 and slot_wf premise. Derives head positivity and tail bound; retains all four recursive representation-safety conjuncts and handles empty lists.',
 'struct_head_tail':'Preserves arbitrary structs environment separately from items. Indexed lookups converted only under the original nonnegative/in-range conditions; no out-of-range policy or added premise is assumed.',
 'struct_size_bridge':'Composes old rep-members = slots-size and slots-size = struct-slots-size lemmas under the same slots_wf premise, preserving the original bound and type meaning.',
 'final_theorem':'forall policy p, cm_typed_program policy p -> cm_concrete_structs_ready p. Existing lookup-policy parameterization retained; typed_program is the only premise.',
 'scope':'The code_ready source file proves structure/member readiness, not the later complete cm_concrete_code_ready_from_wf theorem. No runtime C implementation or compilation-preservation result is claimed.'},
counting_note='Nonblank non-comment lines, including theorem statements and Proof/Qed. Source includes 11 shared internal helper lines once; excludes 12 getter and 7 framework lines. All 63 target proof lines are in a new reusable public library and are counted once as module proof; extra dependency cost is 0, not a claim that no public proof was added. Reused definitions and old lemmas cost 0 increment.')
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
table='\n'.join(f"| `{x['name']}` | {x['source_nonblank_lines']} | {x['target_nonblank_lines']} |"for x in rows)
report=f'''# cmc_concrete_code_ready.c：C* → Rocq

完成原文件定义与定理的迁移，目标为 QCP 可复用的纯数学支持库。源文件无运行时函数，C annotation 为 0，不建立虚假的 C 验证单元。

## 原含义和覆盖

原公开导出包括 cm_concrete_structs_ready 定义、cm_slots_nonnegative、cm_slots_safe 和 cmc_structs_ready_from_typed 三条定理，均已覆盖。structs_wf_head、structs_wf_tail、structs_safe 三条内部支持定理也保持原陈述。cm_slot_rep_positive 的证明作用通过已有尺寸对应引理和原 slot_wf 的正尺寸条件完成。

定义直接复用 function-pc-total 公共库的 `cm_concrete_structs_ready p := cm_rep_structs_safe (cm_program_structs p)`。主定理为 `forall policy p, cm_typed_program policy p -> cm_concrete_structs_ready p`，没有增加前提。保留任意结构体环境、空成员列表域、合法索引范围，以及原 1048576 成员总尺寸上界。该文件完成结构体／成员 readiness；完整 code-ready-from-wf 属于后续 compile_ready，尚未声称完成。

## 验证与信任

C* 隔离重放通过，耗时 {source['verification_seconds']:.3f} 秒，VC／axioms／strategies 全为空。Rocq 8.20.1 模块编译、六条签名与定义方程审计、递归 coqchk、正式路径编译均通过。六条定理的 Print Assumptions 全部为 Closed under the global context；新增 Admitted、Axiom、Parameter、可信自动 witness 均为 0。

导入的 QCP 框架环境本身仍含既有公理，coqchk 日志保留其清单；本轮六条定理实际不依赖这些公理。未导入先前案例的 proof_auto／proof_manual。518 个源 C/H 文件、181 个既有目标源文件及冻结依赖源码／对象哈希保持不变。

## Proof 工作量

| 项目（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
| 本模块 proof，含必要内部支持 | {result['source_proof_lines']} | {result['target_proof_lines']} |
| 额外公共依赖新增 proof | 0 | 0 |
| 新增数学定义 | 0 | 0 |
| 既有定义规模，增量不重复计费 | 3 | 1 |
| 运行时 annotation | 0 | 0 |

目标新增公共库内有六条定理、63 行 proof；这些已经全部计入“本模块 proof”。额外公共依赖新增为 0，不表示没有新公共定理。已有四条尺寸／非负性引理实际引用记录于 metrics/effort.json，旧依赖不重复计费。

| 定理 | C* proof | Rocq proof |
|---|---:|---:|
{table}
| 同文件共用 cm_slot_rep_positive 支持 | 11 | 已由旧引理复用及上述证明覆盖 |

源 getter 12 行、注册／公理守卫 7 行以及目标 import/scope、验证 harness 另列排除；proof 包含声明和 Proof/Qed。开发编译 1 次通过，修复 0 次。每次命令、退出状态、哈希和耗时见验证记录。历史人工和模型活跃时间无法独立测量，记为 null；成品行数不能推断工具工时或难度。

## 产物

- [公共库]({lib})
- [完整计量与语义审计]({R/'metrics/effort.json'})
- [验证记录]({R/'metrics/checks.json'})
- [定义及定理签名核验]({R/'target/CodeReadinessAudit.v'})

运行时进度保持 30 个实现单元、131 个函数；readiness 纯支持现已完成 data_ready、program_ready、code_ready 三项。后续为 temp_ready、function_ready、compile_ready，之后继续顶层及保持性闭包。
'''
(R/'REPORT.md').write_text(report)
print(json.dumps({'status':'passed','source_proof':result['source_proof_lines'],'target_proof':result['target_proof_lines'],'new_theorems':6,'new_definitions':0,'extra_common_cost':0},indent=2))
