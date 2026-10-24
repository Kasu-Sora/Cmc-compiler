"""Audit exact function-readiness results and separately account for PC support."""
from pathlib import Path
import hashlib,json,re,shutil
from audit_syntax import coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lib=Q/'Rocq/examples/QCP_demos_human/cmc_function_ready_migration_lib.v'
source=json.loads((R/'metrics/cstar-verification.json').read_text())
assert source['clean'] and source['exit_code']==0
assert source['source_sha256']==sha(R/'baseline/cmc_concrete_function_ready.c')
checks=json.loads((R/'metrics/checks.json').read_text())
for kind in ['development','audit','kernel','publication']:
 last=next(x for x in reversed(checks) if x['kind']==kind)
 assert last['exit_code']==0,(kind,last)
 assert last['source_sha256']==sha(R/'target/FunctionReadinessAudit.v' if kind=='audit' else lib)
audit=next(x for x in reversed(checks) if x['kind']=='audit');audit_text=Path(audit['log']).read_text()
assert audit_text.count('Closed under the global context')==8 and 'Axioms:' not in audit_text
kernel=next(x for x in reversed(checks)if x['kind']=='kernel')
assert 'SimpleC.EE.QCP_demos_human.FunctionReadinessAudit' in kernel['command']
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
mapping={
 'cm_function_pcs_current':['cm_prove_function_pcs_current','cm_function_pcs_current'],
 'cm_function_id_ready_from_wf':['cm_prove_function_id_ready_from_wf','cm_function_id_ready_from_wf'],
 'cm_concrete_function_ready_from_wf':['cm_prove_concrete_function_ready_from_wf','cm_concrete_function_ready_from_wf'],
 'cm_concrete_functions_suffix_ready':['cm_prove_concrete_functions_suffix_ready','cm_concrete_functions_suffix_ready'],
 'cm_concrete_functions_ready_from_wf':['cm_prove_concrete_functions_ready_from_wf','cm_concrete_functions_ready_from_wf']}
common_mapping={'cm_function_prefix_step':['cm_prove_function_prefix_step','cm_function_prefix_step'],'cm_function_pc_step':['cm_prove_function_pc_step','cm_function_pc_step']}
common_source={r['name']:r for r in sd['declarations']}
assert sorted(common_source)==sorted(n for ns in common_mapping.values()for n in ns)
rows=[]
for r in regions:
 if r['kind']not in ['Lemma','Theorem']:continue
 assert r['ending']=='Qed'
 cat='module' if r['name']in mapping else 'new_common_dependency'
 sr=srows if cat=='module' else common_source
 names=(mapping if cat=='module' else common_mapping)[r['name']]
 rows.append(dict(name=r['name'],category=cat,target_span=line_span(txt,r['start'],r['end']),target_nonblank_lines=sum(bool(l.strip())for l in mask[r['start']:r['end']].splitlines()),source_declarations=names,source_nonblank_lines=sum(sr[n]['nonblank_lines']for n in names),sha256=hashlib.sha256(txt[r['start']:r['end']].encode()).hexdigest()))
assert len(rows)==7
internal=['cm_join_ready_facts','cm_i32_from_bounds']
assert sorted(n for ns in mapping.values()for n in ns)+sorted(internal)!=[]
assert set(n for ns in mapping.values()for n in ns)|set(internal)==set(srows)
assert sum(r['source_nonblank_lines']for r in rows if r['category']=='module')+sum(srows[n]['nonblank_lines']for n in internal)==se['totals']['proof']==411
assert sd['public_proof_lines']==152 and sd['definition_lines']==0
reuse=['cm_functions_length_bound__model_length_bound','cm_stmt_temps_ready_with_bound','cm_stmt_code_count_nonnegative','cm_slots_size_matches__temp_context','cm_slots_nonnegative','cm_slots_safe']
usage=[dict(name=n,manual_references=len(re.findall(r'\b'+n+r'\b',mask)),new_lines=0)for n in reuse]
assert all(x['manual_references']for x in usage)
manifest=[]
for p in [lib,lib.with_suffix('.vo'),R/'target/FunctionReadinessAudit.v']:
 if p.parent!=R/'target':shutil.copy2(p,R/'target'/p.name)
 manifest.append(dict(path=str(p),sha256=sha(p)))
(R/'target/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
exports=re.findall(r'PROOF extern thm (\w+);',(R/'baseline/cmc_concrete_function_ready.h').read_text())
assert len(exports)==4 and set(exports)<=mapping.keys()
result=dict(status='passed',direction='C*/HOL -> Rocq (QCP shared mathematical library)',source_unit='cmc_concrete_function_ready.c',runtime_functions=0,annotation=0,specification_plus_annotation=0,c_vcs='not applicable: pure PROOF module',new_definitions=0,module_theorems=5,new_common_dependency_theorems=2,total_library_theorems=7,source_exported_theorems=exports,source_proof_lines=411,target_proof_lines=sum(x['target_nonblank_lines']for x in rows if x['category']=='module'),source_new_common_proof_lines=152,target_new_common_proof_lines=sum(x['target_nonblank_lines']for x in rows if x['category']=='new_common_dependency'),new_common_definition_lines=0,source_total_proof_lines=563,target_total_proof_lines=sum(x['target_nonblank_lines']for x in rows),source_effort=se,source_additional_dependencies=sd,per_theorem=rows,same_module_shared_support=[srows[n]for n in internal],reused_helper_usage=usage,reused_audit_helper='cm_emit_stmt_length__stmt_capacity',source_replay=source,checks=checks,all_seven_theorems_and_definition_equivalence_closed_under_global_context=True,new_assumptions=False,trusted_auto_witnesses_added=0,proof_regions_end_in_qed=True,unchanged_files=unchanged,historical_source_active_seconds=None,human_active_seconds=None,model_active_seconds=None,
 semantic_review={
 'coverage':'Four original header exports plus the internal functions-suffix theorem retained. Two newly needed common prefix/PC-step theorems translated with their original bounds. Source proof-building gnode utilities are counted, not treated as runtime C.',
 'definitions':'Existing concrete_function_ready and concrete_functions_ready reused unchanged. A named audit theorem equates the count-normalized function predicate with all 18 original source conjuncts, including actual emitted stmt length; nil/cons equations checked. No new model definition.',
 'function_pc_step':'Unconditional with respect to typing/readiness: only 0<=fid<length functions. Prefix theorem keeps arbitrary functions list and offset length(program_functions)-length(functions)+index. No assumption that the list is an actual suffix.',
 'function_id':'Preserves wf_program and fid bounds. Reuses the old 21*length<=code_size theorem using counts already contained in wf_program; no new public premise.',
 'single_function':'Original wf, index range, counts and both adjacent PC bounds preserved. All 18 readiness conjuncts retained, including member safety, statement temporary safety, frame/offset upper bounds and PC step.',
 'frame_arithmetic':'Retains source frame bound 1048560 and member safety bound 1048576; bridges representation/semantic sizes with existing theorems. Neither replaced by a looser prerequisite.',
 'suffix':'Preserves nonnegative fid and exact length alignment, counts and PC predicates. No artificial list identity or suffix membership hypothesis; nil case retained.',
 'parametric_scope':'Existing arbitrary lookup policy and cm_codegen_obligations parameters retained. Four codegen obligations remain under original wf_program; this does not discharge their concrete CMC/TVM instantiation.',
 'trust':'Seven library results plus original-definition equivalence are closed under global context; recursive coqchk checks library and audit module. Inherited framework axioms are logged but not used by these proofs; no proof_auto/manual imported.',
 'scope':'Completes function_ready proof support only; compile_ready, top-level concrete compilation and semantic preservation remain separate tasks.'},
 counting_note='Nonblank non-comment lines, statements and Proof/Qed included. Module proof 411/72 includes source 16-line same-file shared support once. External PC support 152/31 counted separately despite residing in the same target public library. Total 563/103, no double charge. Reused models/helpers cost zero increment. Source framework guards 5 lines, target imports and audit harness excluded; audit size recorded separately.')
assert (result['target_proof_lines'],result['target_new_common_proof_lines'],result['target_total_proof_lines'])==(72,31,103)
result['development_attempts']=dict(coqc_calls=sum(x['kind']=='development'for x in checks),coqc_failed=sum(x['kind']=='development'and x['exit_code']!=0 for x in checks),preparation_failures_before_coqc=1,preparation_failure_log=str(R/'logs/preparation-failure.txt'))
audit_source=(R/'target/FunctionReadinessAudit.v').read_text()
result['excluded_audit_harness_lines']=sum(bool(l.strip())for l in coq_mask(audit_source).splitlines())
(R/'metrics/effort.json').write_text(json.dumps(result,indent=2)+'\n')
table='\n'.join(f"| `{x['name']}` | {x['source_nonblank_lines']} | {x['target_nonblank_lines']} | {'模块' if x['category']=='module' else '新增公共依赖'} |"for x in rows)
report=f'''# cmc_concrete_function_ready.c：C* → Rocq

已完成原 4 条公开定理与 1 条函数列表后缀定理，另补齐必要的 2 条公共 PC 支持定理。目标为 QCP 可复用纯数学库，运行时函数和 C annotation 均为 0。

## 原定义与定理含义

直接复用原先迁移的 cm_concrete_function_ready 与 cm_concrete_functions_ready 定义。审计定理 function_ready_original_definition 验证原单函数 readiness 的全部 18 项结论，包括实际 cm_emit_stmt 输出长度；通过已验证的 cm_emit_stmt_length__stmt_capacity 与既有计数形式等价。此等价无额外前提，列表 nil/cons 方程也通过核验。

主定理保留 wf_program、fid 范围、函数计数可表示性及当前／下一函数 PC 的可表示性，推出完整单函数 readiness。由此在原长度对齐条件下证明后缀列表，并推出从编号 0 开始的整个函数列表 readiness。没有增加“列表必须是实际后缀”、合法查找策略或已有 temps_safe 等条件。

帧上界 1048560、成员安全界 1048576、32 位上界 2147483647 均保留；参数／局部成员尺寸与语义尺寸的桥复用旧引理。policy 与 cg 仍任意，原 wf_program 中四项 codegen obligations 未被删除，也未声称它们的具体语义实例化在本轮得到证明。

## 验证与信任

C* 隔离重放通过，耗时 {source['verification_seconds']:.3f} 秒；VC、axioms、strategies 全为空。Rocq 8.20.1 开发编译、7 条精确签名审计、定义等价核验、递归 coqchk（含审计模块）与正式路径编译全部通过。

7 条库定理及原定义等价证明的 Print Assumptions 全为 Closed under the global context，无新增 Admitted/Axiom/Parameter 或可信自动 witness。导入框架中的既有公理仍在内核日志中列出，但本例结果不依赖它们；未导入 proof_auto/proof_manual。

{unchanged['source-manifest.json']} 个源 C/H 与 {unchanged['target-manifest.json']} 个既有目标源文件及冻结依赖源码／对象哈希均保持不变。

## Proof 工作量

| 类别（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
| 本模块 proof，含内部共用支持 | 411 | 72 |
| 新增公共依赖 proof：prefix/PC step | 152 | 31 |
| 合计 | 563 | 103 |
| 新增模型／定义 | 0 | 0 |
| annotation / specification+annotation | 0 / 0 | 0 / 0 |

新增公共支持的两条定理与模块定理放在同一个目标库，但成本只在公共依赖行计一次。源同文件共用事实拼接／i32 包装共 16 行已计入 411 行；目标复用 conjunction 和算术 tactic，不单独造包装定义。旧 count-bound、temp-ready、成员安全和尺寸桥成本为 0 增量。

| 定理 | C* proof | Rocq proof | 归属 |
|---|---:|---:|---|
{table}
| 同文件共用 cm_join_ready_facts / cm_i32_from_bounds | 16 | 已包含于各证明 | 模块 |

Proof 含声明及 Proof/Qed；源框架守卫 5 行、目标 import/scope 与审计 harness 排除。逐区域行号、哈希与旧引理引用在 effort.json 中。开发 coqc {result['development_attempts']['coqc_calls']} 次，失败 {result['development_attempts']['coqc_failed']} 次（包括定位输出）；另有 1 次文件创建前的准备调用失败，未启动 coqc，单独记录。修复为 prefix 零分支算术归一化和保留已有合取假设，没有修改公开规格。历史工时未知记 null，行数不代表工具耗时或难度排名。

## 产物

- [正式公共库]({lib})
- [完整计量、语义审计及验证记录]({R/'metrics/effort.json'})
- [全部检查命令与日志]({R/'metrics/checks.json'})
- [原定义／定理核验]({R/'target/FunctionReadinessAudit.v'})

运行时仍为 30 个实现单元、131 个函数；readiness 纯支持累计 5 项：data_ready、program_ready、code_ready、temp_ready、function_ready。下一项为 cmc_concrete_compile_ready.c；尚未宣称整个 CMC/TVM 证明完成。
'''
(R/'REPORT.md').write_text(report)
print(json.dumps({k:result[k]for k in ['status','source_proof_lines','target_proof_lines','source_new_common_proof_lines','target_new_common_proof_lines','development_attempts','unchanged_files']},indent=2))
