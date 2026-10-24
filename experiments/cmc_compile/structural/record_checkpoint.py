"""Gate the fourth public-support checkpoint on kernel, assumption and hash checks.
This cannot mark the still-unproved compiler/target simulation complete.
"""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
R=Path(__file__).resolve().parent; E=R.parent; W=E.parent.parent
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='StructuralAudit')
a=next(x for x in reversed(checks)if x['mode']=='development' and x['module']=='StructuralAudit')
assert k['exit_code']==a['exit_code']==0 and k['sha256']==a['sha256']==sha(R/'target/StructuralAudit.v')
log=Path(a['log']).read_text();assert log.count('AUDIT ')==log.count('Closed under the global context')==eff['expected_assumption_audits'] and 'Axioms:'not in log
assert len(pub)==len(eff['modules']) and all(x['exit_code']==0 and sha(Path(x['path']))==x['sha256']for x in pub)
for x in eff['modules']:assert sha(Path(x['file']))==x['sha256']
for x in read(R/'metrics/kernel-input-manifest.json'):assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['vo']))==x['vo_sha256']
for x in read(E/'baseline/source-manifest.json'):assert sha(Path('/Users/nizitong/cmc')/x['path'])==sha(E/'baseline/cstar_project'/x['path'])==x['sha256']
for f in [E/'baseline/target-manifest.json',R/'baseline/previous-public-manifest.json']:
 for x in read(f):assert sha(Path(x['path']))==x['sha256']
for p,h in read(R/'baseline/frozen-inputs.json').items():assert sha(Path(p))==h
for name,p in [('SKILL.md',Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md')),('MIGRATION_PLAN.md',W/'MIGRATION_PLAN.md'),('migration_inventory.csv',W/'migration_inventory.csv')]:assert sha(p)==sha(E/'baseline/documentation-before'/name)
components=read(R/'metrics/invariant-components.json')['components'];verified=[x['name']for x in components if x['transition_status'].startswith('proved')];assert len(verified)==11
remaining=[x['name']for x in components if not x['transition_status'].startswith('proved')];assert len(remaining)==7
failures=[x for x in checks if x['exit_code']]
write(R/'metrics/development-failures.json',dict(attempts=failures,note='All failed development attempts retained. Four boolean-case-expansion runs were terminated after pathological growth; adding andb/orb/negb normalization fixed the repeated branch split. An interactive diagnostic attempt with a temporarily given-up goal failed Qed and produced no accepted module. Final sources contain no admits, placeholders or added axioms; all 101 final proofs pass closed-context and kernel checks.'))
eff.update(tool_seconds=sum(x['seconds']for x in checks),publication_tool_seconds=sum(x['seconds']for x in pub),status='kernel_checked_published_public_support_only')
write(R/'metrics/effort.json',eff)
variants={
 'cm_task_static_step_coordinate':'Uses typed program, source success and coordinates rather than assuming layout readiness. Concrete wf-to-static, initial/step/iter proofs discharge these inputs.',
 'cm_task_budget_step_coordinate':'Uses proved erasure/coordinates/success. No additional capacity bound; original phase/task budget formulas retained.',
 'cm_task_generation_step_coordinate':'Uses static validity, generation and successful-source coordinates. Annotation payload is proved independently with spill consistency and monotone generation limits.',
 'cm_task_static_bases_step_generation':'Uses proved generation bounds plus a local saved-region base refinement. That refinement is initialized and preserved by actual source transitions.',
 'cm_source_termination_base_invariants':'Eleven original components with proved local active-fid, payload and saved-region refinements hold after every n source-annotated steps. No target simulation, TVM termination or cmc_preservation conclusion.'}
write(R/'metrics/signature-audit.json',dict(audited_constants=eff['expected_assumption_audits'],closed_constants=eff['expected_assumption_audits'],new_axioms=[],original_preservation_declared=False,original_success_bridge_declared=False,top_level_contract_modified=False,local_variants=variants))
now=eff['totals'];expected=eff['expected_assumption_audits'];nmodules=len(pub)
checkpoint=dict(status='incremental_public_support_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),top_level_qcp_verified=False,public_modules=nmodules,public_cost=now,assumption_audits=expected,axioms_used_by_new_proofs=[],kernel=k,canonical_publication_all_passed=True,original_components_proved_along_successful_execution=verified,new_components=['cm_task_static_valid','cm_task_budget','cm_task_generation_safe','cm_task_static_bases'],remaining_components=remaining,top_level_vcs_generated=False,skill_updated=False,remaining_obligations=str(R/'metrics/remaining-obligations.json'),note='Four of the eleven requested remaining components are complete in this checkpoint. Seven remain; original preservation, success bridge and top-level QCP are not complete. All local premises are discharged in concrete initial/step/iteration proofs; no contract weakening or assumed transition.')
write(R/'metrics/checkpoint.json',checkpoint)
batches=['semantics','preservation','invariants','structural'];incs=[dict(path=str(E/n/'metrics/effort.json'),totals=read(E/n/'metrics/effort.json')['totals'])for n in batches]
total={key:sum(x['totals'].get(key,0)for x in incs)for key in set().union(*(x['totals']for x in incs))}
status=read(E/'metrics/status.json');status.update(status='in_progress_eleven_support_invariants_verified_full_simulation_pending',public_support_checkpoints=[str(E/n/'metrics/checkpoint.json')for n in batches],latest_public_support_checkpoint=checkpoint,additional_public_dependency_cost_so_far=total,new_verified_public_definitions=total['definitions'],new_verified_public_lemmas=total['lemmas'],skill_updated=False,inventory_success_updated=False,current_dependency_gap='Eleven original invariant components are proved along successful source executions. Pending: layout-ready, runtime, type, tagged-valid, short-ready, code-layout, full target simulation. cmc_preservation, original success bridge and top-level QCP remain incomplete; historical controller report retained unchanged.')
write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall.update(status=checkpoint['status'],additional_public_dependency_cost_so_far=total,public_support_increments=incs,note='Four verified public increments; definitions, lemmas and Ltac counted once. Top-level final annotation/proof and complete C* dependency closure remain null. Partial same-name source lines are not a comparable denominator for a migration ratio.')
overall['target_completed_this_attempt'].update(verified_public_definitions=total['definitions'],verified_public_lemmas=total['lemmas'],public_definition_lines=total['definition_lines'],public_proof_lines=total['proof_lines'])
write(E/'metrics/effort.json',overall)
rows=['| 本批公共模块 | 定义 | 引理 | 定义行 | Proof 行 |','|---|---:|---:|---:|---:|']
for m in eff['modules']:
 c=m['counts'];rows.append(f"| `{Path(m['file']).name}` | {c['definitions']} | {c['lemmas']} | {c['definition_lines']} | {c['proof_lines']} |")
source=read(R/'metrics/source-reference-cost.json')['totals']
(R/'README.md').write_text(f'''# cmc_compile：第四批公共证明支持

本批补齐剩余 11 项中的 **4 项**：static-valid、budget、generation-safe、static-bases。累计原 18 项中的 11 项具备实际 initial/step/任意步数保持性证明。{nmodules} 个新公共库经过编译、{expected} 条假设审计、独立 coqchk，并接入 QCP 正式目录。

**这不是完整迁移成功记录。** 尚缺 layout-ready、runtime、type、tagged-valid、short-ready、code-layout、完整 task-target-sim 共 7 项；cmc_preservation、原 cmc_compile_success_bridge 和顶层 QCP 尚未完成。skill、迁移成功清单和原契约未更改。

## 语义与证明范围

- 静态有效性：完整保留表达式、参数列表、语句、frame 和 task 的原静态谓词。函数体的静态有效性由已有 typed-program/function-wf 导出。嵌套参数递归与公开列表谓词通过证明连接，不能只依赖重命名。
- 临时槽预算：保留各 phase 的 owner、scratch、current-slot 和剩余参数长度约束。复用已验证的表达式临时槽非负性、参数计数/深度引理。覆盖 R/L/S/V/C 与初始调用，不增加 C 容量前提。
- 代际安全：保留值、环境、内存标签、frame、task、spill 和保存的 spill-frame 的代际条件。证明转换/加载/存储、局部分配、调用/恢复、参数存储的保持性；证明实际 source-step 的 generation-limit 不减，再将 annotation payload 保持性与 source 保持性组合。任意 HD 默认解释仍保留，恢复保存 spill 时通过已验证 spill 一致性获得非空性。
- 静态区域基址：保留 cm_region_bases_below_equal、cm_static_regions、cm_task_static_bases。证明新动态区域不会遮蔽静态代际；证明恢复操作在当前/保存区域具有共同基址时仍保持该基址。额外记录 frame 中保存区域的基址性质，并证明初始和逐步保持。
- cm_source_termination_base_invariants 从原 semantic-wf 与实际 source-terminates 推出任意 n 步的十一项支持性质。五项新增本地定义用于合取与 saved-region refinement，**没有作为 C Require，也没有将待证目标模拟作为前提**。

原 23 个公共库原样复用，复用源码新增成本为 0。27 项定义映射原 HOL 定义，5 项为本地辅助定义。具体定义、来源、哈希及签名变体见 metrics/definition-correspondence.json、source-reference-manifest.json、signature-audit.json。带 coordinate/generation 后缀的局部 step 定理不冒充原 layout-ready 前提的同名定理。

## 新增公共成本

非空非注释物理行口径，proof 含引理陈述、Proof/Qed 和 Ltac；定义单独计数，工具与自动生成的审计文件不计入数学 proof。全部新辅助引理均计费。历史人工开发时间未知，保持 null；实测命令耗时和失败次数在 metrics/checks.json、effort.json。

'''+ '\n'.join(rows)+f'''

本批：{now['definitions']} 个定义、{now['lemmas']} 条引理，定义 {now['definition_lines']} 行，proof {now['proof_lines']} 行（引理 {now['lemma_lines']} + {now['automation_declarations']} 个 Ltac 共 {now['automation_lines']} 行）。新增运行时函数、C annotation 均为 0；此处是公共数学依赖的成本，不能当作顶层案例已完成的成本。

四批累计：{total['definitions']} 个定义、{total['lemmas']} 条引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行。C* 同名参照切片：定义 {source['definition_lines']} 行、直接 proof 构造器 {source['proof_constructor_lines']} 行、常量装配 {source['proof_constant_scaffolding_lines']} 行；该切片不含完整传递依赖，且构造分支书写格式不同，**不能拿它与全部 QCP proof 相除作为效率结论**。C* 顶层基线仍为 specification 12 行、annotation 2 行/2 条、案例 proof 499 行，成功桥公共 proof 42 行另列；QCP 顶层最终值仍未产生。

## 验证与重放

{expected} 条 Print Assumptions 均 Closed under the global context，coqchk 退出 0（{k['seconds']:.2f} 秒），正式公共库编译全部通过。最终源码无 Axiom、Parameter、Admitted、admit、Abort。传递环境的历史公理不等于新定理使用公理；本批逐条闭合审计明确列出实际假设。

保留全部失败与中止记录。布尔分支自动化一度未化简已拆开的 andb/orb，重复展开导致膨胀；补齐归一化后同一值分支恢复为有限检查。一次临时诊断给出的未完成目标在 Qed 处失败，没有被编译为可接受模块或发布；最终证明已完整重做并内核核验。

518 个原源文件、185 个旧目标文件、23 个已有公共库、skill/计划/清单哈希均未变。此前 C* 顶层完整重放已通过，本批不重复重跑；本批不是单 C 验证，没有新建 controller run，也未绕过原 controller。

重放按 publish.py 中的依赖顺序运行 check.py development MODULE；运行 source_reference_cost.py 生成成本与 StructuralAudit，然后 check.py development StructuralAudit，待其完成再 check.py kernel StructuralAudit。kernel-input-manifest 固定这次检查的源和 .vo 哈希；publish.py 通过门禁后才复制正式库，record_checkpoint.py 通过全部门禁后才更新本报告。下一步需继续剩余七项及完整保持性闭包，再恢复原 annotation owner/controller 的顶层符号执行和终检；顶层通过后才能更新 skill。
''')
backup=E/'REPORT-before-structural.md'
if not backup.exists():shutil.copy2(E/'REPORT.md',backup)
(E/'REPORT.md').write_text(f'''# cmc_compile：十一项模拟支持不变量已验证，顶层仍未完成

本批补齐剩余 11 项中的 **4 项**：静态有效性、临时槽预算、代际安全、静态区域基址。累计原 18 项中的 11 项已有具体初始、逐步及任意步数保持性证明，复用此前 23 个公共库。详见 [第四批验证与成本](structural/README.md)。

**仍缺 7 项：layout-ready、runtime、type、tagged-valid、short-ready、code-layout、完整 target-sim。cmc_preservation、原 cmc_compile_success_bridge 和顶层 QCP 尚未完成；skill 未更新。** 本批支持性质没有替代目标模拟，没有新增 C Require。见 [剩余义务](structural/metrics/remaining-obligations.json)。

| 工作量 | C* 顶层基线 | QCP 顶层最终值 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 对应统计未完成 | 未完成 |

新增公共成本：{now['definitions']} 个定义、{now['lemmas']} 条引理，定义 {now['definition_lines']} 行、proof {now['proof_lines']} 行（含 {now['automation_lines']} 行 Ltac）。四批累计 {total['definitions']} 个定义、{total['lemmas']} 条引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行。完整可比依赖成本和最终比率仍为 null。

本批 {expected} 条假设审计闭合，独立 coqchk 通过（{k['seconds']:.2f} 秒），{nmodules} 个正式公共库编译通过。原 C* 顶层重放此前通过（约 1040 秒），原源码、旧目标、前批公共库及 skill/计划/清单均保持哈希一致。原 controller run 与 annotation owner 保留，顶层 VC 尚未生成。
''')
print(json.dumps(dict(increment=now,cumulative=total,kernel_seconds=k['seconds'],verified_components=verified,remaining_components=remaining),ensure_ascii=False))
