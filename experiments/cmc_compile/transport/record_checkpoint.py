"""Publish evidence for short readiness only; never mark the compiler complete."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
R=Path(__file__).resolve().parent;E=R.parent;W=E.parent.parent
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='TransportAudit');a=next(x for x in reversed(checks)if x['mode']=='development' and x['module']=='TransportAudit')
assert k['exit_code']==a['exit_code']==0 and k['sha256']==a['sha256']==sha(R/'target/TransportAudit.v')
log=Path(a['log']).read_text();assert log.count('AUDIT ')==log.count('Closed under the global context')==eff['expected_assumption_audits'] and 'Axioms:'not in log
assert len(pub)==len(eff['modules']) and all(x['exit_code']==0 and sha(Path(x['path']))==x['sha256']for x in pub)
for x in eff['modules']:assert sha(Path(x['file']))==x['sha256']
for x in read(R/'metrics/kernel-input-manifest.json'):assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['vo']))==x['vo_sha256']
for x in read(E/'baseline/source-manifest.json'):assert sha(Path('/Users/nizitong/cmc')/x['path'])==sha(E/'baseline/cstar_project'/x['path'])==x['sha256']
for f in [E/'baseline/target-manifest.json',R/'baseline/previous-public-manifest.json']:
 for x in read(f):assert sha(Path(x['path']))==x['sha256']
for p,h in read(R/'baseline/frozen-inputs.json').items():assert sha(Path(p))==h
for name,p in [('SKILL.md',Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md')),('MIGRATION_PLAN.md',W/'MIGRATION_PLAN.md'),('migration_inventory.csv',W/'migration_inventory.csv')]:assert sha(p)==sha(E/'baseline/documentation-before'/name)
components=read(E/'structural/metrics/invariant-components.json')
for x in components['components']:
 if x['name']=='cm_task_short_ready':x.update(target_definition_present=True,transition_status='proved_along_successful_execution_with_verified_support_invariants',iteration_theorem='cm_source_termination_short_ready')
components['note']='Twelve components proved by actual initial/step/iter proofs. Six components and original full preservation remain pending; local saved-generation inclusion is proved, not assumed.'
write(R/'metrics/invariant-components.json',components)
verified=[x['name']for x in components['components']if x['transition_status'].startswith('proved')];remaining=[x['name']for x in components['components']if not x['transition_status'].startswith('proved')];assert len(verified)==12 and len(remaining)==6
obligations=read(E/'structural/metrics/remaining-obligations.json')
for x in obligations['remaining']:
 x['detail']=x['detail'].replace('Eleven','Twelve').replace('eleven-component','twelve-component').replace('tagged-valid, short-ready, code-layout','tagged-valid, code-layout')
write(R/'metrics/remaining-obligations.json',obligations)
eff.update(status='kernel_checked_published_public_support_only',tool_seconds=sum(x['seconds']for x in checks),publication_tool_seconds=sum(x['seconds']for x in pub));write(R/'metrics/effort.json',eff)
write(R/'metrics/development-failures.json',dict(attempts=[x for x in checks if x['exit_code']],note='Failed development commands retained; final two modules pass all forty closed-context audits and independent kernel check. No unfinished goals accepted or published.'))
write(R/'metrics/definition-correspondence.json',dict(original_definitions=['cm_frame_short_ready','cm_frames_short_ready','cm_task_short_ready'],local_definitions=['cm_region_generations_incl','cm_frame_saved_generations','cm_frames_saved_generations','cm_task_saved_generations','cm_short_support_invariants'],note='Original short predicates retain the op=0/false and op=1/true implications and all active task constructors. Local generation inclusion strengthens the proof state, with concrete initial/step/iter proofs; no C precondition added.'))
write(R/'metrics/signature-audit.json',dict(audited_constants=40,closed_constants=40,new_axioms=[],original_preservation_declared=False,original_success_bridge_declared=False,top_level_contract_modified=False,local_variants={'cm_task_short_step_generation':'Generation bounds plus local saved-region inclusion replace the source theorem runtime premise. Both discharged along actual successful source executions.','cm_source_termination_short_invariants':'Original semantic wf and source termination imply twelve support components after arbitrary n annotated steps. No target simulation assumed.'}))
now=eff['totals'];checkpoint=dict(status='incremental_public_support_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),top_level_qcp_verified=False,public_modules=2,public_cost=now,assumption_audits=40,axioms_used_by_new_proofs=[],kernel=k,canonical_publication_all_passed=True,original_components_proved_along_successful_execution=verified,new_components=['cm_task_short_ready'],remaining_components=remaining,top_level_vcs_generated=False,skill_updated=False,remaining_obligations=str(R/'metrics/remaining-obligations.json'))
write(R/'metrics/checkpoint.json',checkpoint)
batches=['semantics','preservation','invariants','structural','transport'];incs=[dict(path=str(E/n/'metrics/effort.json'),totals=read(E/n/'metrics/effort.json')['totals'])for n in batches];total={key:sum(x['totals'].get(key,0)for x in incs)for key in set().union(*(x['totals']for x in incs))}
status=read(E/'metrics/status.json');status.update(status='in_progress_twelve_support_invariants_verified_full_simulation_pending',public_support_checkpoints=[str(E/n/'metrics/checkpoint.json')for n in batches],latest_public_support_checkpoint=checkpoint,additional_public_dependency_cost_so_far=total,new_verified_public_definitions=total['definitions'],new_verified_public_lemmas=total['lemmas'],skill_updated=False,inventory_success_updated=False,current_dependency_gap='Twelve original components proved along successful source execution. Pending layout-ready, runtime, type, tagged-valid, code-layout and full target simulation. Original preservation, success bridge and top QCP remain incomplete.');write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall.update(status=checkpoint['status'],additional_public_dependency_cost_so_far=total,public_support_increments=incs,note='Five verified increments. Top final annotation/proof and complete C* dependency closure remain null. Partial same-name source lines are not a comparable migration-cost denominator.');overall['target_completed_this_attempt'].update(verified_public_definitions=total['definitions'],verified_public_lemmas=total['lemmas'],public_definition_lines=total['definition_lines'],public_proof_lines=total['proof_lines']);write(E/'metrics/effort.json',overall)
source=read(R/'metrics/source-reference-cost.json')['totals']
(R/'README.md').write_text(f'''# cmc_compile：第五批公共证明支持

补齐 short-ready。累计原 18 项中的 12 项，亦即本轮剩余 11 项中的 5 项，具备具体 initial/step/任意步数保持性证明。仍缺 layout-ready、runtime、type、tagged-valid、code-layout、完整 target-sim；原 cmc_preservation、cmc_compile 成功桥和顶层 QCP 未完成，skill 未改。

## 证明内容

保持原 cm_frame_short_ready、cm_frames_short_ready、cm_task_short_ready 含义：只有 CMBinRK 记录短路条件，op=0 要求左值为 false，op=1 要求为 true。其余 frame 不额外约束。

新增本地 saved-region generation inclusion：保存的区域代际包含于当前区域代际。通过实际 R/L/S/V/C 步进、调用、局部激活、作用域和调用恢复证明它的初始及任意步保持性。恢复区域时只修改存活性，不改变已有代际的首次基址；调用和局部分配只增加新代际。因此原先有代际界的左值数值及真值不变。逐一覆盖短路 frame 创建、值/控制返回及 IO/存储分支，再结合此前已证明的 generation-safe。没有将尚未完成的 runtime 或目标模拟定理作为假设，也没有添加 C Require。

3 个原定义逐项映射，5 个本地定义用于强化证明状态及组合；它们的初始/逐步条件全部闭合。已验证的 30 个公共库原样复用，复用新增源码成本为 0。

## 新增公共依赖成本

本批 {now['definitions']} 定义、{now['lemmas']} 引理；定义 {now['definition_lines']} 行，proof {now['proof_lines']} 行（引理 {now['lemma_lines']}，8 个 Ltac 共 {now['automation_lines']} 行）。非空非注释物理行，proof 含陈述及 Proof/Qed，工具与生成审计不计；所有辅助引理均计入。新增运行时 C 和 annotation 为 0。

五批累计 {total['definitions']} 定义、{total['lemmas']} 引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行。对应 C* 同名参照切片定义 {source['definition_lines']} 行、直接 proof 构造器 {source['proof_constructor_lines']} 行、常量装配 {source['proof_constant_scaffolding_lines']} 行；该切片不含传递闭包，不计算与全部 QCP proof 的比值。历史人工耗时未知保持 null。

## 验证

40/40 Print Assumptions 闭合，无新公理；独立 coqchk 退出 0，耗时 {k['seconds']:.2f} 秒；两个正式目录公共库编译通过。518 原源文件、185 旧目标文件、30 前批库及 skill/计划/清单哈希未变。失败尝试、命令耗时和哈希保存在 metrics 和 logs。顶层 VC 尚未生成，原 controller/annotation owner 保留。C* 顶层此前完整重放通过，本批未重复。

重放依赖顺序见 publish.py：check.py development MODULE；source_reference_cost.py；check.py development TransportAudit；完成后 check.py kernel TransportAudit。kernel-input-manifest 固定源及 .vo；publish.py 和 record_checkpoint.py 都有核验门禁。
''')
backup=E/'REPORT-before-transport.md'
if not backup.exists():shutil.copy2(E/'REPORT.md',backup)
(E/'REPORT.md').write_text(f'''# cmc_compile：十二项模拟支持不变量已验证，顶层未完成

本轮补齐原剩余 11 项中的 **5 项**：static-valid、budget、generation-safe、static-bases、short-ready。累计 12/18 项有具体初始、逐步及任意步保持性证明。详见 [第四批](structural/README.md) 和 [第五批](transport/README.md)。

**仍缺 6 项：layout-ready、runtime、type、tagged-valid、code-layout、完整 target-sim。cmc_preservation、原成功桥及顶层 QCP 尚未完成；skill 未更新。** 没有新增 C Require 或假设未证的保持性定理。

| 工作量 | C* 顶层基线 | QCP 顶层最终值 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 未完成统计 | 未完成 |

第五批新增公共成本：8 定义、40 引理，定义 12 行、proof 191 行（含 Ltac 33 行）。第四、五批合计新增 40 定义、141 引理，定义 106 行、proof 839 行。五批累计 {total['definitions']} 定义、{total['lemmas']} 引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行。公共依赖与顶层案例成本分列；完整可比成本和最终比率仍为 null。

第五批 40 条假设审计全部闭合，独立 coqchk 通过（{k['seconds']:.2f} 秒），2 个正式库编译通过。第四批 101 条闭合审计、独立内核及 7 个正式库编译亦已通过。原 C* 顶层重放此前通过（约 1040 秒）。原契约、前批证明、skill、迁移成功清单未改；顶层 VC 尚未生成。
''')
print(json.dumps(dict(increment=now,cumulative=total,verified=12,remaining=6),ensure_ascii=False))
