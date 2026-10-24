"""Record checked public increments, never mark the unfinished C theorem passed."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil
R=Path(__file__).resolve().parent; E=R.parent; W=E.parent.parent
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='InvariantAudit')
a=next(x for x in reversed(checks)if x['mode']=='development' and x['module']=='InvariantAudit')
assert k['exit_code']==a['exit_code']==0 and k['sha256']==a['sha256']==sha(R/'target/InvariantAudit.v')
log=Path(a['log']).read_text();assert log.count('AUDIT ')==log.count('Closed under the global context')==eff['expected_assumption_audits'] and 'Axioms:'not in log
assert len(pub)==len(eff['modules']) and all(x['exit_code']==0 and sha(Path(x['path']))==x['sha256'] for x in pub)
for x in eff['modules']:assert sha(Path(x['file']))==x['sha256']
for x in read(R/'metrics/kernel-input-manifest.json'):assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['vo']))==x['vo_sha256']
for x in read(E/'baseline/source-manifest.json'):assert sha(Path('/Users/nizitong/cmc')/x['path'])==sha(E/'baseline/cstar_project'/x['path'])==x['sha256']
for x in read(E/'baseline/target-manifest.json'):assert sha(Path(x['path']))==x['sha256']
for x in read(R/'baseline/previous-public-manifest.json'):assert sha(Path(x['path']))==x['sha256']
for p,h in read(R/'baseline/frozen-inputs.json').items():assert sha(Path(p))==h
for name,p in [('SKILL.md',Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md')),('MIGRATION_PLAN.md',W/'MIGRATION_PLAN.md'),('migration_inventory.csv',W/'migration_inventory.csv')]:assert sha(p)==sha(E/'baseline/documentation-before'/name)
now=eff['totals']; expected=eff['expected_assumption_audits']; nmodules=len(pub)
components=read(R/'metrics/invariant-components.json')['components'];verified=[x['name']for x in components if x['transition_status'].startswith('proved')]
assert len(verified)==7
failures=[x for x in checks if x['exit_code']]
write(R/'metrics/development-failures.json',dict(attempts=failures,note='Includes unfinished interactive proofs. The first kernel attempt was dispatched before the audit .vo existed and failed closed; the completed audit and subsequent kernel check are the accepted evidence.'))
eff['tool_seconds']=sum(x['seconds']for x in checks)
eff['publication_tool_seconds']=sum(x['seconds']for x in pub)
eff['status']='kernel_checked_published_public_support_only'
write(R/'metrics/effort.json',eff)
checkpoint=dict(status='incremental_public_support_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),top_level_qcp_verified=False,public_modules=nmodules,public_cost=now,assumption_audits=expected,axioms_used_by_new_proofs=[],kernel=k,canonical_publication_all_passed=True,original_components_proved_along_successful_execution=verified,extra_local_refinement='cm_task_active_fid_ready',top_level_vcs_generated=False,skill_updated=False,remaining_obligations=str(R/'metrics/remaining-obligations.json'),note='Original spill/context/fid predicates retained. Local step signatures differ explicitly; their premises are discharged by concrete initial/step/iter proofs. The seven-component theorem concludes support invariants, not target simulation, cmc_preservation or cmc_compile_success_bridge.')
write(R/'metrics/checkpoint.json',checkpoint)
incs=[]
for name in ['semantics','preservation','invariants']:
 path=E/name/'metrics/effort.json';incs.append(dict(path=str(path),totals=read(path)['totals']))
total={key:sum(x['totals'].get(key,0)for x in incs)for key in set().union(*(x['totals']for x in incs))}
status=read(E/'metrics/status.json');status.update(status='in_progress_seven_support_invariants_verified_full_simulation_pending',public_support_checkpoints=[str(E/n/'metrics/checkpoint.json')for n in ['semantics','preservation','invariants']],latest_public_support_checkpoint=checkpoint,additional_public_dependency_cost_so_far=total,new_verified_public_definitions=total['definitions'],new_verified_public_lemmas=total['lemmas'],skill_updated=False,inventory_success_updated=False,current_dependency_gap='Seven of eighteen original invariant components now proved along successful source executions, including spill/context/fid and an active-fid refinement. Eleven components including runtime/type/layout/generation/budget/full target simulation remain pending; cmc_preservation, original cmc_compile_success_bridge and top-level QCP remain incomplete. Historical controller report retained unchanged.')
write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall.update(status=checkpoint['status'],additional_public_dependency_cost_so_far=total,public_support_increments=incs,note='Three verified public increments; all definitions, lemmas and Ltac automation counted once. Final top-level annotation/proof and complete source dependency closure remain null. Partial same-name source lines are not a comparable denominator for a migration ratio.')
overall['target_completed_this_attempt'].update(verified_public_definitions=total['definitions'],verified_public_lemmas=total['lemmas'],public_definition_lines=total['definition_lines'],public_proof_lines=total['proof_lines'])
write(E/'metrics/effort.json',overall)
rows=['| 本批公共模块 | 定义 | 引理 | 定义行 | Proof 行 |','|---|---:|---:|---:|---:|']
for m in eff['modules']:
 c=m['counts'];rows.append(f"| `{Path(m['file']).name}` | {c['definitions']} | {c['lemmas']} | {c['definition_lines']} | {c['proof_lines']} |")
source=read(R/'metrics/source-reference-cost.json')['totals']
(R/'README.md').write_text(f'''# cmc_compile 模拟不变量：第三批公共支持

本批 {nmodules} 个公共库通过 Rocq 编译、独立 coqchk 和 {expected} 条逐项假设审计，并接入 QCP。**这不是顶层完成记录：完整目标模拟、cmc_preservation、原签名 cmc_compile_success_bridge 及顶层 C 验证仍未完成；skill 未更新。**

## 已证明的内容

- 临时槽一致性：保留反序参数暂存、阶段拥有的半开临时槽区间、调用时保存/恢复调用者临时槽等原定义。证明 remove/put 不覆盖其他槽、staged/phase/cursor 保持性及任意成功执行的 annotation spill 一致性。
- 控制上下文：保留语句父阶段、循环/函数作用域屏障和 return 条件。函数体作用域从已有 cm_stmt_wf/cm_typed_program 推出，覆盖表达式、语句、值返回和控制返回，证明 step/iter。
- 函数编号：保留 cm_frame_fid_ready/cm_frames_fid_ready/cm_task_fid_ready 原定义。增加并证明局部 active-fid 分量：R/L/S 阶段处于有效函数，V/C 可回到根编号 -1。进入调用由 cm_call_ok 推出被调函数编号范围；错误路径不可能成功的引理已证明。
- 具体合取 cm_control_support_invariants 包含原 18 项中的 7 项及上述局部分量，有直接 initial/step/iter 证明。cm_source_termination_support_invariants 从原良构条件和实际源终止谓词推出任意 n 步后的这些性质，**不以待证保持性或模拟作为假设，也不声称 TVM 终止**。

此前 17 个公共语义/annotation/坐标/存储/取指模块原样复用，新增源码成本为 0。原 C 契约、源程序和旧目标文件未修改。

## 签名和语义对应

cm_annotation_step_spill_coordinate 使用成功性、擦除和坐标分量；没有冒充源侧只以 layout-ready 为前提的同名引理。cm_task_context_step_coordinate 使用已有类型良构、擦除、坐标分量。cm_task_fid_step_coordinate 使用已证明 active-fid 分量。上述局部前提均在七分量 initial/step/iter 中得到证明，未加入 cmc_compile 的 Require。

源 bool 命题迁移为 Prop，23 个 phase 构造分支采用等价合并分支。context 的公共两分量提到外层，非 S/C 分支的额外 True 合取不改变命题。spill 保存帧的 hd 默认值继续由任意 cm_annotation_policy 表示，且保存帧非空要求保持。详细源文件哈希、同名声明行区间及签名审计分别见 metrics/source-reference-manifest.json、source-reference-cost.json、signature-audit.json。

## 新增公共成本

按非空非注释物理行计；proof 包含引理陈述、Proof/Qed 和 Ltac。定义另列；工具和生成的审计文件不计入数学 proof；未知历史人工耗时保持 null。紧凑分支和自动化会影响行数，不能将行数直接解释为人工难度。

'''+ '\n'.join(rows)+f'''

本批 {now['definitions']} 个定义、{now['lemmas']} 条引理：定义 {now['definition_lines']} 行，proof {now['proof_lines']} 行（引理 {now['lemma_lines']} + {now['automation_declarations']} 个 Ltac 共 {now['automation_lines']} 行）。三批累计 {total['definitions']} 个定义、{total['lemmas']} 条引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行；所有辅助引理均计费，不只统计被最终定理使用的子集。

C* 同名参照切片：定义 {source['definition_lines']} 行、直接 proof 构造器 {source['proof_constructor_lines']} 行、常量装配 {source['proof_constant_scaffolding_lines']} 行。它不含完整传递依赖，也不涵盖本批改用局部前提的组合证明，**不可与全部 QCP proof 相除得出迁移比率**。C* 顶层基线仍是 specification 12 行、annotation 2 行/2 条、案例 proof 499 行；成功桥接公共 proof 42 行另列。QCP 顶层最终成本尚未产生。

## 验证和剩余工作

{expected} 条 Print Assumptions 均 Closed under the global context，独立内核检查退出 0，用时 {k['seconds']:.2f} 秒；正式目录 {nmodules} 个库编译均通过。没有新增 Axiom/Parameter/Admitted/Abort。传递 QCP 环境含历史公理，新证明的闭合审计不代表整个环境无公理。未因公共追加而重复旧的有限回归；本批验证对象是全称 initial/step/iter 定理。所有开发失败和检查时序失败如实保存在 metrics/checks.json 与 development-failures.json。

518 个原源文件、185 个先前目标文件、17 个已验证公共库以及 skill/计划/完成清单哈希不变。C* 完整原始重放此前通过，本批未重跑。

尚缺 11 项：layout-ready、runtime、type、generation、static-valid、static-bases、tagged-valid、budget、short-ready、code-layout、完整 task-target-sim。其后还需完整 cm_preservation_initial/step/iter、cmc_successful_exec_simulation、cmc_preservation、原 cmc_compile_success_bridge，以及原 controller run 的顶层符号执行、手工 VC 和终检。见 metrics/invariant-components.json 与 remaining-obligations.json。skill 更新门槛仍是顶层验证通过。

重放顺序见 publish.py：先按依赖序运行 check.py development，再 source_reference_cost.py、check.py development InvariantAudit，等待结束后运行 check.py kernel InvariantAudit。publish.py 会核对审计和哈希；record_checkpoint.py 仅在全部检查通过后写入本记录。
''')
backup=E/'REPORT-before-invariants.md'
if not backup.exists():shutil.copy2(E/'REPORT.md',backup)
(E/'REPORT.md').write_text(f'''# cmc_compile：七项模拟支持不变量已验证，顶层仍未完成

新增临时槽一致性、控制上下文、函数编号及其 step/iter 证明，复用此前已验证的成功性、擦除、根约束和坐标。七项原不变量及一个已证明局部分量已合并，并可从原良构条件和源终止性推出任意步数后的保持。详见 [第三批验证与成本](invariants/README.md)。

**仍缺十一项完整模拟分量，cmc_preservation、原 cmc_compile_success_bridge 和顶层 QCP 尚未验证；skill 未更新。** 已证明的七项支持性质没有替代目标执行模拟，也未作为新增 Require。完整剩余项见 [义务清单](invariants/metrics/remaining-obligations.json)。

| 工作量 | C* 顶层基线 | QCP 顶层最终值 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥接公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 尚未完成对应统计 | 尚未完成 |

本批新增公共成本单列：{now['definitions']} 个定义、{now['lemmas']} 条引理，定义 {now['definition_lines']} 行、proof {now['proof_lines']} 行（含 {now['automation_lines']} 行 Ltac）。此前 17 个库原样复用；三批累计 {total['definitions']} 个定义、{total['lemmas']} 条引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行。完整依赖闭包和可比总成本未完成，最终比率保持 null。

本批 {expected} 条假设审计均闭合、独立 coqchk 通过（{k['seconds']:.2f} 秒）、{nmodules} 个正式公共库编译通过。原 C* 顶层重放此前通过（约 1040 秒），未重复运行；原源、旧目标、前两批公共库以及 skill/计划/完成清单哈希均保持一致。原 controller run 与 annotation owner 保留；缺失语义闭包未完成之前，不宣称顶层 VC 已生成或完成。
''')
print(json.dumps(dict(increment=now,cumulative=total,kernel_seconds=k['seconds'],verified_components=verified)))
