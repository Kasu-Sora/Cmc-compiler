"""Record only the independently checked incremental public proof work."""
from pathlib import Path
import json,hashlib,shutil
from datetime import datetime,timezone
R=Path(__file__).resolve().parent;E=R.parent;W=E.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,indent=2)+'\n')
eff=read(R/'metrics/effort.json');checks=read(R/'metrics/checks.json');pub=read(R/'metrics/publication.json')
k=next(x for x in reversed(checks)if x['mode']=='kernel' and x['module']=='PreservationAudit');assert k['exit_code']==0 and k['sha256']==sha(R/'target/PreservationAudit.v')
a=next(x for x in reversed(checks)if x['mode']=='development' and x['module']=='PreservationAudit')
log=Path(a['log']).read_text();assert a['exit_code']==0 and a['sha256']==sha(R/'target/PreservationAudit.v')
assert log.count('AUDIT ')==log.count('Closed under the global context')==eff['expected_assumption_audits'] and 'Axioms:'not in log
assert len(pub)==len(eff['modules']) and all(x['exit_code']==0 and sha(Path(x['path']))==x['sha256']for x in pub)
for x in read(R/'metrics/kernel-input-manifest.json'):
 assert sha(Path(x['source']))==x['source_sha256'] and sha(Path(x['vo']))==x['vo_sha256']
for x in read(E/'baseline/source-manifest.json'):assert sha(Path('/Users/nizitong/cmc')/x['path'])==sha(E/'baseline/cstar_project'/x['path'])==x['sha256']
for x in read(E/'baseline/target-manifest.json'):assert sha(Path(x['path']))==x['sha256']
for x in read(R/'baseline/previous-semantics-manifest.json'):assert sha(Path(x['path']))==x['sha256']
for name,dst in [('SKILL.md',Path('/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md')),('MIGRATION_PLAN.md',W/'MIGRATION_PLAN.md'),('migration_inventory.csv',W/'migration_inventory.csv')]:assert sha(dst)==sha(E/'baseline/documentation-before'/name)
reg=next(x for x in checks if x['module']=='PreservationRegression');assert reg['exit_code']==0 and reg['sha256']==sha(R/'target/PreservationRegression.v')
write(R/'metrics/regression-check.json',reg)
remaining=read(R/'metrics/remaining-obligations.json');remaining['remaining'][0]['status']='verified';write(R/'metrics/remaining-obligations.json',remaining)
summary=dict(status='incremental_public_support_verified_top_level_incomplete',recorded_at=datetime.now(timezone.utc).isoformat(),
 top_level_qcp_verified=False,public_modules=len(pub),public_cost=eff['totals'],assumption_audits=eff['expected_assumption_audits'],
 axioms_used_by_new_proofs=[],kernel=k,canonical_publication_all_passed=True,regression_checks=9,
 trusted_automation_results_added=0,top_level_vcs_generated=False,skill_updated=False,
 note='Generic composition lemmas retain explicit invariant initialization/step/simulation premises. They are not cmc_preservation or the original cmc_compile_success_bridge. These premises were not added to the runtime contract.',
 remaining_obligations=str(R/'metrics/remaining-obligations.json'))
write(R/'metrics/checkpoint.json',summary)
prior=read(E/'semantics/metrics/effort.json')['totals'];now=eff['totals'];total={key:prior.get(key,0)+now.get(key,0)for key in set(prior)|set(now)}
status=read(E/'metrics/status.json');status['status']='in_progress_annotation_invariants_verified_full_simulation_pending'
status['public_support_checkpoints']=[str(E/'semantics/metrics/checkpoint.json'),str(R/'metrics/checkpoint.json')]
status['latest_public_support_checkpoint']=summary;status['additional_public_dependency_cost_so_far']=total
status['new_verified_public_definitions']=total['definitions'];status['new_verified_public_lemmas']=total['lemmas']
status['current_dependency_gap']='Annotation update/erasure/rooted/coordinate preservation and memory provenance/store plus code-fetch support verified. Full 18-component invariant initial/step/iteration, cmc_preservation and original cmc_compile_success_bridge still pending. No top-level VC generation. Historical annotation blocker text is retained verbatim.'
status['skill_updated']=False;status['inventory_success_updated']=False
write(E/'metrics/status.json',status)
overall=read(E/'metrics/effort.json');overall['status']=summary['status'];overall['additional_public_dependency_cost_so_far']=total
if 'public_support_increments'not in overall:overall['public_support_increments']=[dict(path=str(E/'semantics/metrics/effort.json'),totals=prior)]
overall['public_support_increments']=[x for x in overall['public_support_increments']if x['path']!=str(R/'metrics/effort.json')]+[dict(path=str(R/'metrics/effort.json'),totals=now)]
t=overall['target_completed_this_attempt'];t.update(verified_public_definitions=total['definitions'],verified_public_lemmas=total['lemmas'],public_definition_lines=total['definition_lines'],public_proof_lines=total['proof_lines'])
overall['note']='Top-level final annotation/proof costs remain null. Public support so far: two verified increments; include all new helpers and Ltac automation, including generic composition lemmas not yet instantiated by a full simulation invariant. No source/target ratio is valid before matching the complete property/dependency closure.'
write(E/'metrics/effort.json',overall)
rows=['| 本批公共模块 | 定义 | 引理 | 定义行 | Proof 行 |','|---|---:|---:|---:|---:|']
for m in eff['modules']:
 c=m['counts'];rows.append(f"| `{Path(m['file']).name}` | {c['definitions']} | {c['lemmas']} | {c['definition_lines']} | {c['proof_lines']} |")
(R/'README.md').write_text('''# cmc_compile 逐步模拟支持：第二批验证记录

本批 8 个公共模块已通过 Rocq 编译、独立 coqchk 和 67 条逐项假设审计，并已接入 QCP 正式库。**完整逐步模拟、cmc_preservation、原签名的 cmc_compile_success_bridge 和顶层 C 验证尚未完成；skill 未更新。**

已完成：

- 按原 C* 有限方程表迁移 cm_update_r/l/s/v/c 的 85 个构造分支，以及 annotation_step、annotated_step/iter。显式保留 HOL 的 HD [] 解释参数，未用固定默认值消除非法分支。逐条映射保存在 metrics/update-equations.json；生成脚本遇到未覆盖语法会失败。
- 证明五类更新的栈擦除和根约束保持、annotation_step 的保持，以及任意步数迭代的源执行对应、擦除、根约束和成功性。这里只闭合了原 18 项不变量中的四个分量（成功性、擦除、根约束、坐标），完整合取尚未迁移。
- 补齐任意整数的八字节编码/解码、word 写后读、写入不相交字节范围不改变 word、存储后旧/新指针来源标记的数值模拟。沿用既有初始化字节模拟，未增加顶层输入条件。
- 迁移代码片段位置谓词及拼接/嵌套/头指令查找，连接实际 TVM 单步执行；验证 push/pop/load/store 四类基础步骤。
- 证明循环/调用坐标不变量的 initial/step/iter，保留临时槽、父游标以及 break/continue 目标之间的原始关系。
- 完成从“已证明不变量”到终止观察的组合引理，以及模型终止到解码对象终止的组合引理。初始化、逐步保持和模拟投影仍是这些通用引理的显式参数；**它们不是已证明的 cmc_preservation，也没有作为 cmc_compile 的 Require 使用。**

新增公共工作量按非空非注释物理行计；Proof 包含引理陈述和 Proof/Qed，以及局部 Ltac 自动化。定义与 proof 分列；生成的检查文件、回归和 Python 工具不计入公共 proof。85 个模型分支由保留的脚本转写，其最终定义仍全计入定义规模，不能将物理行数当成人工耗时。

'''+ '\n'.join(rows)+f'''

本批增量：{now['definitions']} 项定义、{now['lemmas']} 条引理；定义 {now['definition_lines']} 行，proof {now['proof_lines']} 行（引理 {now['lemma_lines']} + 7 个 Ltac 共 {now['automation_lines']} 行）。此前 9 个公共模块原样复用，新增源码成本为 0。两批累计 {total['definitions']} 项定义、{total['lemmas']} 条引理，定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行。最终依赖闭包仍未完成，最终成本和比率保持 null。

C* 顶层既有规模不变：specification 12 行、annotation 2 行/2 条、案例 proof 499 行、成功桥接 proof 42 行另列；完整外部保持性依赖成本尚未完成。metrics/source-reference-cost.json 给出本批可精确定位的同名源定义和直接 proof 构造器行区间，不能把该不完整切片与全部目标 proof 作比率。

验证证据：metrics/checkpoint.json、metrics/checks.json、metrics/publication.json。67 条新证明的 Print Assumptions 均 closed，没有新增 Axiom/Parameter/Admitted/Abort。传递 QCP 环境仍包含历史公理；不能将新证明审计结果扩大为整个环境无公理。独立内核检查用时 {k['seconds']:.2f} 秒，退出 0。9 项回归覆盖带 annotation 的常量、短路、双参数调用/I/O、循环赋值、全局字符、负数/溢出 word 和相邻/重叠写入，均通过；有限回归不替代全称模拟证明。

metrics/invariant-components.json 和 metrics/remaining-obligations.json 列出未完成连接。后续仍需布局/上下文/运行时/类型/函数编号/临时槽/代际/静态地址/标签/预算/短路/代码位置不变量及保持，构造完整 initial/step/iter，之后才能得到原 cmc_preservation 和成功桥接，恢复原 controller run 完成顶层 C 的 VC 与终检。

重放：按 publish.py 依赖序执行 check.py development；audit.py 生成逐项签名和成本审计；check.py development PreservationAudit 与 check.py kernel PreservationAudit 执行独立审计。所有命令、失败尝试、退出码和哈希均保存。C* 原始重放此前已通过，本批未重复运行。
''')
backup=E/'REPORT-before-preservation.md'
if not backup.exists():shutil.copy2(E/'REPORT.md',backup)
(E/'REPORT.md').write_text(f'''# cmc_compile：annotation 保持性已验证，完整模拟仍待补齐

第二批 8 个公共 Rocq 模块已完成编译、独立内核检查和 67 条假设审计，并接入 QCP。新增内容包括 85 个 annotation 更新分支、栈擦除/根约束/坐标的单步与迭代保持、存储后指针来源模拟、word 编解码、代码片段取指及基础 TVM 单步支撑。详见 [本批验证与工作量](preservation/README.md)。

**cmc_preservation 和原签名 cmc_compile_success_bridge 尚未完成，顶层 QCP 未验证，skill 未更新。** 通用组合引理已编译，但其完整不变量前提尚未被具体证明；未将这些前提加入原 C 契约。原 18 项模拟不变量中目前闭合四个分量，详见 [剩余义务](preservation/metrics/remaining-obligations.json)。

| 指标 | C* 顶层基线 | QCP 顶层最终成本 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥接公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 尚未完成匹配统计 | 尚未完成 |

公共增量单列：本批定义 {now['definition_lines']} 行，proof {now['proof_lines']} 行（{now['lemma_lines']} 行引理和 {now['automation_lines']} 行自动化）；50 项定义、67 条引理。两批累计定义 {total['definition_lines']} 行、proof {total['proof_lines']} 行，326 项定义、175 条引理。此前库原样复用，不重复算新增成本。没有依据将这些未完成闭包的规模换算为两种工具的难度或时间比率。

C* 原始顶层重放此前已通过（约 1040 秒，验证义务/新增公理/策略均为空），记录在 metrics/cstar-verification.json。本批核对 518 个源文件、185 个先前目标文件和上一批 9 个公共库，哈希均一致。技能、迁移计划及完成清单保持原样。原 controller run/annotation owner 仍保留，待语义闭包完成后继续其正式流程；没有绕过 controller 或制造顶层完成结果。
''')
print(json.dumps(dict(status=summary['status'],increment=now,cumulative=total,kernel_seconds=k['seconds'])))
