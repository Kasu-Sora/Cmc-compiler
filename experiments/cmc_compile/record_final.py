"""Publish completion documentation only for an accepted and reviewed final case."""
from pathlib import Path
import json, csv, shutil, hashlib
R=Path(__file__).resolve().parent; W=R.parent.parent
skill=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
read=lambda p:json.loads(p.read_text())
write=lambda p,x:p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=read(R/'metrics/final-effort.json')
assert f['controller_final_check']['status']=='passed'
assert read(R/'metrics/final-contract-audit.json')['status']=='review_passed'
assert (f['manual_top_level'],f['manual_splits'],f['automatic_trusted_witnesses'])==(9,3,17)
hist=R/'history/pre-final';hist.mkdir(parents=True,exist_ok=True)
for p in [R/'REPORT.md',R/'metrics/status.json',R/'metrics/effort.json',W/'MIGRATION_PLAN.md',W/'MIGRATED_FUNCTIONS.md',W/'migration_inventory.csv',skill/'SKILL.md']:
 dest=hist/p.name
 if not dest.exists():shutil.copy2(p,dest)
old=read(hist/'effort.json');math=f['mathematical_public_cost'];t=f['target']
case=dict(definitions=11,definition_lines=t['case_public_definitions'],lemmas=5,proof_lines=t['case_public_proof'])
combined=dict(definitions=math['definitions']+11,definition_lines=math['definition_lines']+case['definition_lines'],
              lemmas=math['lemmas']+5,proof_lines=math['proof_lines']+case['proof_lines'])
effort=dict(status='verified_complete',source=f['source'],target_final=t,
 mathematical_public_dependency_cost=math,case_public_dependency_cost=case,
 additional_public_dependency_cost_final=combined,
 additional_public_dependency_cost_so_far=math,
 public_support_increments=old['public_support_increments'],
 source_dependency_slice='source-dependency-slice.json',source_exact_minimal_dependency_cost=None,
 comparison_ratio=None,historical_source_development_time=None,human_active_time=None,
 final_measurement='final-effort.json',note='Physical artifact sizes, not elapsed human effort. Math and case-specific public support are disjoint. Conservative source lexical slice is not a minimal closure or a valid full-cost ratio denominator.',
 process=dict(mathematics='mathematical-process.json',implementation_groups='group-effort.json',
 controller_recovery='../controller_recovery/recovery.json',stopped_provers='stopped-prover-checks.json',
 annotation_symexec_repairs=4,vc_check_report_format_repairs=2))
write(R/'metrics/effort.json',effort)
(R/'REPORT.md').write_text("""# cmc_compile：C* → QCP 迁移完成

2026-10-21 完成。原 18 项模拟不变量已在成功执行的全部可达注解状态上建立；`cmc_preservation`、原 `cmc_compile_success_bridge` 及实际 C 函数 `cmc_compile` 均已验证。QCP run `cmc_compile_migration-20261019230022` 最终状态为 `done`，final-check 于 UTC 2026-10-20 17:07:11 通过。

## 验证结果与契约

- 原 C* `cmc.c` 完整重放通过，耗时 1040.281 秒；不是只通过编译或复用旧验收结论。
- 22 批、198 个新增数学公共模块均完成编译、逐条假设审计及独立内核检查；最终批 38 条定理假设闭合，独立 coqchk 用时 313.308 秒。198 个模块全部进入顶层依赖闭包。
- 顶层 9 条手工 VC（6 entail、3 return）和 3 条空间拆分目标完成。4 个证明组、父级合并检查及 main-root 最终检查全部通过；重新符号执行确认生成目标新鲜且一致。
- 5 个调用契约与此前已验证实现逐字一致。运行时代码 token、结构体 ABI、518 个源文件和 185 个先前目标文件的冻结哈希保持不变。
- 保留成功／容量不足两分支、原所需长度、entry=0／-1、程序堆所有权、零容量缓冲区及精确输出前缀与未写尾部。成功分支实际应用原成功桥，量化真实源终止和对象解码，得出相同输入、输出、退出状态的 TVM 终止。

目标实现与证明：[标注 C](target/cmc_compile_migration.c)、[手工证明](target/cmc_compile_migration_proof_manual.v)、[案例公共定义／引理](target/cmc_compile_migration_lib.v)。语义审计：[最终契约审计](metrics/final-contract-audit.json)、[保持性定理对照](metrics/preservation-contract-audit.json)。

## Annotation 与 proof 工作量

口径为去空行、去注释的物理行；proof 含定理陈述及 Proof/Qed。自动生成的 VC 展开文本不计手写 proof。QCP 计数排除纯结束注释分隔符；源属性按既有 C* 语法区域计量。长行排版会影响数字，不能用行数直接推断人工效率。

| 类别 | C* | QCP |
|---|---:|---:|
| 顶层 specification | 12 | 4 |
| 函数内 annotation | 2 | 147 |
| specification + annotation | 14 | 151 |
| 案例私有 proof | 499 | 161 |
| 复制已验证 helper 契约的接入标注 | 独立于本函数计量 | 36 |
| Extern／Import 接入声明 | 独立于本函数计量 | 60 + 1 |

C* 私有 proof 为 435 行 inline + 64 行私有支持；`cmc_compile_success_bridge` 的 42 行公开证明另列，getter 3 行、范围外工具支持 29 行不混入私有 proof。QCP 的 147 行包括 6 个 Assert 和 5 个 where；接入 helper 契约后 specification/annotation 共 187 行。C* 的 inline proof 与 QCP 的中间 Assert 将部分工作放在不同类别，因此不以 499/161 单项作效率结论。详见可重放的 [最终区域计量](metrics/final-effort.json)。

## 新增公共依赖成本

本表只计此前 30 个实现单元及六项 readiness 支持之外的新增内容。

| 独立类别 | 定义数／行数 | 定理数 | proof 行数 |
|---|---:|---:|---:|
| 源／TVM 语义及保持性公共支持，22 批 198 模块 | 494 / 1998 | 1061 | 8165 |
| 顶层案例堆包装及公共引理 | 11 / 76 | 5 | 112 |
| 新增合计 | 505 / 2074 | 1066 | 8277 |

数学支持 proof 的 8165 行细分为定理 7950、自动化 213、构造性判定证明 2；自动化含 75 项声明。案例 5 条引理为 2 条代码长度桥和 3 条数组前缀桥；没有新增自动化声明。已有库复用的新增成本为零。逐批明细见 [effort.json](metrics/effort.json)，实际导入见 [模块使用清单](metrics/public-module-import-usage.json)。

源侧另提供 [保守词法依赖切片](metrics/source-dependency-slice.json)：扣除先前案例闭包及顶层文件后，451 项定义／8710 行、2823 个 proof 声明／91199 行。它包含词法引用可能带入的未使用内容，不是精确最小证明闭包，也不是历史人工成本；完整源／目标公共成本效率比保留为 null。

## 开发与检查过程

保留了原 annotation 前置依赖缺口、控制器恢复补丁及检查证据，没有伪造 VC、手改 controller 状态或放宽契约。补齐依赖后沿同一 owner 恢复。

数学阶段记录 679 次检查调用，其中 404 次开发失败；累计调用用时 8907.848 秒，另有 198 次发布检查、429.183 秒。这些是调用耗时加总，包含重复检查，不等于人工工作时长或并行墙钟总时间。

实现阶段记录 4 次 symexec 修复、2 次 VC 检查报告格式修复；证明 owner 共 26 次 development（21 次失败）、6 次 debug（1 次失败）、3 次主动 exact（全部通过），另有控制器对全部 4 组的验收。无界 `rewrite !eval_addr` 引起的两个耗时子进程经定位后停止，记录为失败检查，使用精确地址实例化后通过。原始日志、owner 报告与最终状态保存在 [controller 快照](logs/qcp-controller/controller_state.json)。

过程证据：[数学检查](metrics/mathematical-process.json)、[证明组](metrics/group-effort.json)、[停止检查记录](metrics/stopped-prover-checks.json)、[工具恢复](controller_recovery/README.md)。历史人工时间未知，未估造。

## 信任边界与覆盖范围

手工证明及新增案例公共库没有新增 Axiom、Parameter 或 Admitted；新增数学证明的实际假设审计闭合。QCP 既有分离逻辑基础仍属于框架信任边界。自动求解有 **12 个原始 VC（7 safety、5 partial-solve）**，导出时加上 **5 个 pure 子义务**，合计 **17 条 Admitted 常量**；它们明确作为可信自动结果，不能称为独立 Rocq 内核证明。

保持性归纳使用更强的内部支持不变量，再投影原 18 项。最终公开保持性与成功桥保留原前提和结论；未额外交付“任意满足弱 18 项的状态”的同名 step/iter 定理。此次完成顶层所需语义链和 C 契约，不宣称全部 254 个源文件及每个辅助导出逐名迁移，也不包含发散保持、双向等价、全部示例推论或独立 TVM C 解释器实现验证。

最终验收后更新 [迁移 skill]( /Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md )、[迁移清单](../../migration_inventory.csv)、[函数表](../../MIGRATED_FUNCTIONS.md)。此前阶段性报告保存在 [历史快照](history/pre-final/REPORT.md)，其中 pending 状态仅表示当时进度。
""".replace('( /Users','(/Users').replace('SKILL.md )','SKILL.md)'))

# Update only verified scope; file-wide coverage of mathematical source exports is not inferred.
inventory=W/'migration_inventory.csv'
with inventory.open(newline='') as h:
 reader=csv.DictReader(h);fields=reader.fieldnames;rows=list(reader)
for row in rows:
 if row['source_c']=='/Users/nizitong/cmc/cmc.c':
  row['migration_status']='verified_cmc_compile_1_function_9_manual_3_split_12_auto_vcs_17_trusted_constants_preservation_bridge_complete'
with inventory.open('w',newline='') as h:
 writer=csv.DictWriter(h,fieldnames=fields);writer.writeheader();writer.writerows(rows)

p=W/'MIGRATION_PLAN.md';s=p.read_text()
s=s.replace('30 个已完成实现单元、131 个运行时函数','31 个已完成实现单元、132 个运行时函数')
s=s.replace('清点更新：2026-10-19。','清点更新：2026-10-21。')
# Keep the old case-by-case details as explicitly historical evidence.
s=s.replace('当前完成 `cmc_write_byte`','此前已完成 `cmc_write_byte`',1)
s=s.replace('运行时仍为 30 个实现单元、131 个函数。','当时运行时为 30 个实现单元、131 个函数。')
anchor='[migration_inventory.csv](migration_inventory.csv) 逐项列出'
s=s.replace(anchor,'顶层 `cmc_compile` 于 2026-10-21 完成：18 项模拟不变量、`cmc_preservation`、原成功桥及实际 C 最终验证通过。累计 **31 个实现单元、132 个运行时函数**。9 条手工 VC、3 个 split；12 个自动 VC 导出 17 条可信 Admitted 常量。新增数学公共支持和案例公共支持分账，见 [顶层报告](experiments/cmc_compile/REPORT.md)。\n\n'+anchor)
s=s.replace('| 6：编译保持性 |','| 顶层所需保持性已完成 |').replace('在 Rocq 重建模拟不变式、执行保持、调用/返回、类型与栈条件，得到同样前提下的终止观察保持与无目标错误结论','原 18 项在成功执行可达状态上成立；cmc_preservation 与成功桥已验证，采用更强内部不变量；不代表每个源 helper 逐名迁移')
s=s.replace('| 7：顶层组合 |','| 已完成顶层组合 |').replace('QCP 验证 `cmc_compile`；把模型保持性与具体输出解码连接起来，恢复成功/容量不足的完整契约','cmc_compile 完整成功／容量不足契约通过 QCP final-check；保持性连接到具体缓冲区解码，见顶层报告')
s=s.replace('完整 emitter 语义及 readiness 桥仍待迁移','所需 emitter/readiness 桥已由后续案例及顶层支持补齐')
s=s.replace('emitter 桥接待迁移，四项 TVM 条件保留参数化边界','所需桥接已补齐，顶层以四项真实 TVM 条件实例化参数')
start=s.index('## 推荐下一单元')
s=s[:start]+"""## 当前验收范围

顶层所需剩余工作已经完成，完整记录见 [cmc_compile 报告](experiments/cmc_compile/REPORT.md)。已有 helper 的模块化验证与顶层最终验收共同构成实现链；只检查顶层不能替代 helper 实现验证。

CSV 仍按源文件清点，未逐名核对的数学文件保留原文件级状态；这不再表示顶层保持性存在依赖缺口。目标数学库按定理依赖重组，不强求一个源文件对应一个目标文件。源文件级全部导出、示例推论及独立 TVM C 解释器属于另行限定的范围。
"""
p.write_text(s)

p=W/'MIGRATED_FUNCTIONS.md';s=p.read_text()
s=s.replace('整理日期：2026-10-20','整理日期：2026-10-21').replace('30 个已完成迁移的实现单元、131 个运行时函数','31 个已完成迁移的实现单元、132 个运行时函数')
s=s.replace('完成状态沿用已有验证报告；本次只清点和解释，没有重跑证明。','先前 131 个函数沿用已有验证报告；本次新增顶层 cmc_compile 的完整验证。')
s=s.replace('顶层 `cmc_compile` 尚未完成，见文末范围说明。','顶层 `cmc_compile` 已完成，见第 13 组及文末范围说明。')
s=s.replace('| [12. CALL 物理回填](#group-12) | 2 | 将 CALL 函数编号替换为实际 PC |','| [12. CALL 物理回填](#group-12) | 2 | 将 CALL 函数编号替换为实际 PC |\n| [13. 顶层编译](#group-13) | 1 | 容量检查、代码／数据生成及原语义保持性连接 |')
s=s[:s.index('## 未计入上述 131 个函数的内容')]+"""<a id="group-13"></a>

## 13. 顶层编译

[迁移与验证报告](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile/REPORT.md)

| 函数（点击查看 spec） | 需要实现的功能 | 关键约束／结果 |
|---|---|---|
| [cmc_compile](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile/target/cmc_compile_migration.c:128) | 计算所需容量，生成代码、回填 CALL 并生成数据。 | 容量不足返回 1、保留所需长度及 entry=-1；成功返回 0、entry=0，精确输出模型字节／指令，并保持源终止的输入、输出和退出状态。 |

## 与上述 132 个运行时函数分开统计的内容

| 项目 | 当前范围／状态 |
|---|---|
| readiness 纯证明支持 | data_ready、program_ready、code_ready、temp_ready、function_ready、compile_ready 六个源支持单元已迁移，不增加运行时函数数。 |
| 顶层数学公共支持 | 22 批 198 模块，494 项定义、1061 条定理；另有案例库 11 项定义、5 条引理。 |
| 编译语义保持性 | 原 18 项不变量在成功执行可达状态上成立；cmc_preservation 与原成功桥已验证，实际顶层成功返回证明调用此桥。 |
| 范围边界 | 不宣称全部源 helper/export 逐名迁移、发散保持、双向等价或独立 TVM C 解释器实现验证。 |

依据：[迁移总览](/Users/nizitong/Documents/ChatGPT/Cmc/MIGRATION_PLAN.md)、[顶层最终报告](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile/REPORT.md)。
"""
# Link to the actual function line rather than an assumed line.
c=(R/'target/cmc_compile_migration.c').read_text()
line=c[:c.index('int cmc_compile(')].count('\n')+1
s=s.replace('cmc_compile_migration.c:128)',f'cmc_compile_migration.c:{line})')
p.write_text(s)

draft=(R/'skill-reference-draft.md').read_text()
draft=draft.replace('（待最终验收后发布）','').replace('此文件是实验目录草稿，尚未写入 skill。验收事实和数字应从最终 `metrics/final-effort.json` 填入。',
 '2026-10-21 已完成原 C* 重放与顶层 QCP controller 全流程（done）。完成 9 条手工 VC、3 个 split；12 个自动 VC 导出 17 条可信 Admitted 常量（含 5 个 pure 子义务）。')
draft+='''\n## 验收材料与实测成本

报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile/REPORT.md`；机器数据为同目录 `metrics/final-effort.json` 与 `metrics/final-contract-audit.json`。

C*／QCP 顶层 specification 为 12／4 行、annotation 为 2／147 行、私有 proof 为 499／161 行。QCP 另有 36 行 helper 契约接入。新增公共数学支持为 494 定义／1998 行、1061 定理／8165 proof 行；案例公共支持另计 11 定义／76 行和 5 引理／112 行。未把源侧保守依赖切片当作精确比较分母，人工时长保持未知。
'''
(skill/'references/cmc-compile-case.md').write_text(draft)
p=skill/'SKILL.md';s=p.read_text()
s=s.replace('完整 emitter 语义及 readiness 桥仍待迁移。','所需 emitter 语义及 readiness 桥已由后续案例与 cmc_compile 公共支持补齐。')
ending='这些结果覆盖三十个具体实现迁移单元的运行时部分、131 个运行时函数及必要依赖；不能外推为整个 CMC/TVM 证明已完成迁移。新的函数、其他数据结构和不同方向仍需各自验证。'
assert ending in s
s=s.replace(ending,'''`cmc_compile` 于 2026-10-21 完成原 C* 重放及实际顶层 QCP final-check，controller 为 done。18 项原模拟不变量、cmc_preservation 与原成功桥已具备；9 条手工 VC 和 3 个 split 完成，12 个自动 VC 导出 17 条可信 Admitted 常量。涉及操作语义／保持性与具体输出缓冲区连接、零容量资源、HOL 总查询、强内部不变量或大规模公共依赖计量时，读取 [references/cmc-compile-case.md](references/cmc-compile-case.md)。公共数学成本与案例空间包装／引理成本分别记录。

这些结果覆盖三十一个具体实现迁移单元、132 个运行时函数及顶层所需语义保持性支持。原 18 项按可达执行证明，未声称每个任意状态 helper 或全部源文件导出逐名迁移；也不包含发散保持、双向等价或独立 TVM C 解释器验证。新的函数、其他数据结构和不同方向仍需各自验证。''')
p.write_text(s)
status=dict(status='verified_complete',direction='C* -> QCP',unit='cmc_compile',
 controller_run='cmc_compile_migration-20261019230022',controller_phase='done',
 final_check=f['controller_final_check'],source_cstar_verified=True,
 top_level_qcp_verified=True,original_invariant_components_completed=18,
 remaining_invariant_components=[],preservation_verified=True,success_bridge_verified=True,
 target_vcs=dict(manual_top_level=9,manual_splits=3,completed_manual=9,completed_splits=3,
                 automatic_top_level=12,automatic_pure_subobligations=5,automatic_admitted_constants=17),
 target_completed_annotation_lines=t['annotation'],target_completed_proof_lines=t['case_proof'],
 additional_public_dependency_cost_final=combined,mathematical_public_dependency_cost=math,
 case_public_dependency_cost=case,original_sources_unchanged=True,prior_targets_unchanged=True,
 semantic_audit='final-contract-audit.json',measurement='final-effort.json',skill_updated=True,
 skill_validation_pending=True,inventory_success_updated=True,current_dependency_gap=None,
 current_remaining_work=None,prior_status='../history/pre-final/status.json',
 scope_note='Top-level C contract and required semantic chain complete; not every source export name, divergence theorem or independent interpreter.',
 documentation_hashes={str(p):sha(p) for p in [skill/'SKILL.md',skill/'references/cmc-compile-case.md',W/'MIGRATION_PLAN.md',W/'MIGRATED_FUNCTIONS.md',W/'migration_inventory.csv']})
write(R/'metrics/status.json',status)
print(json.dumps(dict(status='verified_complete',counts=t,additional_public=combined,skill_updated=True),ensure_ascii=False))
