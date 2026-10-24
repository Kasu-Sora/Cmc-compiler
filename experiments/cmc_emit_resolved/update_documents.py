#!/usr/bin/env python3
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
text=f'''# 已验证案例：emit-resolved，C* → QCP

2026-10-17 完成 `cmc_concrete_emit_resolved.c` 全部八个包装函数。C* 原证明隔离重放通过；QCP run `{run}` 为 done、final-check passed。完整审计与计量：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_resolved/REPORT.md`。正式目标为 QCP 仓库的 `cmc_emit_resolved_migration.c` 和对应 Rocq 文件。

## 原始缓冲区与 resolved 视图

`cm_resolved_emitter_rep` 存在一个 raw 指令前缀，拥有 raw 对应的 ops/imms 缓冲区，同时断言 cm_patch_code(raw)=resolved_prefix。CALL 在物理缓冲区中仍保存函数编号；cm_patch_inst 只在逻辑上将其映射为既有 cm_function_pc，其他指令保持原样。不要把 resolved 契约误译成物理缓冲区已经回填 PC，也不要修改运行时代码来满足这种误译。后续物理 patch pass 仍须单独验证。

cm_emit_resolved_call 接受任意 signed int function_id，包括负数及越界编号；原规范没有编号合法、程序 wf、readiness 或 PC 可表示性条件。统一使用既有 total cm_lookup_policy 和 cm_function_pc，不因名称叫 CALL 就增加输入限制。

其他包装函数精确追加原 core 片段。normalize/load/store 只保留原编码相等和 type-code-wf；临时变量包装保留前后置八项纯事实、入口容量界和完整函数上下文，不加 fid 范围。七个 helper 的契约直接从已验证 core 接入；不重复证明底层实现，也不导入其旧 auto/manual。

## 复用与证明结构

先用 patch-code 长度保持把 resolved 容量界转成 raw 计划的容量界，调用 core，再以 patch-code append 和片段 patch 等式恢复 resolved existential。普通指令需要非 CALL 前提，CALL 单独映射到 PC；类型相关和临时变量片段不含 CALL，可保持不变。这些是实际证明的等式，不是额外假设。

新 patch 库导出可复用模型和引理；emit-core 的 instruction datatype、编码表、数组表示与各片段完全复用。源文件的六类片段 patch 私有证明在目标成为公共引理，比较时同时给出案例 proof 和公共 proof，避免因搬到库中而低估成本。源函数外 18 个私有 PROOF 支持声明计入案例 proof；源依赖的两个公共 patch 定理及构造器另列。

## 已验证规模

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split；另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。手工证明与新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源额外公共 proof／目标新增公共 proof | 28 | {Q['new_common_proof']} |

新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。对应源额外模型 3 项/21 行。已有库记零新增，自动生成内容排除；最终公共成本及使用情况以合并库计量。历史工时未知，行数不是工具效率比较；本例不代表完整 TVM 或编译保持性迁移完成。
'''
(S/'references/cmc-emit-resolved-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-resolved-case.md' not in s
s=s.replace('emit-core 的九个指令生成函数；','emit-core 的九个指令生成函数、emit-resolved 的八个包装函数；')
s=s.replace('emit-core 为 `cmc_emit_core_migration.c`。','emit-core 为 `cmc_emit_core_migration.c`，emit-resolved 为 `cmc_emit_resolved_migration.c`。')
entry=f'`cmc_concrete_emit_resolved.c` 于 2026-10-17 完成八个包装函数验证。涉及 raw 缓冲区与 resolved 逻辑视图、CALL 编号的总映射、patch 长度/拼接和 core 契约复用时，读取 [references/cmc-emit-resolved-case.md](references/cmc-emit-resolved-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十三个具体实现文件的运行时部分、77 个运行时函数及必要依赖；';assert old in s;s=s.replace(old,entry+'这些结果覆盖十四个具体实现文件的运行时部分、85 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text();s=s.replace('emit-core 的九个指令生成函数，共十三个具体实现文件的运行时部分、77 个运行时函数','emit-core 的九个指令生成函数及 emit-resolved 的八个包装函数，共十四个具体实现文件的运行时部分、85 个运行时函数');s=s.replace('9、12、7、83 条可信自动',f'9、12、7、83、{N["automatic_witnesses"]} 条可信自动');s=s.replace('[emit-core 报告](experiments/cmc_emit_core/REPORT.md)。','[emit-core 报告](experiments/cmc_emit_core/REPORT.md)、[emit-resolved 报告](experiments/cmc_emit_resolved/REPORT.md)。')
s=s.replace('| 5：指令与程序生成 | `cmc_concrete_emit_resolved.c`、',f'| 已完成 | `cmc_concrete_emit_resolved.c` | 八个 resolved 包装函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
s=s.replace('emit-data 与 emit-core 的运行时部分已完成。下一候选为 `cmc_concrete_emit_resolved.c`','emit-data、emit-core 与 emit-resolved 的运行时部分已完成。下一候选为 `cmc_concrete_emit_plan.c`');p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_resolved.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_8_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions';b=io.StringIO(newline='');csv.writer(b,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=b.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines));print('Updated verified resolved reference, skill, plan and inventory.')
