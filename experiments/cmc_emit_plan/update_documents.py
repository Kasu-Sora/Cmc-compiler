#!/usr/bin/env python3
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
text=f'''# 已验证案例：emit-plan，C* → QCP

2026-10-17 完成 cmc_concrete_emit_plan.c 全部八个包装函数。C* 原证明隔离重放通过；QCP run `{run}` 为 done、final-check passed。审计和完整计量见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_plan/REPORT.md`。正式目标为 QCP 仓库的 cmc_emit_plan_migration.c 及对应 Rocq 文件。

## 计划谓词与契约

cm_resolved_emitter_plan_rep 是 `Zlength(done)+Zlength(todo)<=capacity` 与既有 resolved emitter 表示的组合。todo 是逻辑容量预算，不额外拥有内存，不要求是完整程序代码或可达后缀。沿用既有 raw-buffer / resolved 逻辑视图与同一个 total cm_lookup_policy。

八个包装函数消费 todo 前面的精确 fragment，将它追加至 done，tail 保持不变。CALL 的逻辑 fragment 含 cm_function_pc，实际仍交由 resolved helper 写原函数编号；不得把计划变成直接写入 PC。原 CALL 契约接受全部 signed int function_id，不附加编号范围、程序 wf、readiness 或 PC 可表示性。其他原输入条件与临时函数前后置八项纯事实和完整上下文保持不变。

## 复用与证明结构

八个 resolved helper 契约与前例规范化后相同；只证明新包装函数体，公共库直接导入 resolved 及其既有依赖，不能为闭合本例而导入旧 manual/auto。容量证明依赖列表长度非负和拼接加法：从 done+(fragment++tail) 的长度界导出本次 fragment 容量界，同时保留调用后 (done++fragment)+tail 的容量界，以恢复完整计划谓词。调用结果只给 resolved 表示时，不能丢掉剩余 tail 的预算事实。

本例的 aggressive_pre_process 先产生空间子目标，再产生两个容量纯子目标，与 split 声明顺序不同；按实际子目标选择 Goal_apply。部分空间 split 已由 LLM_pre_process 闭合，继续添加 unfold/cancel 会报无目标。这里记录的是已发生的行为，其他目标仍应检查实际剩余子目标。

本例源文件的两个私有容量 helper 计案例 proof；cmc_concrete_defs.c 中公开 cm_plan_open、cm_plan_close 及私有 cm_plan_fragment_term 计额外公共 proof。它们是操作符号状态的 PROOF 例程，不应报告成两个独立 HOL 定理。

## 已验证规模

{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 已完成。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层；手工证明和新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源额外公共 proof／目标新增公共 proof | 52 | {Q['new_common_proof']} |

QCP 新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行、引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行；对应源新增模型范围为 1 项/6 行。现成库零新增，实际编译依赖和哈希已核对。历史源工时未知，排版不同，行数不能代表工具效率；本例不包含物理 CALL 回填、完整 TVM 或编译保持性证明。
'''
(S/'references/cmc-emit-plan-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-plan-case.md' not in s
s=s.replace('emit-resolved 的八个包装函数；','emit-resolved 与 emit-plan 各八个包装函数；')
s=s.replace('emit-resolved 为 `cmc_emit_resolved_migration.c`。','emit-resolved 为 `cmc_emit_resolved_migration.c`，emit-plan 为 `cmc_emit_plan_migration.c`。')
entry=f'`cmc_concrete_emit_plan.c` 于 2026-10-17 完成八个计划包装函数验证。涉及 resolved 计划容量、任意 tail、片段消费/追加及模块调用后预算恢复时，读取 [references/cmc-emit-plan-case.md](references/cmc-emit-plan-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十四个具体实现文件的运行时部分、85 个运行时函数及必要依赖；';assert old in s
s=s.replace(old,entry+'这些结果覆盖十五个具体实现文件的运行时部分、93 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text()
s=s.replace('emit-core 的九个指令生成函数及 emit-resolved 的八个包装函数，共十四个具体实现文件的运行时部分、85 个运行时函数','emit-core 的九个指令生成函数及 emit-resolved、emit-plan 各八个包装函数，共十五个具体实现文件的运行时部分、93 个运行时函数')
s=s.replace('9、12、7、83、16 条可信自动',f'9、12、7、83、16、{N["automatic_witnesses"]} 条可信自动')
s=s.replace('[emit-resolved 报告](experiments/cmc_emit_resolved/REPORT.md)。','[emit-resolved 报告](experiments/cmc_emit_resolved/REPORT.md)、[emit-plan 报告](experiments/cmc_emit_plan/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_emit_plan.c`、';assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_plan.c` | 八个计划包装函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
s=s.replace('emit-core 与 emit-resolved 的运行时部分已完成。下一候选为 `cmc_concrete_emit_plan.c`','emit-core、emit-resolved 与 emit-plan 的运行时部分已完成。下一候选为 `cmc_concrete_emit_ast.c`');p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_plan.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_8_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions'
  b=io.StringIO(newline='');csv.writer(b,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=b.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines));print('Updated verified plan reference, skill, plan and inventory.')
