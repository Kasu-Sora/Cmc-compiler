#!/usr/bin/env python3
"""Publish proven emitter-core guidance after final checks and semantic audit."""
from pathlib import Path
import json,csv,io,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id'];date=datetime.datetime.now().astimezone().date().isoformat()
ref=f'''# 已验证案例：emit-core，C* → QCP

{date} 完成 `cmc_concrete_emit_core.c` 全部九个运行时函数，包括 static cm_emit_raw。C* 隔离重放通过，QCP run `{run}` 为 done、final-check passed。报告与逐函数计量：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_core/REPORT.md`。正式目标是 QCP 仓库的 `cmc_emit_core_migration.c` 及对应 Rocq 文件。

## 指令片段与双数组

保持 TVM 的具体 opcode datatype、完整 28 项编码和 TVMInst 的 opcode/immediate 两个字段。cm_rep_ops 与 cm_rep_imms 分别投影到 int32 和 int64 数组。cm_emitter_rep 拥有 emitter 的 output/pc、output 的 ops/imms/code_capacity 和已初始化前缀/未初始化后缀；保留非空指针、等长及容量事实。QCP seg/undef_seg 可表达原先显式指针偏移的区间，但元素宽度和端点必须逐项核对。

cm_emitter_plan_rep 还约束 done 与 todo 的总长度；cm_emit 将一条确切指令从 todo 移入 done。包装函数保留源定义的具体片段。不要把这项契约替换成只增加 pc 或只输出正确长度，也不要用任意整数替代 opcode datatype。验证片段输出并不等于验证 TVM 执行语义或完整编译保持性。

共享 ABI 中原来没有 cm_emitter，本例在 C 中补入与源头文件完全一致的结构体声明。审计应分别比较运行时函数 token、既有 ABI 及新增 ABI 声明，不能把合法的类型声明误报成运行时改写。

## 保留输入域与调用切点事实

normalize/load/store 只要求源契约中的 encoded-type 相等和 cm_type_code_wf；不要为方便证明增加 scalar-type 条件。char 分支发出原字节相关片段，所有其他类型走原非 char 分支。完整 Assert 切点可能清除后续重建模型片段所需的事实；本次首版 symexec 虽通过，生成 VC 审查仍发现 char/nonchar 模型判别事实缺失。补回从原前提可推导的 model_ty =/<> CMCharTy，再完成这些断言的 VC；不能把断言当成无需证明的新假设。

cmc_binary_opcode 的 Require 是 emp，必须覆盖所有 signed int 输入和默认 MOD 分支，保留结果不等于 CALL 编码 22。不能把前提限制为已知枚举值。

临时变量发射器保留完整函数上下文与八项前后置纯条件，复用既有 cm_temp_offset 及 total cm_lookup_policy，不增加 fid 范围。cmc_temp_offset 的 C helper 契约从 layout 原样接入；用已验证 globals 库中的 scalar representation-size 引理建立 slots 聚合及偏移桥。既有模型和引理按零新增记账，新增桥接引理单列。

## 工作量与边界

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 新增公共 proof | —（既有源库） | {Q['new_common_proof']} |

C* 案例 proof 含 12 个私有 proof helpers 的 142 行；不能因它们位于函数外而漏计或算作新增公共库。新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。源依赖中的对应 16 项定义/124 行另行记录。自动生成内容不计手写 proof；QCP 包装与证明体在 effort.json 分开。

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split；另有 {N['automatic_witnesses']} 条自动结果以 Admitted 导出，依赖 QCP 自动层。最终手工证明和新增库无 Admitted/Axiom/Parameter。两次连接中断与恢复独立记录，不算形式证明失败；墙钟包括等待，不能解释为活跃工时或工具速度。新增公共引理以最终合并库计数，不只看最初设计或候选池。
'''
(S/'references/cmc-emit-core-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-core-case.md' not in s
s=s.replace('及 emit-data 的组合函数；','及 emit-data 的组合函数、emit-core 的九个指令生成函数；')
s=s.replace('emit-data 为 `cmc_emit_data_migration.c`。','emit-data 为 `cmc_emit_data_migration.c`，emit-core 为 `cmc_emit_core_migration.c`。')
entry=f'`cmc_concrete_emit_core.c` 于 {date} 完成全部九个运行时函数验证。涉及 TVM 指令片段、双数组 emitter 表示、分支事实保留、任意 int 默认映射和临时槽偏移桥时，读取 [references/cmc-emit-core-case.md](references/cmc-emit-core-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十二个具体实现文件的运行时部分、68 个运行时函数及必要依赖；';assert old in s;s=s.replace(old,entry+'这些结果覆盖十三个具体实现文件的运行时部分、77 个运行时函数及必要依赖；')
s=s.replace('完整 emitter 语义及桥接仍待迁移。','emit-core 的基础指令片段与双数组表示已迁移；完整 emitter 语义及 readiness 桥仍待迁移。');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text();s=s.replace('清点更新：2026-10-16。',f'清点更新：{date}。')
s=s.replace('及 emit-data 组合函数，共十二个具体实现文件的运行时部分、68 个运行时函数','及 emit-data 组合函数、emit-core 的九个指令生成函数，共十三个具体实现文件的运行时部分、77 个运行时函数')
s=s.replace('332、184、6、11、9、12、7 条可信自动',f'332、184、6、11、9、12、7、{N["automatic_witnesses"]} 条可信自动')
s=s.replace('[emit-data 报告](experiments/cmc_emit_data/REPORT.md)。','[emit-data 报告](experiments/cmc_emit_data/REPORT.md)、[emit-core 报告](experiments/cmc_emit_core/REPORT.md)。')
s=s.replace('| 5：指令与程序生成 | `cmc_concrete_emit_core.c`、',f'| 已完成 | `cmc_concrete_emit_core.c` | 九个指令生成函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
s=s.replace('emit-globals、emit-strings 与 emit-data 的运行时部分已完成。下一阶段转向指令生成，先审查 `cmc_concrete_emit_core.c` 的依赖闭包。','emit-globals、emit-strings、emit-data 与 emit-core 的运行时部分已完成。下一候选为 `cmc_concrete_emit_resolved.c`；开始前仍须审查其完整依赖闭包。')
p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_core.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_9_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions';buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
print('Updated verified core reference, migration skill, plan and inventory.')
