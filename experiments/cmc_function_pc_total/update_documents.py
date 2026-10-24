#!/usr/bin/env python3
"""Publish the audited migration experience only after verified completion."""
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
ref=f'''# 已验证案例：function-pc-total，C* → QCP

2026-10-16，`cmc_concrete_function_pc_total.c` 的两个运行时函数完成迁移，run `{run}` 为 done，final-check passed，原 C* 重放通过。报告及可追溯计量位于 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_pc_total/REPORT.md`。正式文件为 QCP 仓库下 `QCP_examples/QCP_demos_human/cmc_function_pc_total_migration.c` 及 Rocq 对应 lib/manual。

## 不限制 total 输入域

`target` 是任意 signed long long。原契约没有合法函数编号约束；负数和超过链表长度的目标都递归到末尾。不要套用只支持 `0 <= remaining <= length` 的旧 prefix 引理而加强 Require。原导出界定理 `cm_function_prefix_total_bounds` 对任意 remaining 成立，应保留这个量化范围。逻辑表达式 target-index 是 Z 运算，不能额外加入运行时 signed64 减法安全条件。

## Readiness 的等价表示

复用 counts/layout/copy-bytes 库，新增完整单函数、函数列表、结构和程序 code-ready 定义；保留全部合取项。源 readiness 的 emit_stmt 长度依据 C* 无条件定理 `cm_stmt_code_length` 归一化为已迁移的 statement count，源 `cmc_concrete_function_ready.c` 也使用该改写。这是明确记录的源侧等价归一化；本例没有迁移完整 emitter 语义或在 Rocq 重证该长度桥。后续迁移 emitter 时需补齐对应桥接，不能将计数契约验证误报为已验证 TVM 输出。

继续使用同一个全称 lookup policy 和 codegen obligations，未添加目标编号边界、未删除原 wf 中的四项参数化 TVM 条件。具体 TVM 实例化仍待迁移。helper `cmc_function_code_count` 直接接入已验证完整契约，既有实现 proof 不重复计量。

## 已验证规模与信任边界

{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 完成；{N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，仍依赖 QCP 自动层。手工证明和新库无 Admitted/Axiom/Parameter。运行时 token、ABI 与既有依赖哈希保持不变。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |

新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，公共引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。源额外四项 readiness 定义 50 行及 cm_temp_offset 定义 10 行单列。既有库按已付成本复用；新增但未直接被 manual 引用的公共定理也计实际成本，见 shared-helper-usage.json。Proof 声明/包装与证明体、失败检查和重试分别记录；最终规模不是作者工时或公平工具效率比较。
'''
(S/'references/cmc-function-pc-total-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text()
s=s.replace('count-context 的 4 个包装函数；','count-context 的 4 个包装函数及 function-pc-total 的 2 个函数；')
s=s.replace('count-context 为 `cmc_count_context_migration.c`。','count-context 为 `cmc_count_context_migration.c`，function-pc-total 为 `cmc_function_pc_total_migration.c`。')
s=s.replace('文件末尾供 emitter 使用的 readiness 导出尚未迁移。','当时未迁移的 readiness 定义已在 function-pc-total 案例中补齐计数形式；完整 emitter 语义及桥接仍待迁移。')
entry=f'`cmc_concrete_function_pc_total.c` 于 2026-10-16 完成两个函数验证。涉及任意 target 的总前缀查询、无条件长度界和完整 readiness 归一化时，读取 [references/cmc-function-pc-total-case.md](references/cmc-function-pc-total-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
if 'references/cmc-function-pc-total-case.md' not in s:s=s.replace('这些结果覆盖八个具体实现文件的运行时部分、63 个运行时函数及必要依赖；',entry+'这些结果覆盖九个具体实现文件的运行时部分、65 个运行时函数及必要依赖；')
s=s.replace('counts 的 15 个运行时函数及 count-context 的 4 个包装函数及 function-pc-total','counts 的 15 个运行时函数、count-context 的 4 个包装函数及 function-pc-total')
p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text()
s=s.replace('及 count-context 的 4 个包装函数，共八个具体实现文件的运行时部分、63 个运行时函数','、count-context 的 4 个包装函数及 function-pc-total 的 2 个函数，共九个具体实现文件的运行时部分、65 个运行时函数')
s=s.replace('332、184、6 条可信自动',f'332、184、6、{N["automatic_witnesses"]} 条可信自动')
s=s.replace('[count-context 报告](experiments/cmc_count_context/REPORT.md)。','[count-context 报告](experiments/cmc_count_context/REPORT.md)、[function-pc-total 报告](experiments/cmc_function_pc_total/REPORT.md)。')
s=s.replace('readiness 导出待后续 emitter，','readiness 定义已在 function-pc-total 中补齐计数形式，emitter 桥接待迁移，')
row=f'| 已完成 | `cmc_concrete_function_pc_total.c` | 两个函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；保留任意 target，新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n'
if row not in s:s=s.replace('| 3：表示与尺寸的剩余部分 |',row+'| 3：表示与尺寸的剩余部分 |')
s=s.replace('、counts 中剩余 readiness 导出、`cmc_concrete_function_pc_total.c`','中尚未迁移的定义与引理')
s=s.replace('及 `cmc_concrete_count_context.c`。layout/counts','、`cmc_concrete_count_context.c` 及 `cmc_concrete_function_pc_total.c`。layout/counts')
a=s.index('五个基础写入/复制实现、layout、counts 的运行时部分与 count-context 四个包装函数已完成。');b=s.index('\n\n',a)
s=s[:a]+'五个基础写入/复制实现、layout、counts、count-context 与 function-pc-total 的运行时部分已完成。下一个候选是 `cmc_concrete_emit_globals.c`，之后处理 strings/data 等数据区生成。继续复用已验证公共库，新增成本单列。完整 emitter 语义、readiness 长度桥的 Rocq 重证及具体 TVM 实例化仍待后续迁移。'+s[b:];p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_function_pc_total.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_2_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions';buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
print('Published verified function-pc-total case and updated inventory.')
