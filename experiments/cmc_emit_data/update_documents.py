#!/usr/bin/env python3
"""Update migration guidance only after verified and audited delivery."""
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed'
assert A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries']
run=json.loads((R/'metrics/run.json').read_text())['run_id']
ref=f'''# 已验证案例：emit-data，C* → QCP

2026-10-16，`cmc_concrete_emit_data.c` 的组合函数已迁移。C* 原证明重放通过，QCP run `{run}` 为 done、final-check passed。报告与审计：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_data/REPORT.md`。目标为 QCP 仓库的 `cmc_emit_data_migration.c` 及对应 Rocq 文件。

## 原契约与 helper 组合

保留 Require 和 Ensure 的全部七项纯条件：globals 安全性、完整 data-globals-wf、strings 安全性、两项大小非负、总空间界及 INT_MAX 容量界；同时恢复两条源链表及源字符串数组。不要因为某些后置纯事实可推出就漏掉原规格。精确输出八个零字节、globals 字节、strings 字节，拼接顺序和返回末端与原规格一致；不引入额外 program-wf、codegen 或非空 data 条件。

已有 globals/strings 公共库及其依赖涵盖本例需要的数学模型。三个 helper 的契约从已验证的 cmc_write_zeroes、cmc_emit_globals、cmc_emit_strings 原样接入，不重复证明其实现，也不导入旧 auto/manual。helper 接入行数与函数体 annotation 分别统计。

## 资源形状归一化

本次直接串联调用的初稿在 symexec 阶段未能自动匹配 zeroes 的 `[0,0+8)`、`nil ++ zeros(8)` 与 globals 所需的 `[0,8)`、`zeros(8)`。这些表达式数学等价，但工具的资源匹配未必自动归约。保留原 helper 契约，在必要调用边界给出可证明的规范形式断言，完整保留两条链表、纯条件和未初始化余段。不要为了绕过匹配而改写运行时代码、强化前提或修改已验证 helper 规格。

这种断言需要实际生成并完成 VC，不是允许假定等价性。先检查失败报告中具体的端点和字节列表差异，再选择最小归一化位置；不要求所有 helper 调用都添加 Assert。同一 annotation attempt 中失败和修改仍计入过程成本。

## 验证与计量

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split；{N['automatic_witnesses']} 条自动结果以 Admitted 导出，依赖 QCP 自动层。手工证明及新增库无 Admitted/Axiom/Parameter。运行时 token、ABI、复用依赖不变。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |
| 上述 proof 合计 | {C['proof_including_shared']} | {Q['proof_including_shared']} |

新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。阶段增量、失败检查和实际产物引用均记录在报告中。已有依赖不重复计量，历史工时未知；行数不是公平工具效率比较。本例不代表整个 CMC/TVM 编译保持性迁移完成。
'''
(S/'references/cmc-emit-data-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text()
s=s.replace('emit-globals 和 emit-strings 的递归函数；','emit-globals 和 emit-strings 的递归函数及 emit-data 的组合函数；')
s=s.replace('emit-strings 为 `cmc_emit_strings_migration.c`。','emit-strings 为 `cmc_emit_strings_migration.c`，emit-data 为 `cmc_emit_data_migration.c`。')
entry=f'`cmc_concrete_emit_data.c` 于 2026-10-16 完成数据区组合函数验证。涉及 helper 串联、资源端点/字节列表归一化和完整后置纯事实保留时，读取 [references/cmc-emit-data-case.md](references/cmc-emit-data-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
assert 'references/cmc-emit-data-case.md' not in s
s=s.replace('这些结果覆盖十一个具体实现文件的运行时部分、67 个运行时函数及必要依赖；',entry+'这些结果覆盖十二个具体实现文件的运行时部分、68 个运行时函数及必要依赖；')
p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text()
s=s.replace('emit-globals 和 emit-strings 的递归函数，共十一个具体实现文件的运行时部分、67 个运行时函数','emit-globals 和 emit-strings 的递归函数及 emit-data 组合函数，共十二个具体实现文件的运行时部分、68 个运行时函数')
s=s.replace('332、184、6、11、9、12 条可信自动',f'332、184、6、11、9、12、{N["automatic_witnesses"]} 条可信自动')
s=s.replace('[emit-strings 报告](experiments/cmc_emit_strings/REPORT.md)。','[emit-strings 报告](experiments/cmc_emit_strings/REPORT.md)、[emit-data 报告](experiments/cmc_emit_data/REPORT.md)。')
old='| 4：数据区生成 | `cmc_concrete_emit_data.c` | 全局变量和字符串的精确字节输出；复用前述字节写入与表示层 |'
assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_data.c` | 八个零字节、globals、strings 的精确组合；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |')
s=s.replace('及 `cmc_concrete_emit_strings.c`。layout/counts','、`cmc_concrete_emit_strings.c` 及 `cmc_concrete_emit_data.c`。layout/counts')
s=s.replace('function-pc-total、emit-globals 与 emit-strings 的运行时部分已完成。下一个候选是组合数据区的 `cmc_concrete_emit_data.c`。','function-pc-total、emit-globals、emit-strings 与 emit-data 的运行时部分已完成。下一阶段转向指令生成，先审查 `cmc_concrete_emit_core.c` 的依赖闭包。')
p.write_text(s.replace('` 、','`、'))
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_data.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_1_function_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions'
  buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
print('Updated verified data case, skill reference, plan and inventory.')
