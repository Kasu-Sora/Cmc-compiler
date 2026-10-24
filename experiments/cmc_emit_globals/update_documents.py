#!/usr/bin/env python3
"""Publish only the completed and audited globals migration."""
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
ref=f'''# 已验证案例：emit-globals，C* → QCP

2026-10-16，`cmc_concrete_emit_globals.c` 的完整递归 emitter 已迁移，run `{run}` 为 done、final-check passed，原 C* 重放通过。报告、语义审计和计量：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_globals/REPORT.md`。正式目标为 QCP 仓库的 `cmc_emit_globals_migration.c` 及对应 Rocq lib/manual。

## 保留字节级契约

保留原 globals safety 与完整逐节点 global-wf、非负 cursor、容量界及总空间条件；输出精确 prefix ++ cm_globals_bytes，并恢复全局链表和未初始化余段。空链表无需新增 data 非空前提。已初始化字符写一个低字节，其他已初始化标量写八个小端字节，无初始化对象写零。

数据区合法性不是完整 program-wf；直接复用 counts 中的 cm_global_wf，不把无关 lookup policy/codegen obligations 加入新契约。cm_global_wf 的标量约束排除 struct，但允许合法指针，且初始化指针必须为零；不能只保留证明眼前算术所需的部分合取项。新 cm_data_globals_wf 使用原逐节点递归合取。

## 连接已验证模型

counts 的初始化字节使用 map/seq 和除以 256 的幂，word 库使用八项 tower_encode_byte 与连续除法。保留两者原定义，证明等价；Z.div 的正除数连除法则适用于负数，不需加强为非负初始化值。字符复用 tower_u8，零填充复用 zeros/repeat。

保持 long long 到 int 的 size 转换。其安全性依赖原表示大小界；语义大小与表示大小在完整 global-wf 下连接，不在任意非法类型上宣称相等。复用已验证类型编码辅助引理，避免重复定义 AST、列表表示或大小模型。

四项 helper 接入契约与既有已验证 C 文件规范化后逐字一致：layout 的 cmc_code_slot_size，char、word 和 zeroes。它们的实现证明不重复计入新成本，实际依赖快照验证纯库复用，旧 auto/manual 不导入。

## 结果与工作量

{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 完成；{N['automatic_witnesses']} 条自动 witness 以 Admitted 导出。手工证明与新库无 Admitted/Axiom/Parameter。运行时 token、ABI 和复用依赖不变。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |
| 上述 proof 合计 | {C['proof_including_shared']} | {Q['proof_including_shared']} |

新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行、引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。源 private helper {C['private_case_proof_support']} 行计入案例 proof，不能遗漏或再计公共成本。最终合并库中的 helper 全部计量，已复用库不重复累计。声明包装、实际证明体、自动结果及失败修正分别记录；规模和重放耗时不是公平工具效率比较。
'''
(S/'references/cmc-emit-globals-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text()
s=s.replace('function-pc-total 的 2 个函数；','function-pc-total 的 2 个函数及 emit-globals 的递归函数；').replace('function-pc-total 为 `cmc_function_pc_total_migration.c`。','function-pc-total 为 `cmc_function_pc_total_migration.c`，emit-globals 为 `cmc_emit_globals_migration.c`。')
entry=f'`cmc_concrete_emit_globals.c` 于 2026-10-16 完成递归全局数据区生成验证。涉及精确字节输出、初始化分支、语义/表示大小桥及跨库字节编码一致性时，读取 [references/cmc-emit-globals-case.md](references/cmc-emit-globals-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
if 'references/cmc-emit-globals-case.md' not in s:s=s.replace('这些结果覆盖九个具体实现文件的运行时部分、65 个运行时函数及必要依赖；',entry+'这些结果覆盖十个具体实现文件的运行时部分、66 个运行时函数及必要依赖；')
p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('及 function-pc-total 的 2 个函数，共九个具体实现文件的运行时部分、65 个运行时函数','、function-pc-total 的 2 个函数及 emit-globals 的递归函数，共十个具体实现文件的运行时部分、66 个运行时函数')
s=s.replace('332、184、6、11 条可信自动',f'332、184、6、11、{N["automatic_witnesses"]} 条可信自动').replace('[function-pc-total 报告](experiments/cmc_function_pc_total/REPORT.md)。','[function-pc-total 报告](experiments/cmc_function_pc_total/REPORT.md)、[emit-globals 报告](experiments/cmc_emit_globals/REPORT.md)。')
row=f'| 已完成 | `cmc_concrete_emit_globals.c` | 递归生成精确全局字节；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n'
if row not in s:s=s.replace('| 4：数据区生成 |',row+'| 4：数据区生成 |')
s=s.replace('| 4：数据区生成 | `cmc_concrete_emit_globals.c`、','| 4：数据区生成 | ')
s=s.replace('及 `cmc_concrete_function_pc_total.c`。layout/counts','、`cmc_concrete_function_pc_total.c` 及 `cmc_concrete_emit_globals.c`。layout/counts')
a=s.index('五个基础写入/复制实现、layout、counts、count-context 与 function-pc-total 的运行时部分已完成。');b=s.index('\n\n',a)
s=s[:a]+'五个基础写入/复制实现、layout、counts、count-context、function-pc-total 与 emit-globals 的运行时部分已完成。下一个候选是 `cmc_concrete_emit_strings.c`，之后组合 emit-data。继续复用已验证公共库，新增成本单列；完整指令 emitter 语义、readiness 长度桥的 Rocq 重证及具体 TVM 实例化仍待后续迁移。'+s[b:];p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_globals.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_1_function_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions';buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines));print('Published verified globals migration and skill reference.')
