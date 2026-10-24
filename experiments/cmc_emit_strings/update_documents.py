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
ref=f'''# 已验证案例：emit-strings，C* → QCP

2026-10-16，`cmc_concrete_emit_strings.c` 的唯一递归函数已迁移。C* 原证明重放通过，QCP run `{run}` 为 done、final-check passed。报告与审计：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_strings/REPORT.md`。目标为 QCP 仓库的 `cmc_emit_strings_migration.c` 及对应 Rocq 文件。

## 保持原契约与空字符串语义

保留原字符串安全条件、cursor 非负、总输出空间及容量界。每个字符串原样复制并追加一个零字节，精确得到 prefix ++ cm_strings_bytes；恢复整个源链表及各源字节数组，精确返回新 cursor 并保留未初始化余段。

空字符串长度为零但仍输出一个终止零字节；它的源指针不需非空。源 cm_uint8_buffer 在空字节列表上是 emp，接入 copy helper 的零长度完整数组表示时要证明空分支对应关系，再在返回时恢复原表示。不得为了省去此分支而增加 source != 0、非空 bytes 或额外 string-wf 前提。

## 复用与标注

字符串描述符、大小、安全条件和链表表示已在 layout 中迁移；精确 cm_strings_bytes 来自 counts；条件非空谓词来自 copy-bytes。直接导入已有定义，不复制相同模型。两个 helper 接入契约分别来自已验证 cmc_copy_bytes 与 cmc_write_byte，语义及规范化文字一致。

本例仅用一个调用边界 Assert 暴露 head/tail、源数组和由原条件推出的长度与容量事实。copy 的 prefix 显式指定，write-byte 的 model_byte 指定为 0，递归 tail/prefix 从当前资源推断。不要把 Assert 内存在量名字用于其作用域之外的 where。递归返回后的拼接结合律和表示折叠留在 proof 中，不为此增加运行时代码。

## 验证与计量

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split；{N['automatic_witnesses']} 条自动结果以 Admitted 导出，依赖 QCP 自动层。手工证明和新增公共库无 Admitted/Axiom/Parameter。运行时 token、ABI、既有公共依赖不变。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |
| 上述 proof 合计 | {C['proof_including_shared']} | {Q['proof_including_shared']} |

新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。C* 私有支持 {C['private_case_proof_support']} 行计入案例 proof。最终合并后的引理与引用才是计量依据；不因标注阶段使用 import-only 库就预设整个案例公共成本为零。最终产物规模不能代替人工工时或公平工具效率比较。
'''
(S/'references/cmc-emit-strings-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text()
s=s.replace('及 emit-globals 的递归函数；','、emit-globals 和 emit-strings 的递归函数；')
s=s.replace('emit-globals 为 `cmc_emit_globals_migration.c`。','emit-globals 为 `cmc_emit_globals_migration.c`，emit-strings 为 `cmc_emit_strings_migration.c`。')
entry=f'`cmc_concrete_emit_strings.c` 于 2026-10-16 完成递归字符串数据区生成验证。涉及空字符串、源数组保持、零终止字节和跨 helper 表示转换时，读取 [references/cmc-emit-strings-case.md](references/cmc-emit-strings-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
assert 'references/cmc-emit-strings-case.md' not in s
s=s.replace('这些结果覆盖十个具体实现文件的运行时部分、66 个运行时函数及必要依赖；',entry+'这些结果覆盖十一个具体实现文件的运行时部分、67 个运行时函数及必要依赖；')
p.write_text(s.replace('函数 、','函数、').replace('` 、','`、'))
p=W/'MIGRATION_PLAN.md';s=p.read_text()
s=s.replace('及 emit-globals 的递归函数，共十个具体实现文件的运行时部分、66 个运行时函数','、emit-globals 和 emit-strings 的递归函数，共十一个具体实现文件的运行时部分、67 个运行时函数')
s=s.replace('332、184、6、11、9 条可信自动',f'332、184、6、11、9、{N["automatic_witnesses"]} 条可信自动')
s=s.replace('[emit-globals 报告](experiments/cmc_emit_globals/REPORT.md)。','[emit-globals 报告](experiments/cmc_emit_globals/REPORT.md)、[emit-strings 报告](experiments/cmc_emit_strings/REPORT.md)。')
row=f'| 已完成 | `cmc_concrete_emit_strings.c` | 原字符串字节和零终止输出、源数组保持；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n'
s=s.replace('| 4：数据区生成 | `cmc_concrete_emit_strings.c`、',row+'| 4：数据区生成 | ')
s=s.replace('及 `cmc_concrete_emit_globals.c`。layout/counts','、`cmc_concrete_emit_globals.c` 及 `cmc_concrete_emit_strings.c`。layout/counts')
s=s.replace('function-pc-total 与 emit-globals 的运行时部分已完成。下一个候选是 `cmc_concrete_emit_strings.c`，之后组合 emit-data。','function-pc-total、emit-globals 与 emit-strings 的运行时部分已完成。下一个候选是组合数据区的 `cmc_concrete_emit_data.c`。')
p.write_text(s.replace('函数 、','函数、').replace('` 、','`、'))
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_strings.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_1_function_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions'
  buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
print('Updated verified strings case, skill reference, plan and inventory.')
