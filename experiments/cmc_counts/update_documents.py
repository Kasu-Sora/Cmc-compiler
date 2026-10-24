#!/usr/bin/env python3
"""Publish migration inventory and skill learning only after audited completion."""
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed'
assert A['final_verification']['status']=='passed'
Q=E['counts']['qcp'];C=E['counts']['cstar'];N=E['entries']
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
ref=f'''# 已验证案例：cmc_concrete_counts.c，C* → QCP

2026-10-16（Asia/Shanghai）完成 15 个运行时函数和 1 个前向声明。源 `/Users/nizitong/cmc/cmc_concrete_counts.c`；目标 `/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_counts_migration.c`。报告、快照与逐区间计量在 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_counts/`。

Run `cmc_counts_migration-20261015235041` 为 done，final-check passed；原 C* 重放通过。44 组、{N['manual_top_level']} 条顶层手工义务和 {N['manual_splits']} 个 split 完成。{N['automatic_witnesses']} 条自动 witness 以 Admitted 导出；{len(E['unused_split_drafts_aborted'])} 个未采用 split 草稿的父目标已整体证明。manual 与新增库没有 Admitted/Axiom/Parameter。运行时 token 和原源码一致，ABI 与已验证依赖哈希不变。

## 契约边界

- 计数模型按 AST/列表结构递归；保留左右值、语句、参数、序言、函数前缀、PC、代码/数据长度的原精确结果及 representability 子条件。
- 函数查询复用 layout 的同一全称 `cm_lookup_policy`；不能为方便证明补上源契约没有的 fid 范围。PC 允许 fid 等于函数列表长度；prefix 保留完整列表/后缀的 index 关系和 remaining 上界。
- model-data-length 的模型/表示尺寸等式原本就是源前提，不能误称本轮额外假定。
- 15 个运行时函数及必要依赖完成不等于文件中所有 PROOF 导出已迁移。末尾 cm_concrete_function_ready/cm_concrete_functions_ready 及 getter/export 不在当前闭包，留给后续 emitter。

### 无关 emitter/TVM 条件的显式参数化

`cm_wf_program` 保留 typed-program、代码/数据长度界、栈界及 codegen 条件的原合取。四项 emitter/TVM 条件由全称 `cm_codegen_obligations` record 携带，源实例为 code_shape(model_code p)、targets_valid(model_code p)、patches_valid(model_patches p)、target_valid(model_code p,0)。实际计数、类型、作用域、frame、stack、data 模型直接翻译。

证明对 record 任意取值成立，后续包装函数应沿用同一参数，不能删除这些合取。合取对应引理只是定义恒等式；尚无具体 Rocq emitter/TVM 实例化定理或完整跨内核等价证书。后续 emitter 迁移需要补具体模型及实例对应，不得宣称本例完成编译保持性。

## 公共库与并行成本

实际复用 layout/copy-bytes 纯库和既有 ABI；7 个 layout helper 以与已验证版本相同的契约接入，接入 annotation 单列。无需把已验证 helper 的 auto/manual 实现证明导入新案例。

新增 {len(N['new_model_declarations'])} 项定义/{Q['new_common_definitions']} 行、{len(N['new_helpers'])} 条公共引理/{Q['new_common_proof']} 行；证明阶段额外加入 28 条桥接引理，未改规格模型。库提供上下文表示、计数与合法性模型，以及类型编码/归一化、slot 类型、函数链表拆合、prefix 非负和长度界桥接。

本轮 worker 受 round-start frozen 公共快照约束，不能读取同轮后续晋升的 helper 或 sibling 输出。多组因此独立写了同义桥接，按最终合并文件全部计成本，不按候选池数量或语义去重后的数量计。类似任务可在 annotation 阶段提前准备反复需要的类型编码、normalize 和函数链表 cons 桥接；后续案例直接复用已完成的 counts 库，不复制同义定义。

## 工作量与验证口径

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（原 include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |

C* 案例 proof 包含 {C['inline_proof']} 内联和 {C['private_case_proof_support']} 私有辅助行；原文件公开辅助去重闭包另计。目标 proof 包含 {E['proof_body_lines']} 证明体和 {E['proof_wrapper_lines']} 包装行。长单行规格另给词法 token/字符数；历史作者活跃工时未知，不能以行数或本次重放时间判定效率。

annotation acceptance 复用了 owner 符号执行 receipt 并验证封存/新鲜度；不是该阶段独立重跑 symexec。完整 parent check 和 final-check 均已通过。4 个父目标因分割丢失空表等式所需堆前提而改走整体证明，不把它们认定为需要加强契约的缺口。一次并发状态 compare-and-swap 冲突通过 controller step 和幂等 finalize 恢复，未手改 state 或 formal 文件。过程失败/修正与完整时间见报告。
'''
(S/'references/cmc-counts-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text()
s=s.replace('以及整个 layout 文件的 39 个函数；','以及整个 layout 文件的 39 个函数和 counts 的 15 个运行时函数；')
s=s.replace('layout 为 `cmc_layout_migration.c`。','layout 为 `cmc_layout_migration.c`，counts 为 `cmc_counts_migration.c`。')
entry=f'`cmc_concrete_counts.c` 于 2026-10-16 完成 15 个运行时函数的验证。处理精确计数、上下文表示、无关 codegen 条件的显式参数化、冻结公共库下的复用或增量计量时，读取 [references/cmc-counts-case.md](references/cmc-counts-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增 {len(N["new_model_declarations"])} 项定义和 {len(N["new_helpers"])} 条公共引理。文件末尾供 emitter 使用的 readiness 导出尚未迁移。\n\n'
if 'references/cmc-counts-case.md' not in s:s=s.replace('这些结果覆盖六个具体实现文件、44 个运行时函数及必要依赖；',entry+'这些结果覆盖七个具体实现文件的运行时部分、59 个运行时函数及必要依赖；')
p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text();first=s.split('\n\n',2)
first[1]=first[1].replace('清点日期：2026-10-15。','清点更新：2026-10-16。').replace('和 layout 整文件 39 个函数，共六个具体实现文件、44 个运行时函数','、layout 整文件 39 个函数和 counts 的 15 个运行时函数，共七个具体实现文件的运行时部分、59 个运行时函数').replace('332 条可信自动','332、184 条可信自动').replace('、[layout 报告](experiments/cmc_layout/REPORT.md)。','、[layout 报告](experiments/cmc_layout/REPORT.md)、[counts 报告](experiments/cmc_counts/REPORT.md)。')
s='\n\n'.join(first)
row=f'| 已完成运行时部分 | `cmc_concrete_counts.c` | 15 个函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；readiness 导出待后续 emitter，四项 TVM 条件保留参数化边界 |\n'
if row not in s:s=s.replace('| 3：表示与尺寸的剩余部分 |',row+'| 3：表示与尺寸的剩余部分 |')
s=s.replace('`cmc_concrete_counts.c`、`cmc_concrete_count_context.c`','counts 中剩余 readiness 导出、`cmc_concrete_count_context.c`')
s=s.replace('和 `cmc_concrete_layout.c`。layout 的必要模型闭包','、`cmc_concrete_layout.c` 和 counts 的运行时部分。layout/counts 的必要模型闭包')
start=s.index('五个基础写入/复制实现及 layout 整文件已完成。');end=s.index('\n\n',start)
s=s[:start]+'五个基础写入/复制实现、layout 与 counts 的运行时部分已完成。按用户要求自动推进 `cmc_concrete_count_context.c` 的 4 个包装函数，复用已验证 counts/layout 公共库并单列接入 annotation 和新增引理成本。之后可检查 `cmc_concrete_function_pc_total.c`，再处理 globals/strings 等数据区生成。counts 的 readiness 导出和 emitter/TVM 具体实例化仍待后续迁移。'+s[end:]
p.write_text(s)
p=W/'migration_inventory.csv';data=p.read_bytes();lines=data.splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_counts.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_15_runtime_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_readiness_exports_pending';buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
print('Updated counts report routing, migration inventory and skill reference after verified completion.')
