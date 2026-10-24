"""Publish only verified case evidence and close the prior recursive dependency note."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());q=x['counts']['qcp'];c=x['counts']['cstar'];e=x['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/recursive-contract-link.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/verified-lessons.md').read_text()
case=f'''# 已验证案例：emit-expr，C* → QCP

2026-10-19 完成 cmc_concrete_emit_expr.c 七个运行时函数，包括 intrinsic/unary/index/assignment/binary/member 六个 static helper 和公共 cm_emit_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。完整报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr/REPORT.md`。

## 契约与递归衔接

保留原构造子条件、lvalue 两分支、全部 wf/typed/count/slot/表示安全事实、PC 起止界、临时槽预算、完整 program/function/expression 所有权，以及精确生成列表、done 追加和任意 tail。运行体 token 与共享 ABI 不变，没有新增输入限制。既有 lookup policy 与 codegen obligations 参数化边界不变。

复用 call 案例的一般表达式代码模型和长度/count 定理，以及 binary-finish、simple、plan、count-context、leaf 的既有接口。十五个外部 helper 契约与其已验证 BODY 合同核对；cm_emit_expr 实现规约与上一例 call 的外部假定契约匹配，补齐该模块化实现依赖。同文件前向声明保持 BODY 合同且重复成本另列。不要把既有 helper 实现 proof 或整套共享模型重复计入本例。

这是各函数 BODY 的模块化规约验证，没有新增终止性、跨模块链接元定理、HOL→Rocq 等价或 TVM 执行保持性结论。

## 经验证的迁移经验

{lessons}

## 计量与信任

{e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split 完成；{e['automatic_witnesses']} 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。manual 与新增公共库无 Admitted/Axiom/Parameter，未采用的 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个单列。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共 proof 依赖 | {c['additional_public_proof_closure']} | {q['new_common_proof']} |

QCP 新增公共定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行、引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行，以最终合并库计量。C* 案例 proof 含 26 项私有辅助；其新增公共模型与证明闭包单列在 source-additional-definitions.json。物理行受排版影响，不能当作工时；精确区间、token/字符、失败修复与实际调用记录见报告和 effort.json。未知历史时间为 null。
'''
(S/'references/cmc-emit-expr-case.md').write_text(case)
p=S/'SKILL.md';t=p.read_text();t=t.replace('emit-expr-call、emit-binary-finish 各三个函数；','emit-expr-call、emit-binary-finish 各三个函数及 emit-expr 的七个函数；').replace('emit-binary-finish 为 `cmc_emit_binary_finish_migration.c`。','emit-binary-finish 为 `cmc_emit_binary_finish_migration.c`，emit-expr 为 `cmc_emit_expr_migration.c`。')
t=t.replace('通用 `cm_emit_expr` 的原外部契约保留，其实现证明仍待迁移。','通用 `cm_emit_expr` 的原外部契约保留，其实现规约已由后续 emit-expr 案例验证并核对契约衔接。')
entry=f'`cmc_concrete_emit_expr.c` 于 2026-10-19 完成七个运行时函数验证。涉及通用表达式递归、短路跳转、PC/临时槽界和相互递归模块契约衔接时，读取 [references/cmc-emit-expr-case.md](references/cmc-emit-expr-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace('这些结果覆盖二十二个具体实现文件的运行时部分、113 个运行时函数',entry+'这些结果覆盖二十三个具体实现迁移单元的运行时部分、120 个运行时函数');p.write_text(t)
p=S/'references/cmc-emit-expr-call-case.md';t=p.read_text();t+='\n## 后续依赖补齐\n\n2026-10-19，通用表达式生成文件的七个运行时函数（含 `cm_emit_expr`）已在 [emit-expr 案例](cmc-emit-expr-case.md) 完成验证，并核对其实现合同与本例假定的外部合同一致。本例原始计量和验证范围不回溯修改；这是模块化契约衔接，没有新增终止性或 TVM 保持性元定理。\n';p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text().replace('清点更新：2026-10-18。','清点更新：2026-10-19。');t=t.replace('emit-expr-call、emit-binary-finish 各三个函数，共二十二个具体实现文件的运行时部分、113 个运行时函数','emit-expr-call、emit-binary-finish 各三个函数及 emit-expr 的七个函数，共二十三个具体实现迁移单元的运行时部分、120 个运行时函数');t=t.replace('60、127 条可信自动 witness',f'60、127、{e["automatic_witnesses"]} 条可信自动 witness').replace('[emit-binary-finish 报告](experiments/cmc_emit_binary_finish/REPORT.md)。','[emit-binary-finish 报告](experiments/cmc_emit_binary_finish/REPORT.md)、[emit-expr 报告](experiments/cmc_emit_expr/REPORT.md)。')
t=t.replace('通用 cm_emit_expr 实现仍为待迁移依赖','通用 cm_emit_expr 实现已由 emit-expr 案例补齐')
t=t.replace('| 5：指令与程序生成 |',f'| 已完成 | `cmc_concrete_emit_expr.c` | 七个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；补齐 call 的通用表达式实现依赖；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 |')
t=t.replace('`cmc_concrete_emit_expr*.c`（leaf、var、dispatch、simple 已完成；call 已完成模块化验证）、','')
t=t.replace('emit-expr-call 与 emit-binary-finish 的运行时部分已完成模块化验证。下一候选为通用 `cmc_concrete_emit_expr.c`，以补齐 call 的外部实现依赖','emit-expr-call、emit-binary-finish 与 emit-expr 的运行时部分已完成模块化验证，call 的通用表达式实现依赖已补齐。下一候选为 `cmc_concrete_emit_return.c`');p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_expr.c,'):
  assert b',not_migrated,' in row;rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_7_functions_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows));print('Updated verified skill evidence, recursive dependency note, plan and inventory.')
