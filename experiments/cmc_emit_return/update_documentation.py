"""Publish only the fully verified return case and update exact inventory scope."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());e=x['entries'];q=x['counts']['qcp'];c=x['counts']['cstar']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
case=S/'references/cmc-emit-return-case.md';assert not case.exists()
case.write_text(f'''# 已验证案例：emit-return，C* → QCP

2026-10-19 完成 `cmc_concrete_emit_return.c` 的唯一运行时函数 `cm_emit_return_epilogue_plan`，C* 重放与 QCP 完整终检通过。完整计量与日志：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_return/REPORT.md`。

## 契约与复用

保留任意 program、done、tail、out、capacity；消费 `cm_return_epilogue ++ tail`，得到 `done ++ cm_return_epilogue` 与原 tail。沿用已验证 resolved plan 表示中的 lookup-policy 参数。运行体和 ABI 不变，不添加输入限制。精确尾声为 PUSH 8、LOAD 0、LOAD 0、PUSH 8、STORE 0、RET 0；本例验证输出片段生成，不等于证明该 RET 的 TVM 执行效果。

复用 `cm_emit_plan` 的已验证 BODY 契约及公共库闭包。新增公共定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行；已验证 helper 实现证明不重复计费。

## 经验证的迁移经验

对固定指令片段，函数契约保留命名代码列表；若 QCP 无法把该列表直接匹配到逐指令 helper 的 cons 前提，在调用边界把同一列表展开，并建立固定 opcode 编码及非 CALL 事实。该断言必须保留 emitter 局部单元和完整 plan，并由原前提单独证明，不能变成额外用户前提。本例一次建立四个 opcode 的八项事实，随后六个 where 实例按前次 helper 的后置形式指定嵌套追加的 done 和剩余 tail。

最后把嵌套的单指令追加重结合为 `done ++ cm_return_epilogue`。先复用列表定义归约、结合律与现有资源取消；本例的最终公共引理数和成本以上述合并结果为准，不为固定列表额外复制 plan 表示或整套 emitter 模型。

## 计量与信任

{e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split 完成；另有 {e['automatic_witnesses']} 条自动 witness 以 Admitted 导出。manual 和新增库无 Admitted/Axiom/Parameter。非空行：

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | 5 | {q['new_common_definitions']} |
| 新增公共 proof | {c['additional_public_proof_closure']} | {q['new_common_proof']} |

长 where 单行与 C* 多条短属性的格式不同，不能按物理行推断难度。报告另存区间、条目、token/字符、失败修复及调用量；历史工时未知记 null。
''')
p=S/'SKILL.md';t=p.read_text();t=t.replace('及 emit-expr 的七个函数；','及 emit-expr 的七个函数及 emit-return 的一个函数；').replace('emit-expr 为 `cmc_emit_expr_migration.c`。','emit-expr 为 `cmc_emit_expr_migration.c`，emit-return 为 `cmc_emit_return_migration.c`。')
entry=f'`cmc_concrete_emit_return.c` 于 2026-10-19 完成唯一运行时函数验证。涉及固定指令片段、命名列表展开、逐调用计划与前缀重结合时，读取 [references/cmc-emit-return-case.md](references/cmc-emit-return-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
old='这些结果覆盖二十三个具体实现迁移单元的运行时部分、120 个运行时函数';assert old in t;t=t.replace(old,entry+'这些结果覆盖二十四个具体实现迁移单元的运行时部分、121 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();t=t.replace('及 emit-expr 的七个函数，共二十三个具体实现迁移单元的运行时部分、120 个运行时函数','及 emit-expr 的七个函数及 emit-return 的一个函数，共二十四个具体实现迁移单元的运行时部分、121 个运行时函数').replace('127、449 条可信自动 witness',f'127、449、{e["automatic_witnesses"]} 条可信自动 witness').replace('[emit-expr 报告](experiments/cmc_emit_expr/REPORT.md)。','[emit-expr 报告](experiments/cmc_emit_expr/REPORT.md)、[emit-return 报告](experiments/cmc_emit_return/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 |',f'| 已完成 | `cmc_concrete_emit_return.c` | 返回尾声生成；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 |').replace('| 5：指令与程序生成 | `cmc_concrete_emit_return.c`、','| 5：指令与程序生成 | ')
t=t.replace('emit-binary-finish 与 emit-expr 的运行时部分已完成','emit-binary-finish、emit-expr 与 emit-return 的运行时部分已完成').replace('下一候选为 `cmc_concrete_emit_return.c`','下一候选为 `cmc_concrete_emit_stmt.c`（连同必要的 stmt proof 支持）');p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_return.c,'):
  assert b',not_migrated,' in row;rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_1_function_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing return inventory row')
p.write_bytes(b''.join(rows));print('Updated verified return skill reference, plan and inventory.')
