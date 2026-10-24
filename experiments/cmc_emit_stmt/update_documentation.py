"""Publish only the fully verified stmt case and its necessary proof support."""
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());e=x['entries'];q=x['counts']['qcp'];c=x['counts']['cstar'];d=x['source_additional_dependency_definitions']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/semantic-audit.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/validated-lessons.md').read_text();assert lessons.strip()
date=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d')
case=S/'references/cmc-emit-stmt-case.md';assert not case.exists()
case.write_text(f'''# 已验证案例：emit-stmt，C* → QCP

{date} 完成 `cmc_concrete_emit_stmt.c` 两个运行时函数 `cmc_emit_if_stmt`、`cmc_emit_stmt`，包含必要的 stmt proof 支持。C* 重放与 QCP 完整终检通过。完整计量与日志：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_stmt/REPORT.md`。

## 契约与复用

保留原全部纯事实、完整 program/function/statement 资源、原 loop 标志及 PC/temp/break/continue 界，精确消费语句代码并追加至 done，保留任意 tail。if 构造子条件不变；while 子体 loop=true、break=end、continue=guard PC。运行体和 ABI 不变，不增强输入限制。沿用已验证 policy/cg 参数化边界。本例是 BODY 的模块化规约验证，不产生 TVM 执行、终止性或编译保持性结论。

复用 expr、return、AST、plan、count-context、layout 的九个 helper BODY 契约与公共库闭包，两个互递归前向声明与各自 BODY 合同一致。新增公共定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行；既有 helper 实现 proof 不重复计费。

## 经验证的迁移经验

{lessons.strip()}

## 计量与信任

{e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split 完成；另有 {e['automatic_witnesses']} 条自动 witness 以 Admitted 导出。manual 和新增库无 Admitted/Axiom/Parameter。非空行：

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {d['definition_lines']} | {q['new_common_definitions']} |
| 新增公共 proof | {d['public_proof_lines']} | {q['new_common_proof']} |

源公共 proof 包含 stmt_proof.c 的 162 行及长度定理支持的 28 行。源 expr 中同名 rvalue-length helper 是 static；此处新导出的 19 行仍计入本例。物理行受排版影响，不代表工时；区间、token/字符、分轮检查与修复见报告。历史工时未知记 null。
''')
p=S/'SKILL.md';t=p.read_text();t=t.replace('及 emit-return 的一个函数；','及 emit-return 的一个函数及 emit-stmt 的两个函数（含必要 stmt proof 支持）；').replace('emit-return 为 `cmc_emit_return_migration.c`。','emit-return 为 `cmc_emit_return_migration.c`，emit-stmt 为 `cmc_emit_stmt_migration.c`。')
entry=f'`cmc_concrete_emit_stmt.c` 于 {date} 完成两个运行时函数及必要 stmt proof 支持验证。涉及语句互递归、if/while 跳转、构造子投影、局部资源开闭及增量计量时，读取 [references/cmc-emit-stmt-case.md](references/cmc-emit-stmt-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
old='这些结果覆盖二十四个具体实现迁移单元的运行时部分、121 个运行时函数';assert old in t;t=t.replace(old,entry+'这些结果覆盖二十五个具体实现迁移单元的运行时部分、123 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();t=t.replace('及 emit-return 的一个函数，共二十四个具体实现迁移单元的运行时部分、121 个运行时函数','及 emit-return 的一个函数及 emit-stmt 的两个函数（含必要 stmt proof 支持），共二十五个具体实现迁移单元的运行时部分、123 个运行时函数').replace('449、24 条可信自动 witness',f'449、24、{e["automatic_witnesses"]} 条可信自动 witness').replace('[emit-return 报告](experiments/cmc_emit_return/REPORT.md)。','[emit-return 报告](experiments/cmc_emit_return/REPORT.md)、[emit-stmt 报告](experiments/cmc_emit_stmt/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 |',f'| 已完成 | `cmc_concrete_emit_stmt.c` 及必要 `cmc_concrete_emit_stmt_proof.c` 支持 | 两个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 |').replace('| 5：指令与程序生成 | `cmc_concrete_emit_stmt*.c`、','| 5：指令与程序生成 | ')
t=t.replace('、`cmc_concrete_emit_stmt_proof.c` | 在 Rocq',' | 在 Rocq')
t=t.replace('emit-expr 与 emit-return 的运行时部分已完成','emit-expr、emit-return 与 emit-stmt 的运行时部分已完成').replace('下一候选为 `cmc_concrete_emit_stmt.c`（连同必要的 stmt proof 支持）','下一候选为 `cmc_concrete_emit_function.c`')
p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
statuses={'cmc_concrete_emit_stmt.c':f'qcp_pipeline_verified_2_functions_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto','cmc_concrete_emit_stmt_proof.c':'qcp_required_support_migrated_with_emit_stmt'}
for name,status in statuses.items():
 for i,row in enumerate(rows):
  if row.startswith(('/Users/nizitong/cmc/'+name+',').encode()):
   assert b',not_migrated,' in row;rows[i]=row.replace(b',not_migrated,',(','+status+',').encode());break
 else:raise AssertionError('Missing inventory row: '+name)
p.write_bytes(b''.join(rows));print('Updated verified stmt skill reference, plan and two inventory rows.')
