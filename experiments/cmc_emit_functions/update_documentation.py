"""Publish only after complete formal validation and independent semantic audit."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/semantic-audit.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):
 assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/validated-lessons.md').read_text();assert lessons.strip()
date=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d')
p=S/'references/cmc-emit-functions-case.md';assert not p.exists()
p.write_text(f'''# 已验证案例：emit-functions，C* → QCP

{date} 完成 `cmc_concrete_emit_functions.c` 的唯一运行时函数 `cmc_emit_functions` 及必要 proof 支持。C* 隔离重放与 QCP 完整终检通过。完整报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_functions/REPORT.md`。

## 契约与复用

保留任意 functions/fid/PC/done/tail、完整 readiness 与 wf/typed/表示安全/数据大小事实，以及 program-context 和整个函数链表资源。空列表无额外 fid 非负条件。按当前 fid 生成头函数，然后以 fid+1 和精确下一 PC 发射尾部，保持原计划消费与输出追加语义。运行体和 ABI 不变。

复用 counts 和 emit-function 的两个已验证 BODY 契约、原 readiness 和函数链表表示、单函数发射模型及 statement 长度定理。新增定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行。沿用已有 policy/cg 参数化边界；本例不增加 TVM 执行、终止性、链接或编译保持性定理。

## 经验证的经验

{lessons.strip()}

## 成本与信任

完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split，另有 {e['automatic_witnesses']} 条自动 witness 以 Admitted 导出。manual 和新增库没有 Admitted/Axiom/Parameter。非空非纯注释行：

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {c['new_public_definitions']} | {q['new_common_definitions']} |
| 新增公共 proof | {c['exported_shared_proof_closure']+c['additional_public_proof_closure']} | {q['new_common_proof']} |

源案例 proof 包含 26 行私有 ready-fact 支持；已有公共支持不再计新增成本。行数受排版影响，报告同时提供 token、字符、调用失败和逐函数区间，不推断历史工时。
''')
p=S/'SKILL.md';t=p.read_text()
old='及 emit-function 的三个函数（含必要 function proof 支持）；';assert old in t
t=t.replace(old,'及 emit-function 的三个函数（含必要 function proof 支持）及 emit-functions 的一个函数（含必要 proof 支持）；')
t=t.replace('emit-function 为 `cmc_emit_function_migration.c`。','emit-function 为 `cmc_emit_function_migration.c`，emit-functions 为 `cmc_emit_functions_migration.c`。')
old='这些结果覆盖二十六个具体实现迁移单元的运行时部分、126 个运行时函数';assert old in t
entry=f'`cmc_concrete_emit_functions.c` 于 {date} 完成唯一运行时函数及必要 proof 支持验证。涉及函数列表递归、readiness 展开、函数 PC 推进、链表资源恢复及单函数发射复用时，读取 [references/cmc-emit-functions-case.md](references/cmc-emit-functions-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace(old,entry+'这些结果覆盖二十七个具体实现迁移单元的运行时部分、127 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text()
old='及 emit-function 的三个函数（含必要 function proof 支持），共二十六个具体实现迁移单元的运行时部分、126 个运行时函数';assert old in t
t=t.replace(old,'及 emit-function 的三个函数（含必要 function proof 支持）及 emit-functions 的一个函数（含必要 proof 支持），共二十七个具体实现迁移单元的运行时部分、127 个运行时函数')
t=t.replace('224、106 条可信自动 witness',f'224、106、{e["automatic_witnesses"]} 条可信自动 witness')
t=t.replace('[emit-function 报告](experiments/cmc_emit_function/REPORT.md)。','[emit-function 报告](experiments/cmc_emit_function/REPORT.md)、[emit-functions 报告](experiments/cmc_emit_functions/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 | `cmc_concrete_emit_functions.c`、',f'| 已完成 | `cmc_concrete_emit_functions.c` 及必要 proof 支持 | 一个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
t=t.replace('emit-stmt 与 emit-function 的运行时部分已完成','emit-stmt、emit-function 与 emit-functions 的运行时部分已完成')
t=t.replace('下一候选为 `cmc_concrete_emit_functions.c`','下一候选为 `cmc_concrete_emit_prelude.c`')
p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_functions.c,'):
  assert b',not_migrated,' in row
  rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_1_function_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows))
print('Published verified functions reference, skill routing, plan and one inventory row.')
