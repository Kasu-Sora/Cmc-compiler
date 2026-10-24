"""Publish only after full verification and semantic audit."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/semantic-audit.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/validated-lessons.md').read_text();assert lessons.strip()
date=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d')
p=S/'references/cmc-emit-prelude-case.md';assert not p.exists()
p.write_text(f'''# 已验证案例：emit-prelude，C* → QCP

{date} 完成 `cmc_concrete_emit_prelude.c` 唯一运行时函数 `cmc_emit_prelude` 及必要 proof 支持。C* 隔离重放与 QCP 完整终检通过。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_prelude/REPORT.md`。

## 契约与复用

仅需原程序上下文和计划资源，无新增 wf/typed/readiness、main_id 非负或有效入口限制。生成精确 11 条指令，CALL 采用既有 policy 下 main_id 的总 PC 查询；保留上下文，输出追加到任意 done，保留任意 tail。运行体和 ABI 不变。

复用 cm_emit_plan 与 cm_emit_call_plan 已验证 BODY 契约及计划/上下文公共库。新增定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行。此例不新增 TVM 执行、main 终止性、链接或编译保持性定理。

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

已有公共支持不重复计费。行数受格式影响；报告另有 token、字符、调用失败和精确区间，不据此推断历史工时。
''')
p=S/'SKILL.md';t=p.read_text()
old='及 emit-functions 的一个函数（含必要 proof 支持）；';assert old in t
t=t.replace(old,'及 emit-functions 的一个函数（含必要 proof 支持）及 emit-prelude 的一个函数；')
t=t.replace('emit-functions 为 `cmc_emit_functions_migration.c`。','emit-functions 为 `cmc_emit_functions_migration.c`，emit-prelude 为 `cmc_emit_prelude_migration.c`。')
old='这些结果覆盖二十七个具体实现迁移单元的运行时部分、127 个运行时函数';assert old in t
entry=f'`cmc_concrete_emit_prelude.c` 于 {date} 完成唯一运行时函数及必要 proof 支持验证。涉及固定序列计划展开、程序上下文保持、任意 main_id 的总 PC 查询及无额外合法性前提时，读取 [references/cmc-emit-prelude-case.md](references/cmc-emit-prelude-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace(old,entry+'这些结果覆盖二十八个具体实现迁移单元的运行时部分、128 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text()
old='及 emit-functions 的一个函数（含必要 proof 支持），共二十七个具体实现迁移单元的运行时部分、127 个运行时函数';assert old in t
t=t.replace(old,'及 emit-functions 的一个函数（含必要 proof 支持）及 emit-prelude 的一个函数，共二十八个具体实现迁移单元的运行时部分、128 个运行时函数')
t=t.replace('224、106、20 条可信自动 witness',f'224、106、20、{e["automatic_witnesses"]} 条可信自动 witness')
t=t.replace('[emit-functions 报告](experiments/cmc_emit_functions/REPORT.md)。','[emit-functions 报告](experiments/cmc_emit_functions/REPORT.md)、[emit-prelude 报告](experiments/cmc_emit_prelude/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 | `cmc_concrete_emit_prelude.c`、',f'| 已完成 | `cmc_concrete_emit_prelude.c` | 一个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
t=t.replace('emit-function 与 emit-functions 的运行时部分已完成','emit-function、emit-functions 与 emit-prelude 的运行时部分已完成')
t=t.replace('已迁移的一般表达式代码模型及代码长度／count 定理在本轮直接复用','本轮 prelude 直接复用计划发射、程序上下文及总 PC 查询公共库')
t=t.replace('下一候选为 `cmc_concrete_emit_prelude.c`','下一候选为 `cmc_concrete_emit_code.c`');p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_prelude.c,'):
  assert b',not_migrated,' in row
  rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_1_function_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows))
print('Published verified prelude reference, skill routing, plan and one inventory row.')
