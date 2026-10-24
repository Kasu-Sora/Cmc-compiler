"""Update skill and migration inventory only after final audited success."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/semantic-audit.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/validated-lessons.md').read_text();assert lessons.strip()
date=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d')
p=S/'references/cmc-patch-calls-case.md';assert not p.exists()
p.write_text(f'''# 已验证案例：patch-calls，C* → QCP

{date} 完成 `cmc_concrete_patch_calls.c` 两个运行时函数，含 static 递归数组函数与公开 resolved wrapper 及必要 proof 支持。C* 重放与 QCP 完整终检通过。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_patch_calls/REPORT.md`。

## 契约与复用

保留原 wf/code-ready、长度界、程序上下文和函数链表；对双数组逐项回填 CALL immediate，非 CALL 保持不变。任意 signed64 target 用既有总 PC 查询，没有新增有效函数编号前提，空数组域保持。公开 wrapper 从存在 raw 的 resolved 视图得到实际 resolved 缓冲区，保留容量和未用尾部，没有假设 patch 幂等。

复用 patch 模型、长度支持、emitter 和数组库及 function-pc-total BODY 契约。新增公共定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行。运行体和 ABI 不变，沿用 policy/cg 边界；不新增编译保持性或 TVM 执行/终止性定理。

## 经验证的经验

{lessons.strip()}

## 成本与信任

完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split，另有 {e['automatic_witnesses']} 条自动 witness 以 Admitted 导出；manual 和新增库没有 Admitted/Axiom/Parameter。非空非纯注释行：

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| 外部 helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {c['new_public_definitions']} | {q['new_common_definitions']} |
| 新增公共 proof | {c['exported_shared_proof_closure']+c['additional_public_proof_closure']} | {q['new_common_proof']} |

源案例 proof 包含 150 行文件内私有支持，公开尾列表观察定义单列；旧公共依赖不重复计费。报告提供 token、字符、逐函数区间和失败记录，不能从排版行数推断工时。
''')
p=S/'SKILL.md';t=p.read_text();old='及 emit-prelude、emit-code 各一个函数；';assert old in t
t=t.replace(old,'及 emit-prelude、emit-code 各一个函数及 patch-calls 的两个函数；').replace('emit-code 为 `cmc_emit_code_migration.c`。','emit-code 为 `cmc_emit_code_migration.c`，patch-calls 为 `cmc_patch_calls_migration.c`。')
old='这些结果覆盖二十九个具体实现迁移单元的运行时部分、129 个运行时函数';assert old in t
entry=f'`cmc_concrete_patch_calls.c` 于 {date} 完成两个运行时函数及必要 proof 支持验证。涉及双数组递归、CALL immediate 总查询、数组头尾拆并及 resolved 逻辑视图实体化时，读取 [references/cmc-patch-calls-case.md](references/cmc-patch-calls-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace(old,entry+'这些结果覆盖三十个具体实现迁移单元的运行时部分、131 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();old='及 emit-prelude、emit-code 各一个函数，共二十九个具体实现迁移单元的运行时部分、129 个运行时函数';assert old in t
t=t.replace(old,'及 emit-prelude、emit-code 各一个函数及 patch-calls 的两个函数，共三十个具体实现迁移单元的运行时部分、131 个运行时函数')
t=t.replace('224、106、20、41、5 条可信自动 witness',f'224、106、20、41、5、{e["automatic_witnesses"]} 条可信自动 witness').replace('[emit-code 报告](experiments/cmc_emit_code/REPORT.md)。','[emit-code 报告](experiments/cmc_emit_code/REPORT.md)、[patch-calls 报告](experiments/cmc_patch_calls/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_patch_calls.c` | 指令列表与实际缓冲区一致；表达式/语句/调用的递归验证；跳转地址和回填 |';assert old in t
t=t.replace(old,f'| 已完成 | `cmc_concrete_patch_calls.c` | 两个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |')
t=t.replace('emit-prelude 与 emit-code 的运行时部分已完成','emit-prelude、emit-code 与 patch-calls 的运行时部分已完成')
t=t.replace('下一候选为 `cmc_concrete_patch_calls.c`；开始前仍须审查其完整依赖闭包。','下一步应审查 `cmc_compile` 及其 readiness／保持性依赖闭包，再确定下一验证单元。')
t=t.replace('本轮 emit-code 直接复用 prelude/functions、程序上下文及计划公共库，完整指令 emitter 的其余语义、readiness 桥及具体 TVM 实例化仍待后续迁移。','本轮 patch-calls 已连接 resolved 逻辑视图与实际回填缓冲区；完整 readiness 桥、顶层组合、保持性及具体 TVM 实例化仍待后续迁移。');p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_patch_calls.c,'):
  assert b',not_migrated,' in row;rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_2_functions_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows));print('Published verified patch-calls reference, skill routing, plan and one inventory row.')
