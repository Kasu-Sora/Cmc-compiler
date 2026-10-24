"""Publish verified case only after controller and independent audits pass."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/semantic-audit.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/validated-lessons.md').read_text();assert lessons.strip()
date=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d')
p=S/'references/cmc-emit-code-case.md';assert not p.exists()
p.write_text(f'''# 已验证案例：emit-code，C* → QCP

{date} 完成 `cmc_concrete_emit_code.c` 唯一运行时函数 `cmc_emit_code` 及必要 proof 支持。C* 隔离重放与 QCP 完整终检通过。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_code/REPORT.md`。

## 契约与复用

保留原 wf/typed、完整 functions readiness、三类表示安全与数据总大小界；保持程序上下文与整个函数链表。输出为 prelude 后接从 fid=0 发射的函数列表，精确追加到任意 done 并保留 tail。PC-zero 在内部推导，运行时和 ABI 不变。

复用 prelude/functions 已验证 BODY 契约及公共模型闭包。新增定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行。已有 policy/cg 参数化边界保持；本例不增加 patch/link、编译保持性或 TVM 执行/终止性定理。

## 经验证的经验

{lessons.strip()}

## 成本与信任

完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split，另有 {e['automatic_witnesses']} 条自动 witness 以 Admitted 导出。manual 与新增库没有 Admitted/Axiom/Parameter。非空非纯注释行：

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {c['new_public_definitions']} | {q['new_common_definitions']} |
| 新增公共 proof | {c['exported_shared_proof_closure']+c['additional_public_proof_closure']} | {q['new_common_proof']} |

源公共 proof 单列 PC-zero 的 11 行支持，旧 prefix-zero 和其他依赖不重复计费。报告含 token、字符、调用失败与精确区间；行数不是历史工时或独立从零证明效率。
''')
p=S/'SKILL.md';t=p.read_text();old='及 emit-prelude 的一个函数；';assert old in t
t=t.replace(old,'及 emit-prelude、emit-code 各一个函数；').replace('emit-prelude 为 `cmc_emit_prelude_migration.c`。','emit-prelude 为 `cmc_emit_prelude_migration.c`，emit-code 为 `cmc_emit_code_migration.c`。')
old='这些结果覆盖二十八个具体实现迁移单元的运行时部分、128 个运行时函数';assert old in t
entry=f'`cmc_concrete_emit_code.c` 于 {date} 完成唯一运行时函数及必要 proof 支持验证。涉及 prelude/functions 组合、PC-zero 桥、完整资源及纯事实保持时，读取 [references/cmc-emit-code-case.md](references/cmc-emit-code-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace(old,entry+'这些结果覆盖二十九个具体实现迁移单元的运行时部分、129 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();old='及 emit-prelude 的一个函数，共二十八个具体实现迁移单元的运行时部分、128 个运行时函数';assert old in t
t=t.replace(old,'及 emit-prelude、emit-code 各一个函数，共二十九个具体实现迁移单元的运行时部分、129 个运行时函数')
t=t.replace('224、106、20、41 条可信自动 witness',f'224、106、20、41、{e["automatic_witnesses"]} 条可信自动 witness').replace('[emit-prelude 报告](experiments/cmc_emit_prelude/REPORT.md)。','[emit-prelude 报告](experiments/cmc_emit_prelude/REPORT.md)、[emit-code 报告](experiments/cmc_emit_code/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 | `cmc_concrete_emit_code.c`、',f'| 已完成 | `cmc_concrete_emit_code.c` | 一个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
t=t.replace('emit-functions 与 emit-prelude 的运行时部分已完成','emit-functions、emit-prelude 与 emit-code 的运行时部分已完成').replace('下一候选为 `cmc_concrete_emit_code.c`','下一候选为 `cmc_concrete_patch_calls.c`').replace('本轮 prelude 直接复用计划发射、程序上下文及总 PC 查询公共库','本轮 emit-code 直接复用 prelude/functions、程序上下文及计划公共库');p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_code.c,'):
  assert b',not_migrated,' in row;rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_1_function_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows));print('Published verified code reference, skill routing, plan and one inventory row.')
