"""Publish the function migration only after complete formal and semantic checks."""
import datetime,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent;W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());q=x['counts']['qcp'];c=x['counts']['cstar'];e=x['entries']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
assert json.loads((R/'metrics/semantic-audit.json').read_text())['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):
 assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lessons=(R/'metrics/validated-lessons.md').read_text();assert lessons.strip()
date=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).strftime('%Y-%m-%d')
p=S/'references/cmc-emit-function-case.md';assert not p.exists()
p.write_text(f'''# 已验证案例：emit-function，C* → QCP

{date} 完成 `cmc_concrete_emit_function.c` 全部三个运行时函数及必要 function proof 支持：`cmc_emit_param_stores_from`、`cmc_emit_prologue`、`cmc_emit_function`。C* 隔离重放和 QCP 完整终检均通过。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_function/REPORT.md`。

## 契约与依赖

保留任意参数前缀/full 列表关系、slot 和 offset 等式、整数与大小界、原 wf/typed/count/表示安全条件及全部上下文资源。参数发射先处理尾部，当前参数地址仍由原前缀确定；序言精确生成 14 条指令及参数写入；完整函数由序言、原 body PC 上的 stmt、PUSH 0 和返回尾声组成。全部契约保留任意 done/tail。运行体和 ABI 不变，没有额外输入限制。

复用十个既有 helper BODY 契约及已验证公共库；新增定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行、引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行。沿用已有 policy/cg 参数化边界；本例不增加 TVM 执行、终止性、链接或编译保持性定理。

## 经验证的经验

{lessons.strip()}

## 成本与信任

完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split；另有 {e['automatic_witnesses']} 条自动 witness 以 Admitted 导出。manual 与新增库没有 Admitted/Axiom/Parameter。非空非纯注释行：

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {c['new_public_definitions']} | {q['new_common_definitions']} |
| 新增公共 proof | {c['exported_shared_proof_closure']+c['additional_public_proof_closure']} | {q['new_common_proof']} |

源文件另有 {c['case_model_definitions']} 行私有模型辅助定义；非 static theorem 常量及其证明构造器按公共支持计一次，即使运行时头文件未重复声明。其余 static 证明支持计案例 proof。行数含证明声明与包装，不代表工时；token、字符、逐函数计量、失败修复和依赖哈希见报告。
''')
p=S/'SKILL.md';t=p.read_text()
old='及 emit-stmt 的两个函数（含必要 stmt proof 支持）；'
assert old in t;t=t.replace(old,'及 emit-stmt 的两个函数（含必要 stmt proof 支持）及 emit-function 的三个函数（含必要 function proof 支持）；')
t=t.replace('emit-stmt 为 `cmc_emit_stmt_migration.c`。','emit-stmt 为 `cmc_emit_stmt_migration.c`，emit-function 为 `cmc_emit_function_migration.c`。')
old='这些结果覆盖二十五个具体实现迁移单元的运行时部分、123 个运行时函数';assert old in t
entry=f'`cmc_concrete_emit_function.c` 于 {date} 完成三个运行时函数及必要 function proof 支持验证。涉及参数反向发射、prefix/offset 关系、序言栈帧与完整函数组合时，读取 [references/cmc-emit-function-case.md](references/cmc-emit-function-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace(old,entry+'这些结果覆盖二十六个具体实现迁移单元的运行时部分、126 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text()
t=t.replace('及 emit-stmt 的两个函数（含必要 stmt proof 支持），共二十五个具体实现迁移单元的运行时部分、123 个运行时函数','及 emit-stmt 的两个函数（含必要 stmt proof 支持）及 emit-function 的三个函数（含必要 function proof 支持），共二十六个具体实现迁移单元的运行时部分、126 个运行时函数')
t=t.replace('449、24、224 条可信自动 witness',f'449、24、224、{e["automatic_witnesses"]} 条可信自动 witness')
t=t.replace('[emit-stmt 报告](experiments/cmc_emit_stmt/REPORT.md)。','[emit-stmt 报告](experiments/cmc_emit_stmt/REPORT.md)、[emit-function 报告](experiments/cmc_emit_function/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 |',f'| 已完成 | `cmc_concrete_emit_function.c` 及其必要 proof 支持 | 三个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 |')
t=t.replace('`cmc_concrete_emit_function*.c`','`cmc_concrete_emit_functions.c`')
t=t.replace('emit-expr、emit-return 与 emit-stmt 的运行时部分已完成','emit-expr、emit-return、emit-stmt 与 emit-function 的运行时部分已完成')
t=t.replace('下一候选为 `cmc_concrete_emit_function.c`','下一候选为 `cmc_concrete_emit_functions.c`')
p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_function.c,'):
  assert b',not_migrated,' in row
  rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_3_functions_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows))
print('Published verified function reference, skill routing, plan and one inventory row.')
